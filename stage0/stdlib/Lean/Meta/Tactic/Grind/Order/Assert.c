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
size_t v_x_9945__boxed_1114_; lean_object* v_res_1115_; 
v_x_9945__boxed_1114_ = lean_unbox_usize(v_x_1112_);
lean_dec(v_x_1112_);
v_res_1115_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg(v_x_1111_, v_x_9945__boxed_1114_, v_x_1113_);
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
size_t v_x_10209__boxed_1264_; lean_object* v_res_1265_; 
v_x_10209__boxed_1264_ = lean_unbox_usize(v_x_1262_);
lean_dec(v_x_1262_);
v_res_1265_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0(v_00_u03b2_1260_, v_x_1261_, v_x_10209__boxed_1264_, v_x_1263_);
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
lean_object* v___x_1294_; lean_object* v___f_1295_; lean_object* v___x_6378__overap_1296_; lean_object* v___x_1297_; 
v___x_1294_ = lean_obj_once(&l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0___closed__0, &l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0___closed__0_once, _init_l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0___closed__0);
v___f_1295_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1295_, 0, v___x_1294_);
v___x_6378__overap_1296_ = lean_panic_fn_borrowed(v___f_1295_, v_msg_1281_);
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
v___x_1297_ = lean_apply_12(v___x_6378__overap_1296_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, lean_box(0));
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
lean_object* v_a_1758_; lean_object* v___y_1760_; lean_object* v___y_1761_; lean_object* v___y_1762_; lean_object* v___y_1763_; lean_object* v___y_1764_; lean_object* v___y_1765_; lean_object* v___y_1766_; lean_object* v___y_1767_; lean_object* v___y_1768_; lean_object* v___y_1769_; lean_object* v___y_1770_; lean_object* v___y_1771_; lean_object* v___y_1772_; lean_object* v___y_1773_; lean_object* v___y_1774_; lean_object* v___y_1775_; lean_object* v___y_1848_; lean_object* v___y_1849_; lean_object* v___y_1850_; lean_object* v___y_1851_; lean_object* v___y_1852_; lean_object* v___y_1853_; lean_object* v___y_1854_; lean_object* v___y_1855_; lean_object* v___y_1856_; lean_object* v___y_1857_; lean_object* v___y_1858_; lean_object* v___y_1892_; lean_object* v___x_1946_; 
v_a_1758_ = lean_ctor_get(v___x_1757_, 0);
lean_inc(v_a_1758_);
lean_dec_ref(v___x_1757_);
v___x_1946_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_a_1756_, v___y_1722_);
if (lean_obj_tag(v___x_1946_) == 0)
{
lean_object* v_a_1947_; uint8_t v___x_1948_; 
v_a_1947_ = lean_ctor_get(v___x_1946_, 0);
lean_inc(v_a_1947_);
v___x_1948_ = lean_unbox(v_a_1947_);
lean_dec(v_a_1947_);
if (v___x_1948_ == 0)
{
v___y_1892_ = v___x_1946_;
goto v___jp_1891_;
}
else
{
lean_object* v___x_1949_; 
lean_dec_ref(v___x_1946_);
v___x_1949_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_a_1758_, v___y_1722_);
v___y_1892_ = v___x_1949_;
goto v___jp_1891_;
}
}
else
{
v___y_1892_ = v___x_1946_;
goto v___jp_1891_;
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
lean_dec_ref(v___y_1771_);
lean_dec_ref(v___y_1770_);
lean_dec_ref(v___y_1769_);
lean_dec_ref(v___y_1767_);
lean_dec(v_a_1758_);
lean_dec(v_a_1756_);
v_as_x27_1719_ = v_tail_1735_;
v_b_1720_ = v___x_1736_;
goto _start;
}
else
{
lean_object* v___x_1779_; 
v___x_1779_ = l_Lean_Meta_Grind_isEqv___redArg(v___y_1771_, v___y_1767_, v___y_1761_);
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
v___x_1782_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath(v_u_1753_, v_v_1754_, v___y_1772_, v___y_1761_, v___y_1766_, v___y_1762_, v___y_1773_, v___y_1774_, v___y_1768_, v___y_1764_, v___y_1763_, v___y_1765_, v___y_1760_);
if (lean_obj_tag(v___x_1782_) == 0)
{
lean_object* v_a_1783_; lean_object* v___x_1784_; 
v_a_1783_ = lean_ctor_get(v___x_1782_, 0);
lean_inc(v_a_1783_);
lean_dec_ref(v___x_1782_);
v___x_1784_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath(v_v_1754_, v_u_1753_, v___y_1772_, v___y_1761_, v___y_1766_, v___y_1762_, v___y_1773_, v___y_1774_, v___y_1768_, v___y_1764_, v___y_1763_, v___y_1765_, v___y_1760_);
if (lean_obj_tag(v___x_1784_) == 0)
{
lean_object* v_a_1785_; lean_object* v___x_1786_; 
v_a_1785_ = lean_ctor_get(v___x_1784_, 0);
lean_inc(v_a_1785_);
lean_dec_ref(v___x_1784_);
lean_inc(v_a_1758_);
lean_inc(v_a_1756_);
v___x_1786_ = l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLe(v_a_1756_, v_a_1758_, v_a_1783_, v_a_1785_, v___y_1772_, v___y_1761_, v___y_1766_, v___y_1762_, v___y_1773_, v___y_1774_, v___y_1768_, v___y_1764_, v___y_1763_, v___y_1765_, v___y_1760_);
if (lean_obj_tag(v___x_1786_) == 0)
{
lean_object* v_a_1787_; lean_object* v___x_1788_; 
v_a_1787_ = lean_ctor_get(v___x_1786_, 0);
lean_inc(v_a_1787_);
lean_dec_ref(v___x_1786_);
lean_inc(v___y_1760_);
lean_inc_ref(v___y_1765_);
lean_inc(v___y_1763_);
lean_inc_ref(v___y_1764_);
lean_inc(v_a_1756_);
v___x_1788_ = lean_infer_type(v_a_1756_, v___y_1764_, v___y_1763_, v___y_1765_, v___y_1760_);
if (lean_obj_tag(v___x_1788_) == 0)
{
lean_object* v_a_1789_; lean_object* v___x_1790_; uint8_t v___x_1791_; 
v_a_1789_ = lean_ctor_get(v___x_1788_, 0);
lean_inc(v_a_1789_);
lean_dec_ref(v___x_1788_);
v___x_1790_ = l_Lean_Int_mkType;
v___x_1791_ = lean_expr_eqv(v_a_1789_, v___x_1790_);
lean_dec(v_a_1789_);
if (v___x_1791_ == 0)
{
lean_dec(v_a_1787_);
lean_dec(v_a_1780_);
lean_dec_ref(v___y_1771_);
lean_dec_ref(v___y_1770_);
lean_dec_ref(v___y_1769_);
lean_dec_ref(v___y_1767_);
lean_dec(v_a_1758_);
lean_dec(v_a_1756_);
v_as_x27_1719_ = v_tail_1735_;
v_b_1720_ = v___x_1736_;
goto _start;
}
else
{
lean_object* v___x_1793_; lean_object* v___x_1794_; uint8_t v___x_1795_; lean_object* v___x_1796_; 
v___x_1793_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg___closed__2, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg___closed__2);
lean_inc_ref(v___y_1767_);
lean_inc_ref(v___y_1771_);
v___x_1794_ = l_Lean_mkApp7(v___x_1793_, v___y_1771_, v___y_1767_, v_a_1756_, v_a_1758_, v___y_1770_, v___y_1769_, v_a_1787_);
v___x_1795_ = lean_unbox(v_a_1780_);
lean_dec(v_a_1780_);
v___x_1796_ = l_Lean_Meta_Grind_pushEqCore___redArg(v___y_1771_, v___y_1767_, v___x_1794_, v___x_1795_, v___y_1761_, v___y_1762_, v___y_1764_, v___y_1763_, v___y_1765_, v___y_1760_);
if (lean_obj_tag(v___x_1796_) == 0)
{
lean_dec_ref(v___x_1796_);
v_as_x27_1719_ = v_tail_1735_;
v_b_1720_ = v___x_1736_;
goto _start;
}
else
{
return v___x_1796_;
}
}
}
else
{
lean_object* v_a_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1805_; 
lean_dec(v_a_1787_);
lean_dec(v_a_1780_);
lean_dec_ref(v___y_1771_);
lean_dec_ref(v___y_1770_);
lean_dec_ref(v___y_1769_);
lean_dec_ref(v___y_1767_);
lean_dec(v_a_1758_);
lean_dec(v_a_1756_);
v_a_1798_ = lean_ctor_get(v___x_1788_, 0);
v_isSharedCheck_1805_ = !lean_is_exclusive(v___x_1788_);
if (v_isSharedCheck_1805_ == 0)
{
v___x_1800_ = v___x_1788_;
v_isShared_1801_ = v_isSharedCheck_1805_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_a_1798_);
lean_dec(v___x_1788_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1805_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v___x_1803_; 
if (v_isShared_1801_ == 0)
{
v___x_1803_ = v___x_1800_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v_a_1798_);
v___x_1803_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
return v___x_1803_;
}
}
}
}
else
{
lean_object* v_a_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1813_; 
lean_dec(v_a_1780_);
lean_dec_ref(v___y_1771_);
lean_dec_ref(v___y_1770_);
lean_dec_ref(v___y_1769_);
lean_dec_ref(v___y_1767_);
lean_dec(v_a_1758_);
lean_dec(v_a_1756_);
v_a_1806_ = lean_ctor_get(v___x_1786_, 0);
v_isSharedCheck_1813_ = !lean_is_exclusive(v___x_1786_);
if (v_isSharedCheck_1813_ == 0)
{
v___x_1808_ = v___x_1786_;
v_isShared_1809_ = v_isSharedCheck_1813_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_a_1806_);
lean_dec(v___x_1786_);
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
lean_dec(v_a_1783_);
lean_dec(v_a_1780_);
lean_dec_ref(v___y_1771_);
lean_dec_ref(v___y_1770_);
lean_dec_ref(v___y_1769_);
lean_dec_ref(v___y_1767_);
lean_dec(v_a_1758_);
lean_dec(v_a_1756_);
v_a_1814_ = lean_ctor_get(v___x_1784_, 0);
v_isSharedCheck_1821_ = !lean_is_exclusive(v___x_1784_);
if (v_isSharedCheck_1821_ == 0)
{
v___x_1816_ = v___x_1784_;
v_isShared_1817_ = v_isSharedCheck_1821_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_a_1814_);
lean_dec(v___x_1784_);
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
lean_dec(v_a_1780_);
lean_dec_ref(v___y_1771_);
lean_dec_ref(v___y_1770_);
lean_dec_ref(v___y_1769_);
lean_dec_ref(v___y_1767_);
lean_dec(v_a_1758_);
lean_dec(v_a_1756_);
v_a_1822_ = lean_ctor_get(v___x_1782_, 0);
v_isSharedCheck_1829_ = !lean_is_exclusive(v___x_1782_);
if (v_isSharedCheck_1829_ == 0)
{
v___x_1824_ = v___x_1782_;
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_a_1822_);
lean_dec(v___x_1782_);
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
lean_dec(v_a_1780_);
lean_dec_ref(v___y_1771_);
lean_dec_ref(v___y_1770_);
lean_dec_ref(v___y_1769_);
lean_dec_ref(v___y_1767_);
lean_dec(v_a_1758_);
lean_dec(v_a_1756_);
v_as_x27_1719_ = v_tail_1735_;
v_b_1720_ = v___x_1736_;
goto _start;
}
}
else
{
lean_object* v_a_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1838_; 
lean_dec_ref(v___y_1771_);
lean_dec_ref(v___y_1770_);
lean_dec_ref(v___y_1769_);
lean_dec_ref(v___y_1767_);
lean_dec(v_a_1758_);
lean_dec(v_a_1756_);
v_a_1831_ = lean_ctor_get(v___x_1779_, 0);
v_isSharedCheck_1838_ = !lean_is_exclusive(v___x_1779_);
if (v_isSharedCheck_1838_ == 0)
{
v___x_1833_ = v___x_1779_;
v_isShared_1834_ = v_isSharedCheck_1838_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_a_1831_);
lean_dec(v___x_1779_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1838_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v___x_1836_; 
if (v_isShared_1834_ == 0)
{
v___x_1836_ = v___x_1833_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v_a_1831_);
v___x_1836_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1835_;
}
v_reusejp_1835_:
{
return v___x_1836_;
}
}
}
}
}
else
{
lean_object* v_a_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1846_; 
lean_dec_ref(v___y_1771_);
lean_dec_ref(v___y_1770_);
lean_dec_ref(v___y_1769_);
lean_dec_ref(v___y_1767_);
lean_dec(v_a_1758_);
lean_dec(v_a_1756_);
v_a_1839_ = lean_ctor_get(v___y_1775_, 0);
v_isSharedCheck_1846_ = !lean_is_exclusive(v___y_1775_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1841_ = v___y_1775_;
v_isShared_1842_ = v_isSharedCheck_1846_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_a_1839_);
lean_dec(v___y_1775_);
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
v___jp_1847_:
{
lean_object* v___x_1859_; 
v___x_1859_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f___redArg(v_a_1756_, v___y_1849_, v___y_1857_);
if (lean_obj_tag(v___x_1859_) == 0)
{
lean_object* v_a_1860_; 
v_a_1860_ = lean_ctor_get(v___x_1859_, 0);
lean_inc(v_a_1860_);
lean_dec_ref(v___x_1859_);
if (lean_obj_tag(v_a_1860_) == 1)
{
lean_object* v_val_1861_; lean_object* v_fst_1862_; lean_object* v_snd_1863_; lean_object* v___x_1864_; 
v_val_1861_ = lean_ctor_get(v_a_1860_, 0);
lean_inc(v_val_1861_);
lean_dec_ref(v_a_1860_);
v_fst_1862_ = lean_ctor_get(v_val_1861_, 0);
lean_inc(v_fst_1862_);
v_snd_1863_ = lean_ctor_get(v_val_1861_, 1);
lean_inc(v_snd_1863_);
lean_dec(v_val_1861_);
v___x_1864_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f___redArg(v_a_1758_, v___y_1849_, v___y_1857_);
if (lean_obj_tag(v___x_1864_) == 0)
{
lean_object* v_a_1865_; 
v_a_1865_ = lean_ctor_get(v___x_1864_, 0);
lean_inc(v_a_1865_);
lean_dec_ref(v___x_1864_);
if (lean_obj_tag(v_a_1865_) == 1)
{
lean_object* v_val_1866_; lean_object* v_fst_1867_; lean_object* v_snd_1868_; lean_object* v___x_1869_; 
v_val_1866_ = lean_ctor_get(v_a_1865_, 0);
lean_inc(v_val_1866_);
lean_dec_ref(v_a_1865_);
v_fst_1867_ = lean_ctor_get(v_val_1866_, 0);
lean_inc(v_fst_1867_);
v_snd_1868_ = lean_ctor_get(v_val_1866_, 1);
lean_inc(v_snd_1868_);
lean_dec(v_val_1866_);
v___x_1869_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_fst_1862_, v___y_1849_);
if (lean_obj_tag(v___x_1869_) == 0)
{
lean_object* v_a_1870_; uint8_t v___x_1871_; 
v_a_1870_ = lean_ctor_get(v___x_1869_, 0);
lean_inc(v_a_1870_);
v___x_1871_ = lean_unbox(v_a_1870_);
lean_dec(v_a_1870_);
if (v___x_1871_ == 0)
{
v___y_1760_ = v___y_1858_;
v___y_1761_ = v___y_1849_;
v___y_1762_ = v___y_1851_;
v___y_1763_ = v___y_1856_;
v___y_1764_ = v___y_1855_;
v___y_1765_ = v___y_1857_;
v___y_1766_ = v___y_1850_;
v___y_1767_ = v_fst_1867_;
v___y_1768_ = v___y_1854_;
v___y_1769_ = v_snd_1868_;
v___y_1770_ = v_snd_1863_;
v___y_1771_ = v_fst_1862_;
v___y_1772_ = v___y_1848_;
v___y_1773_ = v___y_1852_;
v___y_1774_ = v___y_1853_;
v___y_1775_ = v___x_1869_;
goto v___jp_1759_;
}
else
{
lean_object* v___x_1872_; 
lean_dec_ref(v___x_1869_);
v___x_1872_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_fst_1867_, v___y_1849_);
v___y_1760_ = v___y_1858_;
v___y_1761_ = v___y_1849_;
v___y_1762_ = v___y_1851_;
v___y_1763_ = v___y_1856_;
v___y_1764_ = v___y_1855_;
v___y_1765_ = v___y_1857_;
v___y_1766_ = v___y_1850_;
v___y_1767_ = v_fst_1867_;
v___y_1768_ = v___y_1854_;
v___y_1769_ = v_snd_1868_;
v___y_1770_ = v_snd_1863_;
v___y_1771_ = v_fst_1862_;
v___y_1772_ = v___y_1848_;
v___y_1773_ = v___y_1852_;
v___y_1774_ = v___y_1853_;
v___y_1775_ = v___x_1872_;
goto v___jp_1759_;
}
}
else
{
v___y_1760_ = v___y_1858_;
v___y_1761_ = v___y_1849_;
v___y_1762_ = v___y_1851_;
v___y_1763_ = v___y_1856_;
v___y_1764_ = v___y_1855_;
v___y_1765_ = v___y_1857_;
v___y_1766_ = v___y_1850_;
v___y_1767_ = v_fst_1867_;
v___y_1768_ = v___y_1854_;
v___y_1769_ = v_snd_1868_;
v___y_1770_ = v_snd_1863_;
v___y_1771_ = v_fst_1862_;
v___y_1772_ = v___y_1848_;
v___y_1773_ = v___y_1852_;
v___y_1774_ = v___y_1853_;
v___y_1775_ = v___x_1869_;
goto v___jp_1759_;
}
}
else
{
lean_dec(v_a_1865_);
lean_dec(v_snd_1863_);
lean_dec(v_fst_1862_);
lean_dec(v_a_1758_);
lean_dec(v_a_1756_);
v_as_x27_1719_ = v_tail_1735_;
v_b_1720_ = v___x_1736_;
goto _start;
}
}
else
{
lean_object* v_a_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1881_; 
lean_dec(v_snd_1863_);
lean_dec(v_fst_1862_);
lean_dec(v_a_1758_);
lean_dec(v_a_1756_);
v_a_1874_ = lean_ctor_get(v___x_1864_, 0);
v_isSharedCheck_1881_ = !lean_is_exclusive(v___x_1864_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1876_ = v___x_1864_;
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_a_1874_);
lean_dec(v___x_1864_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1879_; 
if (v_isShared_1877_ == 0)
{
v___x_1879_ = v___x_1876_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_a_1874_);
v___x_1879_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
return v___x_1879_;
}
}
}
}
else
{
lean_dec(v_a_1860_);
lean_dec(v_a_1758_);
lean_dec(v_a_1756_);
v_as_x27_1719_ = v_tail_1735_;
v_b_1720_ = v___x_1736_;
goto _start;
}
}
else
{
lean_object* v_a_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1890_; 
lean_dec(v_a_1758_);
lean_dec(v_a_1756_);
v_a_1883_ = lean_ctor_get(v___x_1859_, 0);
v_isSharedCheck_1890_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1885_ = v___x_1859_;
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_a_1883_);
lean_dec(v___x_1859_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1888_; 
if (v_isShared_1886_ == 0)
{
v___x_1888_ = v___x_1885_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v_a_1883_);
v___x_1888_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
return v___x_1888_;
}
}
}
}
v___jp_1891_:
{
if (lean_obj_tag(v___y_1892_) == 0)
{
lean_object* v_a_1893_; uint8_t v___x_1894_; 
v_a_1893_ = lean_ctor_get(v___y_1892_, 0);
lean_inc(v_a_1893_);
lean_dec_ref(v___y_1892_);
v___x_1894_ = lean_unbox(v_a_1893_);
lean_dec(v_a_1893_);
if (v___x_1894_ == 0)
{
v___y_1848_ = v___y_1721_;
v___y_1849_ = v___y_1722_;
v___y_1850_ = v___y_1723_;
v___y_1851_ = v___y_1724_;
v___y_1852_ = v___y_1725_;
v___y_1853_ = v___y_1726_;
v___y_1854_ = v___y_1727_;
v___y_1855_ = v___y_1728_;
v___y_1856_ = v___y_1729_;
v___y_1857_ = v___y_1730_;
v___y_1858_ = v___y_1731_;
goto v___jp_1847_;
}
else
{
lean_object* v___x_1895_; 
v___x_1895_ = l_Lean_Meta_Grind_isEqv___redArg(v_a_1756_, v_a_1758_, v___y_1722_);
if (lean_obj_tag(v___x_1895_) == 0)
{
lean_object* v_a_1896_; uint8_t v___x_1897_; 
v_a_1896_ = lean_ctor_get(v___x_1895_, 0);
lean_inc(v_a_1896_);
lean_dec_ref(v___x_1895_);
v___x_1897_ = lean_unbox(v_a_1896_);
if (v___x_1897_ == 0)
{
lean_object* v___x_1898_; 
v___x_1898_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath(v_u_1753_, v_v_1754_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_);
if (lean_obj_tag(v___x_1898_) == 0)
{
lean_object* v_a_1899_; lean_object* v___x_1900_; 
v_a_1899_ = lean_ctor_get(v___x_1898_, 0);
lean_inc(v_a_1899_);
lean_dec_ref(v___x_1898_);
v___x_1900_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath(v_v_1754_, v_u_1753_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_);
if (lean_obj_tag(v___x_1900_) == 0)
{
lean_object* v_a_1901_; lean_object* v___x_1902_; 
v_a_1901_ = lean_ctor_get(v___x_1900_, 0);
lean_inc(v_a_1901_);
lean_dec_ref(v___x_1900_);
lean_inc(v_a_1758_);
lean_inc(v_a_1756_);
v___x_1902_ = l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLe(v_a_1756_, v_a_1758_, v_a_1899_, v_a_1901_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_);
if (lean_obj_tag(v___x_1902_) == 0)
{
lean_object* v_a_1903_; uint8_t v___x_1904_; lean_object* v___x_1905_; 
v_a_1903_ = lean_ctor_get(v___x_1902_, 0);
lean_inc(v_a_1903_);
lean_dec_ref(v___x_1902_);
v___x_1904_ = lean_unbox(v_a_1896_);
lean_dec(v_a_1896_);
lean_inc(v_a_1758_);
lean_inc(v_a_1756_);
v___x_1905_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_a_1756_, v_a_1758_, v_a_1903_, v___x_1904_, v___y_1722_, v___y_1724_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_);
if (lean_obj_tag(v___x_1905_) == 0)
{
lean_dec_ref(v___x_1905_);
v___y_1848_ = v___y_1721_;
v___y_1849_ = v___y_1722_;
v___y_1850_ = v___y_1723_;
v___y_1851_ = v___y_1724_;
v___y_1852_ = v___y_1725_;
v___y_1853_ = v___y_1726_;
v___y_1854_ = v___y_1727_;
v___y_1855_ = v___y_1728_;
v___y_1856_ = v___y_1729_;
v___y_1857_ = v___y_1730_;
v___y_1858_ = v___y_1731_;
goto v___jp_1847_;
}
else
{
lean_dec(v_a_1758_);
lean_dec(v_a_1756_);
return v___x_1905_;
}
}
else
{
lean_object* v_a_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1913_; 
lean_dec(v_a_1896_);
lean_dec(v_a_1758_);
lean_dec(v_a_1756_);
v_a_1906_ = lean_ctor_get(v___x_1902_, 0);
v_isSharedCheck_1913_ = !lean_is_exclusive(v___x_1902_);
if (v_isSharedCheck_1913_ == 0)
{
v___x_1908_ = v___x_1902_;
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_a_1906_);
lean_dec(v___x_1902_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
lean_object* v___x_1911_; 
if (v_isShared_1909_ == 0)
{
v___x_1911_ = v___x_1908_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v_a_1906_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
return v___x_1911_;
}
}
}
}
else
{
lean_object* v_a_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1921_; 
lean_dec(v_a_1899_);
lean_dec(v_a_1896_);
lean_dec(v_a_1758_);
lean_dec(v_a_1756_);
v_a_1914_ = lean_ctor_get(v___x_1900_, 0);
v_isSharedCheck_1921_ = !lean_is_exclusive(v___x_1900_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1916_ = v___x_1900_;
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_a_1914_);
lean_dec(v___x_1900_);
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
lean_dec(v_a_1896_);
lean_dec(v_a_1758_);
lean_dec(v_a_1756_);
v_a_1922_ = lean_ctor_get(v___x_1898_, 0);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1924_ = v___x_1898_;
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_a_1922_);
lean_dec(v___x_1898_);
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
lean_dec(v_a_1896_);
v___y_1848_ = v___y_1721_;
v___y_1849_ = v___y_1722_;
v___y_1850_ = v___y_1723_;
v___y_1851_ = v___y_1724_;
v___y_1852_ = v___y_1725_;
v___y_1853_ = v___y_1726_;
v___y_1854_ = v___y_1727_;
v___y_1855_ = v___y_1728_;
v___y_1856_ = v___y_1729_;
v___y_1857_ = v___y_1730_;
v___y_1858_ = v___y_1731_;
goto v___jp_1847_;
}
}
else
{
lean_object* v_a_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1937_; 
lean_dec(v_a_1758_);
lean_dec(v_a_1756_);
v_a_1930_ = lean_ctor_get(v___x_1895_, 0);
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1895_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1932_ = v___x_1895_;
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_a_1930_);
lean_dec(v___x_1895_);
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
}
else
{
lean_object* v_a_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1945_; 
lean_dec(v_a_1758_);
lean_dec(v_a_1756_);
v_a_1938_ = lean_ctor_get(v___y_1892_, 0);
v_isSharedCheck_1945_ = !lean_is_exclusive(v___y_1892_);
if (v_isSharedCheck_1945_ == 0)
{
v___x_1940_ = v___y_1892_;
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_a_1938_);
lean_dec(v___y_1892_);
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
lean_object* v_a_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1957_; 
lean_dec(v_a_1756_);
v_a_1950_ = lean_ctor_get(v___x_1757_, 0);
v_isSharedCheck_1957_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1957_ == 0)
{
v___x_1952_ = v___x_1757_;
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_a_1950_);
lean_dec(v___x_1757_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1957_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v___x_1955_; 
if (v_isShared_1953_ == 0)
{
v___x_1955_ = v___x_1952_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v_a_1950_);
v___x_1955_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
return v___x_1955_;
}
}
}
}
else
{
lean_object* v_a_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1965_; 
v_a_1958_ = lean_ctor_get(v___x_1755_, 0);
v_isSharedCheck_1965_ = !lean_is_exclusive(v___x_1755_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1960_ = v___x_1755_;
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_a_1958_);
lean_dec(v___x_1755_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg___boxed(lean_object* v_as_x27_1966_, lean_object* v_b_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_){
_start:
{
lean_object* v_res_1980_; 
v_res_1980_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg(v_as_x27_1966_, v_b_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_);
lean_dec(v___y_1978_);
lean_dec_ref(v___y_1977_);
lean_dec(v___y_1976_);
lean_dec_ref(v___y_1975_);
lean_dec(v___y_1974_);
lean_dec_ref(v___y_1973_);
lean_dec(v___y_1972_);
lean_dec_ref(v___y_1971_);
lean_dec(v___y_1970_);
lean_dec(v___y_1969_);
lean_dec(v___y_1968_);
lean_dec(v_as_x27_1966_);
return v_res_1980_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending(lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_){
_start:
{
lean_object* v___x_1994_; 
v___x_1994_ = l_Lean_Meta_Grind_Order_getStruct(v_a_1982_, v_a_1983_, v_a_1984_, v_a_1985_, v_a_1986_, v_a_1987_, v_a_1988_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_);
if (lean_obj_tag(v___x_1994_) == 0)
{
lean_object* v_a_1995_; lean_object* v___f_1996_; lean_object* v___x_1997_; 
v_a_1995_ = lean_ctor_get(v___x_1994_, 0);
lean_inc(v_a_1995_);
lean_dec_ref(v___x_1994_);
v___f_1996_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending___closed__0));
v___x_1997_ = l_Lean_Meta_Grind_Order_modifyStruct___redArg(v___f_1996_, v_a_1982_, v_a_1983_);
if (lean_obj_tag(v___x_1997_) == 0)
{
lean_object* v_propagate_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; 
lean_dec_ref(v___x_1997_);
v_propagate_1998_ = lean_ctor_get(v_a_1995_, 21);
lean_inc(v_propagate_1998_);
lean_dec(v_a_1995_);
v___x_1999_ = lean_box(0);
v___x_2000_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg(v_propagate_1998_, v___x_1999_, v_a_1982_, v_a_1983_, v_a_1984_, v_a_1985_, v_a_1986_, v_a_1987_, v_a_1988_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_);
lean_dec(v_propagate_1998_);
if (lean_obj_tag(v___x_2000_) == 0)
{
lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2007_; 
v_isSharedCheck_2007_ = !lean_is_exclusive(v___x_2000_);
if (v_isSharedCheck_2007_ == 0)
{
lean_object* v_unused_2008_; 
v_unused_2008_ = lean_ctor_get(v___x_2000_, 0);
lean_dec(v_unused_2008_);
v___x_2002_ = v___x_2000_;
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
else
{
lean_dec(v___x_2000_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v___x_2005_; 
if (v_isShared_2003_ == 0)
{
lean_ctor_set(v___x_2002_, 0, v___x_1999_);
v___x_2005_ = v___x_2002_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v___x_1999_);
v___x_2005_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
return v___x_2005_;
}
}
}
else
{
return v___x_2000_;
}
}
else
{
lean_dec(v_a_1995_);
return v___x_1997_;
}
}
else
{
lean_object* v_a_2009_; lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2016_; 
v_a_2009_ = lean_ctor_get(v___x_1994_, 0);
v_isSharedCheck_2016_ = !lean_is_exclusive(v___x_1994_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_2011_ = v___x_1994_;
v_isShared_2012_ = v_isSharedCheck_2016_;
goto v_resetjp_2010_;
}
else
{
lean_inc(v_a_2009_);
lean_dec(v___x_1994_);
v___x_2011_ = lean_box(0);
v_isShared_2012_ = v_isSharedCheck_2016_;
goto v_resetjp_2010_;
}
v_resetjp_2010_:
{
lean_object* v___x_2014_; 
if (v_isShared_2012_ == 0)
{
v___x_2014_ = v___x_2011_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v_a_2009_);
v___x_2014_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
return v___x_2014_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending___boxed(lean_object* v_a_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_, lean_object* v_a_2023_, lean_object* v_a_2024_, lean_object* v_a_2025_, lean_object* v_a_2026_, lean_object* v_a_2027_, lean_object* v_a_2028_){
_start:
{
lean_object* v_res_2029_; 
v_res_2029_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending(v_a_2017_, v_a_2018_, v_a_2019_, v_a_2020_, v_a_2021_, v_a_2022_, v_a_2023_, v_a_2024_, v_a_2025_, v_a_2026_, v_a_2027_);
lean_dec(v_a_2027_);
lean_dec_ref(v_a_2026_);
lean_dec(v_a_2025_);
lean_dec_ref(v_a_2024_);
lean_dec(v_a_2023_);
lean_dec_ref(v_a_2022_);
lean_dec(v_a_2021_);
lean_dec_ref(v_a_2020_);
lean_dec(v_a_2019_);
lean_dec(v_a_2018_);
lean_dec(v_a_2017_);
return v_res_2029_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0(lean_object* v_as_2030_, lean_object* v_as_x27_2031_, lean_object* v_b_2032_, lean_object* v_a_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_){
_start:
{
lean_object* v___x_2046_; 
v___x_2046_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg(v_as_x27_2031_, v_b_2032_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_);
return v___x_2046_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___boxed(lean_object* v_as_2047_, lean_object* v_as_x27_2048_, lean_object* v_b_2049_, lean_object* v_a_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_){
_start:
{
lean_object* v_res_2063_; 
v_res_2063_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0(v_as_2047_, v_as_x27_2048_, v_b_2049_, v_a_2050_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_);
lean_dec(v___y_2061_);
lean_dec_ref(v___y_2060_);
lean_dec(v___y_2059_);
lean_dec_ref(v___y_2058_);
lean_dec(v___y_2057_);
lean_dec_ref(v___y_2056_);
lean_dec(v___y_2055_);
lean_dec_ref(v___y_2054_);
lean_dec(v___y_2053_);
lean_dec(v___y_2052_);
lean_dec(v___y_2051_);
lean_dec(v_as_x27_2048_);
lean_dec(v_as_2047_);
return v_res_2063_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue___redArg(lean_object* v_e_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_){
_start:
{
lean_object* v___x_2072_; 
v___x_2072_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_2065_, v_a_2069_);
if (lean_obj_tag(v___x_2072_) == 0)
{
lean_object* v_a_2073_; lean_object* v_termMapInv_2074_; lean_object* v___x_2075_; 
v_a_2073_ = lean_ctor_get(v___x_2072_, 0);
lean_inc(v_a_2073_);
lean_dec_ref(v___x_2072_);
v_termMapInv_2074_ = lean_ctor_get(v_a_2073_, 4);
lean_inc_ref(v_termMapInv_2074_);
lean_dec(v_a_2073_);
v___x_2075_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMapInv_2074_, v_e_2064_);
lean_dec_ref(v_termMapInv_2074_);
if (lean_obj_tag(v___x_2075_) == 1)
{
lean_object* v_val_2076_; lean_object* v_fst_2077_; lean_object* v___x_2078_; 
lean_dec_ref(v_e_2064_);
v_val_2076_ = lean_ctor_get(v___x_2075_, 0);
lean_inc(v_val_2076_);
lean_dec_ref(v___x_2075_);
v_fst_2077_ = lean_ctor_get(v_val_2076_, 0);
lean_inc(v_fst_2077_);
lean_dec(v_val_2076_);
v___x_2078_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_fst_2077_, v_a_2065_);
if (lean_obj_tag(v___x_2078_) == 0)
{
lean_object* v_a_2079_; uint8_t v___x_2080_; 
v_a_2079_ = lean_ctor_get(v___x_2078_, 0);
lean_inc(v_a_2079_);
v___x_2080_ = lean_unbox(v_a_2079_);
lean_dec(v_a_2079_);
if (v___x_2080_ == 0)
{
lean_dec(v_fst_2077_);
return v___x_2078_;
}
else
{
lean_object* v___x_2081_; 
lean_dec_ref(v___x_2078_);
v___x_2081_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_fst_2077_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_);
return v___x_2081_;
}
}
else
{
lean_dec(v_fst_2077_);
return v___x_2078_;
}
}
else
{
lean_object* v___x_2082_; 
lean_dec(v___x_2075_);
v___x_2082_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_e_2064_, v_a_2065_);
if (lean_obj_tag(v___x_2082_) == 0)
{
lean_object* v_a_2083_; uint8_t v___x_2084_; 
v_a_2083_ = lean_ctor_get(v___x_2082_, 0);
lean_inc(v_a_2083_);
v___x_2084_ = lean_unbox(v_a_2083_);
lean_dec(v_a_2083_);
if (v___x_2084_ == 0)
{
lean_dec_ref(v_e_2064_);
return v___x_2082_;
}
else
{
lean_object* v___x_2085_; 
lean_dec_ref(v___x_2082_);
v___x_2085_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_2064_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_);
return v___x_2085_;
}
}
else
{
lean_dec_ref(v_e_2064_);
return v___x_2082_;
}
}
}
else
{
lean_object* v_a_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2093_; 
lean_dec_ref(v_e_2064_);
v_a_2086_ = lean_ctor_get(v___x_2072_, 0);
v_isSharedCheck_2093_ = !lean_is_exclusive(v___x_2072_);
if (v_isSharedCheck_2093_ == 0)
{
v___x_2088_ = v___x_2072_;
v_isShared_2089_ = v_isSharedCheck_2093_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_a_2086_);
lean_dec(v___x_2072_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2093_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v___x_2091_; 
if (v_isShared_2089_ == 0)
{
v___x_2091_ = v___x_2088_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v_a_2086_);
v___x_2091_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
return v___x_2091_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue___redArg___boxed(lean_object* v_e_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_){
_start:
{
lean_object* v_res_2102_; 
v_res_2102_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue___redArg(v_e_2094_, v_a_2095_, v_a_2096_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_);
lean_dec(v_a_2100_);
lean_dec_ref(v_a_2099_);
lean_dec(v_a_2098_);
lean_dec_ref(v_a_2097_);
lean_dec_ref(v_a_2096_);
lean_dec(v_a_2095_);
return v_res_2102_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue(lean_object* v_e_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_){
_start:
{
lean_object* v___x_2116_; 
v___x_2116_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue___redArg(v_e_2103_, v_a_2105_, v_a_2109_, v_a_2111_, v_a_2112_, v_a_2113_, v_a_2114_);
return v___x_2116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue___boxed(lean_object* v_e_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_){
_start:
{
lean_object* v_res_2130_; 
v_res_2130_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue(v_e_2117_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_, v_a_2122_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_);
lean_dec(v_a_2128_);
lean_dec_ref(v_a_2127_);
lean_dec(v_a_2126_);
lean_dec_ref(v_a_2125_);
lean_dec(v_a_2124_);
lean_dec_ref(v_a_2123_);
lean_dec(v_a_2122_);
lean_dec_ref(v_a_2121_);
lean_dec(v_a_2120_);
lean_dec(v_a_2119_);
lean_dec(v_a_2118_);
return v_res_2130_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__2(void){
_start:
{
lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; 
v___x_2137_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__1));
v___x_2138_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__6));
v___x_2139_ = l_Lean_Name_append(v___x_2138_, v___x_2137_);
return v___x_2139_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4(void){
_start:
{
lean_object* v___x_2141_; lean_object* v___x_2142_; 
v___x_2141_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__3));
v___x_2142_ = l_Lean_stringToMessageData(v___x_2141_);
return v___x_2142_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue(lean_object* v_u_2144_, lean_object* v_v_2145_, lean_object* v_k_2146_, lean_object* v_c_2147_, lean_object* v_e_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_){
_start:
{
lean_object* v___x_2161_; 
lean_inc_ref(v_e_2148_);
v___x_2161_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue___redArg(v_e_2148_, v_a_2150_, v_a_2154_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_);
if (lean_obj_tag(v___x_2161_) == 0)
{
lean_object* v_a_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2260_; 
v_a_2162_ = lean_ctor_get(v___x_2161_, 0);
v_isSharedCheck_2260_ = !lean_is_exclusive(v___x_2161_);
if (v_isSharedCheck_2260_ == 0)
{
v___x_2164_ = v___x_2161_;
v_isShared_2165_ = v_isSharedCheck_2260_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_a_2162_);
lean_dec(v___x_2161_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2260_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
uint8_t v___x_2166_; 
v___x_2166_ = lean_unbox(v_a_2162_);
lean_dec(v_a_2162_);
if (v___x_2166_ == 0)
{
lean_object* v_options_2167_; lean_object* v_inheritedTraceOptions_2168_; uint8_t v_hasTrace_2169_; lean_object* v___x_2170_; lean_object* v___y_2172_; lean_object* v___y_2173_; lean_object* v___y_2174_; lean_object* v___y_2175_; lean_object* v___y_2176_; lean_object* v___y_2177_; lean_object* v___y_2178_; lean_object* v___y_2179_; lean_object* v___y_2180_; lean_object* v___y_2181_; lean_object* v___y_2182_; 
v_options_2167_ = lean_ctor_get(v_a_2158_, 2);
v_inheritedTraceOptions_2168_ = lean_ctor_get(v_a_2158_, 13);
v_hasTrace_2169_ = lean_ctor_get_uint8(v_options_2167_, sizeof(void*)*1);
v___x_2170_ = l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(v_c_2147_);
if (v_hasTrace_2169_ == 0)
{
v___y_2172_ = v_a_2149_;
v___y_2173_ = v_a_2150_;
v___y_2174_ = v_a_2151_;
v___y_2175_ = v_a_2152_;
v___y_2176_ = v_a_2153_;
v___y_2177_ = v_a_2154_;
v___y_2178_ = v_a_2155_;
v___y_2179_ = v_a_2156_;
v___y_2180_ = v_a_2157_;
v___y_2181_ = v_a_2158_;
v___y_2182_ = v_a_2159_;
goto v___jp_2171_;
}
else
{
lean_object* v___x_2190_; lean_object* v___x_2191_; uint8_t v___x_2192_; 
v___x_2190_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__1));
v___x_2191_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__2, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__2);
v___x_2192_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2168_, v_options_2167_, v___x_2191_);
if (v___x_2192_ == 0)
{
v___y_2172_ = v_a_2149_;
v___y_2173_ = v_a_2150_;
v___y_2174_ = v_a_2151_;
v___y_2175_ = v_a_2152_;
v___y_2176_ = v_a_2153_;
v___y_2177_ = v_a_2154_;
v___y_2178_ = v_a_2155_;
v___y_2179_ = v_a_2156_;
v___y_2180_ = v_a_2157_;
v___y_2181_ = v_a_2158_;
v___y_2182_ = v_a_2159_;
goto v___jp_2171_;
}
else
{
lean_object* v___x_2193_; 
v___x_2193_ = l_Lean_Meta_Grind_Order_getExpr(v_u_2144_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_);
if (lean_obj_tag(v___x_2193_) == 0)
{
lean_object* v_a_2194_; lean_object* v___x_2195_; 
v_a_2194_ = lean_ctor_get(v___x_2193_, 0);
lean_inc(v_a_2194_);
lean_dec_ref(v___x_2193_);
v___x_2195_ = l_Lean_Meta_Grind_Order_getExpr(v_v_2145_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_);
if (lean_obj_tag(v___x_2195_) == 0)
{
lean_object* v_a_2196_; lean_object* v___x_2197_; 
v_a_2196_ = lean_ctor_get(v___x_2195_, 0);
lean_inc(v_a_2196_);
lean_dec_ref(v___x_2195_);
v___x_2197_ = l_Lean_Meta_Grind_Order_Cnstr_pp(v_c_2147_, v_a_2149_, v_a_2150_, v_a_2151_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_);
if (lean_obj_tag(v___x_2197_) == 0)
{
lean_object* v_a_2198_; lean_object* v_k_2199_; uint8_t v_strict_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___y_2204_; lean_object* v___y_2205_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___y_2217_; 
v_a_2198_ = lean_ctor_get(v___x_2197_, 0);
lean_inc(v_a_2198_);
lean_dec_ref(v___x_2197_);
v_k_2199_ = lean_ctor_get(v_k_2146_, 0);
v_strict_2200_ = lean_ctor_get_uint8(v_k_2146_, sizeof(void*)*1);
v___x_2201_ = l_Lean_MessageData_ofExpr(v_a_2194_);
v___x_2202_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4);
v___x_2212_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2212_, 0, v___x_2201_);
lean_ctor_set(v___x_2212_, 1, v___x_2202_);
v___x_2213_ = l_Lean_MessageData_ofExpr(v_a_2196_);
v___x_2214_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2214_, 0, v___x_2212_);
lean_ctor_set(v___x_2214_, 1, v___x_2213_);
v___x_2215_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2215_, 0, v___x_2214_);
lean_ctor_set(v___x_2215_, 1, v___x_2202_);
if (v_strict_2200_ == 0)
{
lean_object* v___x_2228_; 
v___x_2228_ = l_Int_repr(v_k_2199_);
v___y_2217_ = v___x_2228_;
goto v___jp_2216_;
}
else
{
lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; 
v___x_2229_ = l_Int_repr(v_k_2199_);
v___x_2230_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5));
v___x_2231_ = lean_string_append(v___x_2229_, v___x_2230_);
v___y_2217_ = v___x_2231_;
goto v___jp_2216_;
}
v___jp_2203_:
{
lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; 
v___x_2206_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2206_, 0, v___y_2205_);
v___x_2207_ = l_Lean_MessageData_ofFormat(v___x_2206_);
v___x_2208_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2208_, 0, v___y_2204_);
lean_ctor_set(v___x_2208_, 1, v___x_2207_);
v___x_2209_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2208_);
lean_ctor_set(v___x_2209_, 1, v___x_2202_);
v___x_2210_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2210_, 0, v___x_2209_);
lean_ctor_set(v___x_2210_, 1, v_a_2198_);
v___x_2211_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(v___x_2190_, v___x_2210_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_);
if (lean_obj_tag(v___x_2211_) == 0)
{
lean_dec_ref(v___x_2211_);
v___y_2172_ = v_a_2149_;
v___y_2173_ = v_a_2150_;
v___y_2174_ = v_a_2151_;
v___y_2175_ = v_a_2152_;
v___y_2176_ = v_a_2153_;
v___y_2177_ = v_a_2154_;
v___y_2178_ = v_a_2155_;
v___y_2179_ = v_a_2156_;
v___y_2180_ = v_a_2157_;
v___y_2181_ = v_a_2158_;
v___y_2182_ = v_a_2159_;
goto v___jp_2171_;
}
else
{
lean_dec_ref(v___x_2170_);
lean_del_object(v___x_2164_);
lean_dec_ref(v_e_2148_);
lean_dec_ref(v_c_2147_);
lean_dec_ref(v_k_2146_);
lean_dec(v_v_2145_);
lean_dec(v_u_2144_);
return v___x_2211_;
}
}
v___jp_2216_:
{
lean_object* v_k_2218_; uint8_t v_strict_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; 
v_k_2218_ = lean_ctor_get(v___x_2170_, 0);
lean_inc(v_k_2218_);
v_strict_2219_ = lean_ctor_get_uint8(v___x_2170_, sizeof(void*)*1);
v___x_2220_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2220_, 0, v___y_2217_);
v___x_2221_ = l_Lean_MessageData_ofFormat(v___x_2220_);
v___x_2222_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2222_, 0, v___x_2215_);
lean_ctor_set(v___x_2222_, 1, v___x_2221_);
v___x_2223_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2223_, 0, v___x_2222_);
lean_ctor_set(v___x_2223_, 1, v___x_2202_);
if (v_strict_2219_ == 0)
{
lean_object* v___x_2224_; 
v___x_2224_ = l_Int_repr(v_k_2218_);
lean_dec(v_k_2218_);
v___y_2204_ = v___x_2223_;
v___y_2205_ = v___x_2224_;
goto v___jp_2203_;
}
else
{
lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; 
v___x_2225_ = l_Int_repr(v_k_2218_);
lean_dec(v_k_2218_);
v___x_2226_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5));
v___x_2227_ = lean_string_append(v___x_2225_, v___x_2226_);
v___y_2204_ = v___x_2223_;
v___y_2205_ = v___x_2227_;
goto v___jp_2203_;
}
}
}
else
{
lean_object* v_a_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2239_; 
lean_dec(v_a_2196_);
lean_dec(v_a_2194_);
lean_dec_ref(v___x_2170_);
lean_del_object(v___x_2164_);
lean_dec_ref(v_e_2148_);
lean_dec_ref(v_c_2147_);
lean_dec_ref(v_k_2146_);
lean_dec(v_v_2145_);
lean_dec(v_u_2144_);
v_a_2232_ = lean_ctor_get(v___x_2197_, 0);
v_isSharedCheck_2239_ = !lean_is_exclusive(v___x_2197_);
if (v_isSharedCheck_2239_ == 0)
{
v___x_2234_ = v___x_2197_;
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_a_2232_);
lean_dec(v___x_2197_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
v_resetjp_2233_:
{
lean_object* v___x_2237_; 
if (v_isShared_2235_ == 0)
{
v___x_2237_ = v___x_2234_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v_a_2232_);
v___x_2237_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
return v___x_2237_;
}
}
}
}
else
{
lean_object* v_a_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2247_; 
lean_dec(v_a_2194_);
lean_dec_ref(v___x_2170_);
lean_del_object(v___x_2164_);
lean_dec_ref(v_e_2148_);
lean_dec_ref(v_c_2147_);
lean_dec_ref(v_k_2146_);
lean_dec(v_v_2145_);
lean_dec(v_u_2144_);
v_a_2240_ = lean_ctor_get(v___x_2195_, 0);
v_isSharedCheck_2247_ = !lean_is_exclusive(v___x_2195_);
if (v_isSharedCheck_2247_ == 0)
{
v___x_2242_ = v___x_2195_;
v_isShared_2243_ = v_isSharedCheck_2247_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_a_2240_);
lean_dec(v___x_2195_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2247_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
lean_object* v___x_2245_; 
if (v_isShared_2243_ == 0)
{
v___x_2245_ = v___x_2242_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v_a_2240_);
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
lean_dec_ref(v___x_2170_);
lean_del_object(v___x_2164_);
lean_dec_ref(v_e_2148_);
lean_dec_ref(v_c_2147_);
lean_dec_ref(v_k_2146_);
lean_dec(v_v_2145_);
lean_dec(v_u_2144_);
v_a_2248_ = lean_ctor_get(v___x_2193_, 0);
v_isSharedCheck_2255_ = !lean_is_exclusive(v___x_2193_);
if (v_isSharedCheck_2255_ == 0)
{
v___x_2250_ = v___x_2193_;
v_isShared_2251_ = v_isSharedCheck_2255_;
goto v_resetjp_2249_;
}
else
{
lean_inc(v_a_2248_);
lean_dec(v___x_2193_);
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
v___jp_2171_:
{
uint8_t v___x_2183_; 
v___x_2183_ = l_Lean_Meta_Grind_Order_instDecidableLEWeight(v_k_2146_, v___x_2170_);
if (v___x_2183_ == 0)
{
lean_object* v___x_2184_; lean_object* v___x_2186_; 
lean_dec_ref(v___x_2170_);
lean_dec_ref(v_e_2148_);
lean_dec_ref(v_c_2147_);
lean_dec_ref(v_k_2146_);
lean_dec(v_v_2145_);
lean_dec(v_u_2144_);
v___x_2184_ = lean_box(0);
if (v_isShared_2165_ == 0)
{
lean_ctor_set(v___x_2164_, 0, v___x_2184_);
v___x_2186_ = v___x_2164_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v___x_2184_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
return v___x_2186_;
}
}
else
{
lean_object* v___x_2188_; lean_object* v___x_2189_; 
lean_del_object(v___x_2164_);
v___x_2188_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2188_, 0, v_c_2147_);
lean_ctor_set(v___x_2188_, 1, v_e_2148_);
lean_ctor_set(v___x_2188_, 2, v_u_2144_);
lean_ctor_set(v___x_2188_, 3, v_v_2145_);
lean_ctor_set(v___x_2188_, 4, v_k_2146_);
lean_ctor_set(v___x_2188_, 5, v___x_2170_);
v___x_2189_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate(v___x_2188_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_);
return v___x_2189_;
}
}
}
else
{
lean_object* v___x_2256_; lean_object* v___x_2258_; 
lean_dec_ref(v_e_2148_);
lean_dec_ref(v_c_2147_);
lean_dec_ref(v_k_2146_);
lean_dec(v_v_2145_);
lean_dec(v_u_2144_);
v___x_2256_ = lean_box(0);
if (v_isShared_2165_ == 0)
{
lean_ctor_set(v___x_2164_, 0, v___x_2256_);
v___x_2258_ = v___x_2164_;
goto v_reusejp_2257_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2259_, 0, v___x_2256_);
v___x_2258_ = v_reuseFailAlloc_2259_;
goto v_reusejp_2257_;
}
v_reusejp_2257_:
{
return v___x_2258_;
}
}
}
}
else
{
lean_object* v_a_2261_; lean_object* v___x_2263_; uint8_t v_isShared_2264_; uint8_t v_isSharedCheck_2268_; 
lean_dec_ref(v_e_2148_);
lean_dec_ref(v_c_2147_);
lean_dec_ref(v_k_2146_);
lean_dec(v_v_2145_);
lean_dec(v_u_2144_);
v_a_2261_ = lean_ctor_get(v___x_2161_, 0);
v_isSharedCheck_2268_ = !lean_is_exclusive(v___x_2161_);
if (v_isSharedCheck_2268_ == 0)
{
v___x_2263_ = v___x_2161_;
v_isShared_2264_ = v_isSharedCheck_2268_;
goto v_resetjp_2262_;
}
else
{
lean_inc(v_a_2261_);
lean_dec(v___x_2161_);
v___x_2263_ = lean_box(0);
v_isShared_2264_ = v_isSharedCheck_2268_;
goto v_resetjp_2262_;
}
v_resetjp_2262_:
{
lean_object* v___x_2266_; 
if (v_isShared_2264_ == 0)
{
v___x_2266_ = v___x_2263_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2267_; 
v_reuseFailAlloc_2267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2267_, 0, v_a_2261_);
v___x_2266_ = v_reuseFailAlloc_2267_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
return v___x_2266_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___boxed(lean_object** _args){
lean_object* v_u_2269_ = _args[0];
lean_object* v_v_2270_ = _args[1];
lean_object* v_k_2271_ = _args[2];
lean_object* v_c_2272_ = _args[3];
lean_object* v_e_2273_ = _args[4];
lean_object* v_a_2274_ = _args[5];
lean_object* v_a_2275_ = _args[6];
lean_object* v_a_2276_ = _args[7];
lean_object* v_a_2277_ = _args[8];
lean_object* v_a_2278_ = _args[9];
lean_object* v_a_2279_ = _args[10];
lean_object* v_a_2280_ = _args[11];
lean_object* v_a_2281_ = _args[12];
lean_object* v_a_2282_ = _args[13];
lean_object* v_a_2283_ = _args[14];
lean_object* v_a_2284_ = _args[15];
lean_object* v_a_2285_ = _args[16];
_start:
{
lean_object* v_res_2286_; 
v_res_2286_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue(v_u_2269_, v_v_2270_, v_k_2271_, v_c_2272_, v_e_2273_, v_a_2274_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_, v_a_2284_);
lean_dec(v_a_2284_);
lean_dec_ref(v_a_2283_);
lean_dec(v_a_2282_);
lean_dec_ref(v_a_2281_);
lean_dec(v_a_2280_);
lean_dec_ref(v_a_2279_);
lean_dec(v_a_2278_);
lean_dec_ref(v_a_2277_);
lean_dec(v_a_2276_);
lean_dec(v_a_2275_);
lean_dec(v_a_2274_);
return v_res_2286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse___redArg(lean_object* v_e_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_){
_start:
{
lean_object* v___x_2295_; 
v___x_2295_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_2288_, v_a_2292_);
if (lean_obj_tag(v___x_2295_) == 0)
{
lean_object* v_a_2296_; lean_object* v_termMapInv_2297_; lean_object* v___x_2298_; 
v_a_2296_ = lean_ctor_get(v___x_2295_, 0);
lean_inc(v_a_2296_);
lean_dec_ref(v___x_2295_);
v_termMapInv_2297_ = lean_ctor_get(v_a_2296_, 4);
lean_inc_ref(v_termMapInv_2297_);
lean_dec(v_a_2296_);
v___x_2298_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMapInv_2297_, v_e_2287_);
lean_dec_ref(v_termMapInv_2297_);
if (lean_obj_tag(v___x_2298_) == 1)
{
lean_object* v_val_2299_; lean_object* v_fst_2300_; lean_object* v___x_2301_; 
lean_dec_ref(v_e_2287_);
v_val_2299_ = lean_ctor_get(v___x_2298_, 0);
lean_inc(v_val_2299_);
lean_dec_ref(v___x_2298_);
v_fst_2300_ = lean_ctor_get(v_val_2299_, 0);
lean_inc(v_fst_2300_);
lean_dec(v_val_2299_);
v___x_2301_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_fst_2300_, v_a_2288_);
if (lean_obj_tag(v___x_2301_) == 0)
{
lean_object* v_a_2302_; uint8_t v___x_2303_; 
v_a_2302_ = lean_ctor_get(v___x_2301_, 0);
lean_inc(v_a_2302_);
v___x_2303_ = lean_unbox(v_a_2302_);
lean_dec(v_a_2302_);
if (v___x_2303_ == 0)
{
lean_dec(v_fst_2300_);
return v___x_2301_;
}
else
{
lean_object* v___x_2304_; 
lean_dec_ref(v___x_2301_);
v___x_2304_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_fst_2300_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_);
return v___x_2304_;
}
}
else
{
lean_dec(v_fst_2300_);
return v___x_2301_;
}
}
else
{
lean_object* v___x_2305_; 
lean_dec(v___x_2298_);
v___x_2305_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_e_2287_, v_a_2288_);
if (lean_obj_tag(v___x_2305_) == 0)
{
lean_object* v_a_2306_; uint8_t v___x_2307_; 
v_a_2306_ = lean_ctor_get(v___x_2305_, 0);
lean_inc(v_a_2306_);
v___x_2307_ = lean_unbox(v_a_2306_);
lean_dec(v_a_2306_);
if (v___x_2307_ == 0)
{
lean_dec_ref(v_e_2287_);
return v___x_2305_;
}
else
{
lean_object* v___x_2308_; 
lean_dec_ref(v___x_2305_);
v___x_2308_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_2287_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_);
return v___x_2308_;
}
}
else
{
lean_dec_ref(v_e_2287_);
return v___x_2305_;
}
}
}
else
{
lean_object* v_a_2309_; lean_object* v___x_2311_; uint8_t v_isShared_2312_; uint8_t v_isSharedCheck_2316_; 
lean_dec_ref(v_e_2287_);
v_a_2309_ = lean_ctor_get(v___x_2295_, 0);
v_isSharedCheck_2316_ = !lean_is_exclusive(v___x_2295_);
if (v_isSharedCheck_2316_ == 0)
{
v___x_2311_ = v___x_2295_;
v_isShared_2312_ = v_isSharedCheck_2316_;
goto v_resetjp_2310_;
}
else
{
lean_inc(v_a_2309_);
lean_dec(v___x_2295_);
v___x_2311_ = lean_box(0);
v_isShared_2312_ = v_isSharedCheck_2316_;
goto v_resetjp_2310_;
}
v_resetjp_2310_:
{
lean_object* v___x_2314_; 
if (v_isShared_2312_ == 0)
{
v___x_2314_ = v___x_2311_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v_a_2309_);
v___x_2314_ = v_reuseFailAlloc_2315_;
goto v_reusejp_2313_;
}
v_reusejp_2313_:
{
return v___x_2314_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse___redArg___boxed(lean_object* v_e_2317_, lean_object* v_a_2318_, lean_object* v_a_2319_, lean_object* v_a_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_){
_start:
{
lean_object* v_res_2325_; 
v_res_2325_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse___redArg(v_e_2317_, v_a_2318_, v_a_2319_, v_a_2320_, v_a_2321_, v_a_2322_, v_a_2323_);
lean_dec(v_a_2323_);
lean_dec_ref(v_a_2322_);
lean_dec(v_a_2321_);
lean_dec_ref(v_a_2320_);
lean_dec_ref(v_a_2319_);
lean_dec(v_a_2318_);
return v_res_2325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse(lean_object* v_e_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_){
_start:
{
lean_object* v___x_2339_; 
v___x_2339_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse___redArg(v_e_2326_, v_a_2328_, v_a_2332_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
return v___x_2339_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse___boxed(lean_object* v_e_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_){
_start:
{
lean_object* v_res_2353_; 
v_res_2353_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse(v_e_2340_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_, v_a_2345_, v_a_2346_, v_a_2347_, v_a_2348_, v_a_2349_, v_a_2350_, v_a_2351_);
lean_dec(v_a_2351_);
lean_dec_ref(v_a_2350_);
lean_dec(v_a_2349_);
lean_dec_ref(v_a_2348_);
lean_dec(v_a_2347_);
lean_dec_ref(v_a_2346_);
lean_dec(v_a_2345_);
lean_dec_ref(v_a_2344_);
lean_dec(v_a_2343_);
lean_dec(v_a_2342_);
lean_dec(v_a_2341_);
return v_res_2353_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__2(void){
_start:
{
lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; 
v___x_2360_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__1));
v___x_2361_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__6));
v___x_2362_ = l_Lean_Name_append(v___x_2361_, v___x_2360_);
return v___x_2362_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__4(void){
_start:
{
lean_object* v___x_2364_; lean_object* v___x_2365_; 
v___x_2364_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__3));
v___x_2365_ = l_Lean_stringToMessageData(v___x_2364_);
return v___x_2365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse(lean_object* v_u_2366_, lean_object* v_v_2367_, lean_object* v_k_2368_, lean_object* v_c_2369_, lean_object* v_e_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_){
_start:
{
lean_object* v___x_2383_; 
lean_inc_ref(v_e_2370_);
v___x_2383_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse___redArg(v_e_2370_, v_a_2372_, v_a_2376_, v_a_2378_, v_a_2379_, v_a_2380_, v_a_2381_);
if (lean_obj_tag(v___x_2383_) == 0)
{
lean_object* v_a_2384_; lean_object* v___x_2386_; uint8_t v_isShared_2387_; uint8_t v_isSharedCheck_2484_; 
v_a_2384_ = lean_ctor_get(v___x_2383_, 0);
v_isSharedCheck_2484_ = !lean_is_exclusive(v___x_2383_);
if (v_isSharedCheck_2484_ == 0)
{
v___x_2386_ = v___x_2383_;
v_isShared_2387_ = v_isSharedCheck_2484_;
goto v_resetjp_2385_;
}
else
{
lean_inc(v_a_2384_);
lean_dec(v___x_2383_);
v___x_2386_ = lean_box(0);
v_isShared_2387_ = v_isSharedCheck_2484_;
goto v_resetjp_2385_;
}
v_resetjp_2385_:
{
uint8_t v___x_2388_; 
v___x_2388_ = lean_unbox(v_a_2384_);
lean_dec(v_a_2384_);
if (v___x_2388_ == 0)
{
lean_object* v_options_2389_; lean_object* v_inheritedTraceOptions_2390_; uint8_t v_hasTrace_2391_; lean_object* v___x_2392_; lean_object* v___y_2394_; lean_object* v___y_2395_; lean_object* v___y_2396_; lean_object* v___y_2397_; lean_object* v___y_2398_; lean_object* v___y_2399_; lean_object* v___y_2400_; lean_object* v___y_2401_; lean_object* v___y_2402_; lean_object* v___y_2403_; lean_object* v___y_2404_; 
v_options_2389_ = lean_ctor_get(v_a_2380_, 2);
v_inheritedTraceOptions_2390_ = lean_ctor_get(v_a_2380_, 13);
v_hasTrace_2391_ = lean_ctor_get_uint8(v_options_2389_, sizeof(void*)*1);
v___x_2392_ = l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(v_c_2369_);
if (v_hasTrace_2391_ == 0)
{
v___y_2394_ = v_a_2371_;
v___y_2395_ = v_a_2372_;
v___y_2396_ = v_a_2373_;
v___y_2397_ = v_a_2374_;
v___y_2398_ = v_a_2375_;
v___y_2399_ = v_a_2376_;
v___y_2400_ = v_a_2377_;
v___y_2401_ = v_a_2378_;
v___y_2402_ = v_a_2379_;
v___y_2403_ = v_a_2380_;
v___y_2404_ = v_a_2381_;
goto v___jp_2393_;
}
else
{
lean_object* v___x_2413_; lean_object* v___x_2414_; uint8_t v___x_2415_; 
v___x_2413_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__1));
v___x_2414_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__2, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__2);
v___x_2415_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2390_, v_options_2389_, v___x_2414_);
if (v___x_2415_ == 0)
{
v___y_2394_ = v_a_2371_;
v___y_2395_ = v_a_2372_;
v___y_2396_ = v_a_2373_;
v___y_2397_ = v_a_2374_;
v___y_2398_ = v_a_2375_;
v___y_2399_ = v_a_2376_;
v___y_2400_ = v_a_2377_;
v___y_2401_ = v_a_2378_;
v___y_2402_ = v_a_2379_;
v___y_2403_ = v_a_2380_;
v___y_2404_ = v_a_2381_;
goto v___jp_2393_;
}
else
{
lean_object* v___x_2416_; 
v___x_2416_ = l_Lean_Meta_Grind_Order_getExpr(v_u_2366_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_, v_a_2381_);
if (lean_obj_tag(v___x_2416_) == 0)
{
lean_object* v_a_2417_; lean_object* v___x_2418_; 
v_a_2417_ = lean_ctor_get(v___x_2416_, 0);
lean_inc(v_a_2417_);
lean_dec_ref(v___x_2416_);
v___x_2418_ = l_Lean_Meta_Grind_Order_getExpr(v_v_2367_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_, v_a_2381_);
if (lean_obj_tag(v___x_2418_) == 0)
{
lean_object* v_a_2419_; lean_object* v___x_2420_; 
v_a_2419_ = lean_ctor_get(v___x_2418_, 0);
lean_inc(v_a_2419_);
lean_dec_ref(v___x_2418_);
v___x_2420_ = l_Lean_Meta_Grind_Order_Cnstr_pp(v_c_2369_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_, v_a_2381_);
if (lean_obj_tag(v___x_2420_) == 0)
{
lean_object* v_a_2421_; lean_object* v___y_2423_; lean_object* v___y_2424_; lean_object* v_k_2432_; uint8_t v_strict_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___y_2441_; 
v_a_2421_ = lean_ctor_get(v___x_2420_, 0);
lean_inc(v_a_2421_);
lean_dec_ref(v___x_2420_);
v_k_2432_ = lean_ctor_get(v_k_2368_, 0);
v_strict_2433_ = lean_ctor_get_uint8(v_k_2368_, sizeof(void*)*1);
v___x_2434_ = l_Lean_MessageData_ofExpr(v_a_2417_);
v___x_2435_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4);
v___x_2436_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2436_, 0, v___x_2434_);
lean_ctor_set(v___x_2436_, 1, v___x_2435_);
v___x_2437_ = l_Lean_MessageData_ofExpr(v_a_2419_);
v___x_2438_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2438_, 0, v___x_2436_);
lean_ctor_set(v___x_2438_, 1, v___x_2437_);
v___x_2439_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2439_, 0, v___x_2438_);
lean_ctor_set(v___x_2439_, 1, v___x_2435_);
if (v_strict_2433_ == 0)
{
lean_object* v___x_2452_; 
v___x_2452_ = l_Int_repr(v_k_2432_);
v___y_2441_ = v___x_2452_;
goto v___jp_2440_;
}
else
{
lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; 
v___x_2453_ = l_Int_repr(v_k_2432_);
v___x_2454_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5));
v___x_2455_ = lean_string_append(v___x_2453_, v___x_2454_);
v___y_2441_ = v___x_2455_;
goto v___jp_2440_;
}
v___jp_2422_:
{
lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; 
v___x_2425_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2425_, 0, v___y_2424_);
v___x_2426_ = l_Lean_MessageData_ofFormat(v___x_2425_);
v___x_2427_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2427_, 0, v___y_2423_);
lean_ctor_set(v___x_2427_, 1, v___x_2426_);
v___x_2428_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__4);
v___x_2429_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2429_, 0, v___x_2427_);
lean_ctor_set(v___x_2429_, 1, v___x_2428_);
v___x_2430_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2430_, 0, v___x_2429_);
lean_ctor_set(v___x_2430_, 1, v_a_2421_);
v___x_2431_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(v___x_2413_, v___x_2430_, v_a_2378_, v_a_2379_, v_a_2380_, v_a_2381_);
if (lean_obj_tag(v___x_2431_) == 0)
{
lean_dec_ref(v___x_2431_);
v___y_2394_ = v_a_2371_;
v___y_2395_ = v_a_2372_;
v___y_2396_ = v_a_2373_;
v___y_2397_ = v_a_2374_;
v___y_2398_ = v_a_2375_;
v___y_2399_ = v_a_2376_;
v___y_2400_ = v_a_2377_;
v___y_2401_ = v_a_2378_;
v___y_2402_ = v_a_2379_;
v___y_2403_ = v_a_2380_;
v___y_2404_ = v_a_2381_;
goto v___jp_2393_;
}
else
{
lean_dec_ref(v___x_2392_);
lean_del_object(v___x_2386_);
lean_dec_ref(v_e_2370_);
lean_dec_ref(v_c_2369_);
lean_dec_ref(v_k_2368_);
lean_dec(v_v_2367_);
lean_dec(v_u_2366_);
return v___x_2431_;
}
}
v___jp_2440_:
{
lean_object* v_k_2442_; uint8_t v_strict_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; 
v_k_2442_ = lean_ctor_get(v___x_2392_, 0);
lean_inc(v_k_2442_);
v_strict_2443_ = lean_ctor_get_uint8(v___x_2392_, sizeof(void*)*1);
v___x_2444_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2444_, 0, v___y_2441_);
v___x_2445_ = l_Lean_MessageData_ofFormat(v___x_2444_);
v___x_2446_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2446_, 0, v___x_2439_);
lean_ctor_set(v___x_2446_, 1, v___x_2445_);
v___x_2447_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2447_, 0, v___x_2446_);
lean_ctor_set(v___x_2447_, 1, v___x_2435_);
if (v_strict_2443_ == 0)
{
lean_object* v___x_2448_; 
v___x_2448_ = l_Int_repr(v_k_2442_);
lean_dec(v_k_2442_);
v___y_2423_ = v___x_2447_;
v___y_2424_ = v___x_2448_;
goto v___jp_2422_;
}
else
{
lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; 
v___x_2449_ = l_Int_repr(v_k_2442_);
lean_dec(v_k_2442_);
v___x_2450_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5));
v___x_2451_ = lean_string_append(v___x_2449_, v___x_2450_);
v___y_2423_ = v___x_2447_;
v___y_2424_ = v___x_2451_;
goto v___jp_2422_;
}
}
}
else
{
lean_object* v_a_2456_; lean_object* v___x_2458_; uint8_t v_isShared_2459_; uint8_t v_isSharedCheck_2463_; 
lean_dec(v_a_2419_);
lean_dec(v_a_2417_);
lean_dec_ref(v___x_2392_);
lean_del_object(v___x_2386_);
lean_dec_ref(v_e_2370_);
lean_dec_ref(v_c_2369_);
lean_dec_ref(v_k_2368_);
lean_dec(v_v_2367_);
lean_dec(v_u_2366_);
v_a_2456_ = lean_ctor_get(v___x_2420_, 0);
v_isSharedCheck_2463_ = !lean_is_exclusive(v___x_2420_);
if (v_isSharedCheck_2463_ == 0)
{
v___x_2458_ = v___x_2420_;
v_isShared_2459_ = v_isSharedCheck_2463_;
goto v_resetjp_2457_;
}
else
{
lean_inc(v_a_2456_);
lean_dec(v___x_2420_);
v___x_2458_ = lean_box(0);
v_isShared_2459_ = v_isSharedCheck_2463_;
goto v_resetjp_2457_;
}
v_resetjp_2457_:
{
lean_object* v___x_2461_; 
if (v_isShared_2459_ == 0)
{
v___x_2461_ = v___x_2458_;
goto v_reusejp_2460_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v_a_2456_);
v___x_2461_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2460_;
}
v_reusejp_2460_:
{
return v___x_2461_;
}
}
}
}
else
{
lean_object* v_a_2464_; lean_object* v___x_2466_; uint8_t v_isShared_2467_; uint8_t v_isSharedCheck_2471_; 
lean_dec(v_a_2417_);
lean_dec_ref(v___x_2392_);
lean_del_object(v___x_2386_);
lean_dec_ref(v_e_2370_);
lean_dec_ref(v_c_2369_);
lean_dec_ref(v_k_2368_);
lean_dec(v_v_2367_);
lean_dec(v_u_2366_);
v_a_2464_ = lean_ctor_get(v___x_2418_, 0);
v_isSharedCheck_2471_ = !lean_is_exclusive(v___x_2418_);
if (v_isSharedCheck_2471_ == 0)
{
v___x_2466_ = v___x_2418_;
v_isShared_2467_ = v_isSharedCheck_2471_;
goto v_resetjp_2465_;
}
else
{
lean_inc(v_a_2464_);
lean_dec(v___x_2418_);
v___x_2466_ = lean_box(0);
v_isShared_2467_ = v_isSharedCheck_2471_;
goto v_resetjp_2465_;
}
v_resetjp_2465_:
{
lean_object* v___x_2469_; 
if (v_isShared_2467_ == 0)
{
v___x_2469_ = v___x_2466_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v_a_2464_);
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
lean_dec_ref(v___x_2392_);
lean_del_object(v___x_2386_);
lean_dec_ref(v_e_2370_);
lean_dec_ref(v_c_2369_);
lean_dec_ref(v_k_2368_);
lean_dec(v_v_2367_);
lean_dec(v_u_2366_);
v_a_2472_ = lean_ctor_get(v___x_2416_, 0);
v_isSharedCheck_2479_ = !lean_is_exclusive(v___x_2416_);
if (v_isSharedCheck_2479_ == 0)
{
v___x_2474_ = v___x_2416_;
v_isShared_2475_ = v_isSharedCheck_2479_;
goto v_resetjp_2473_;
}
else
{
lean_inc(v_a_2472_);
lean_dec(v___x_2416_);
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
v___jp_2393_:
{
lean_object* v___x_2405_; uint8_t v___x_2406_; 
lean_inc_ref(v___x_2392_);
v___x_2405_ = l_Lean_Meta_Grind_Order_Weight_add(v_k_2368_, v___x_2392_);
v___x_2406_ = l_Lean_Meta_Grind_Order_Weight_isNeg(v___x_2405_);
lean_dec_ref(v___x_2405_);
if (v___x_2406_ == 0)
{
lean_object* v___x_2407_; lean_object* v___x_2409_; 
lean_dec_ref(v___x_2392_);
lean_dec_ref(v_e_2370_);
lean_dec_ref(v_c_2369_);
lean_dec_ref(v_k_2368_);
lean_dec(v_v_2367_);
lean_dec(v_u_2366_);
v___x_2407_ = lean_box(0);
if (v_isShared_2387_ == 0)
{
lean_ctor_set(v___x_2386_, 0, v___x_2407_);
v___x_2409_ = v___x_2386_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v___x_2407_);
v___x_2409_ = v_reuseFailAlloc_2410_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
return v___x_2409_;
}
}
else
{
lean_object* v___x_2411_; lean_object* v___x_2412_; 
lean_del_object(v___x_2386_);
v___x_2411_ = lean_alloc_ctor(1, 6, 0);
lean_ctor_set(v___x_2411_, 0, v_c_2369_);
lean_ctor_set(v___x_2411_, 1, v_e_2370_);
lean_ctor_set(v___x_2411_, 2, v_u_2366_);
lean_ctor_set(v___x_2411_, 3, v_v_2367_);
lean_ctor_set(v___x_2411_, 4, v_k_2368_);
lean_ctor_set(v___x_2411_, 5, v___x_2392_);
v___x_2412_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate(v___x_2411_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_);
return v___x_2412_;
}
}
}
else
{
lean_object* v___x_2480_; lean_object* v___x_2482_; 
lean_dec_ref(v_e_2370_);
lean_dec_ref(v_c_2369_);
lean_dec_ref(v_k_2368_);
lean_dec(v_v_2367_);
lean_dec(v_u_2366_);
v___x_2480_ = lean_box(0);
if (v_isShared_2387_ == 0)
{
lean_ctor_set(v___x_2386_, 0, v___x_2480_);
v___x_2482_ = v___x_2386_;
goto v_reusejp_2481_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v___x_2480_);
v___x_2482_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2481_;
}
v_reusejp_2481_:
{
return v___x_2482_;
}
}
}
}
else
{
lean_object* v_a_2485_; lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2492_; 
lean_dec_ref(v_e_2370_);
lean_dec_ref(v_c_2369_);
lean_dec_ref(v_k_2368_);
lean_dec(v_v_2367_);
lean_dec(v_u_2366_);
v_a_2485_ = lean_ctor_get(v___x_2383_, 0);
v_isSharedCheck_2492_ = !lean_is_exclusive(v___x_2383_);
if (v_isSharedCheck_2492_ == 0)
{
v___x_2487_ = v___x_2383_;
v_isShared_2488_ = v_isSharedCheck_2492_;
goto v_resetjp_2486_;
}
else
{
lean_inc(v_a_2485_);
lean_dec(v___x_2383_);
v___x_2487_ = lean_box(0);
v_isShared_2488_ = v_isSharedCheck_2492_;
goto v_resetjp_2486_;
}
v_resetjp_2486_:
{
lean_object* v___x_2490_; 
if (v_isShared_2488_ == 0)
{
v___x_2490_ = v___x_2487_;
goto v_reusejp_2489_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v_a_2485_);
v___x_2490_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2489_;
}
v_reusejp_2489_:
{
return v___x_2490_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___boxed(lean_object** _args){
lean_object* v_u_2493_ = _args[0];
lean_object* v_v_2494_ = _args[1];
lean_object* v_k_2495_ = _args[2];
lean_object* v_c_2496_ = _args[3];
lean_object* v_e_2497_ = _args[4];
lean_object* v_a_2498_ = _args[5];
lean_object* v_a_2499_ = _args[6];
lean_object* v_a_2500_ = _args[7];
lean_object* v_a_2501_ = _args[8];
lean_object* v_a_2502_ = _args[9];
lean_object* v_a_2503_ = _args[10];
lean_object* v_a_2504_ = _args[11];
lean_object* v_a_2505_ = _args[12];
lean_object* v_a_2506_ = _args[13];
lean_object* v_a_2507_ = _args[14];
lean_object* v_a_2508_ = _args[15];
lean_object* v_a_2509_ = _args[16];
_start:
{
lean_object* v_res_2510_; 
v_res_2510_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse(v_u_2493_, v_v_2494_, v_k_2495_, v_c_2496_, v_e_2497_, v_a_2498_, v_a_2499_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_, v_a_2504_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_);
lean_dec(v_a_2508_);
lean_dec_ref(v_a_2507_);
lean_dec(v_a_2506_);
lean_dec_ref(v_a_2505_);
lean_dec(v_a_2504_);
lean_dec_ref(v_a_2503_);
lean_dec(v_a_2502_);
lean_dec_ref(v_a_2501_);
lean_dec(v_a_2500_);
lean_dec(v_a_2499_);
lean_dec(v_a_2498_);
return v_res_2510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___lam__0(lean_object* v_f_2511_, lean_object* v_x_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_){
_start:
{
lean_object* v_fst_2525_; lean_object* v_snd_2526_; lean_object* v___x_2527_; 
v_fst_2525_ = lean_ctor_get(v_x_2512_, 0);
lean_inc(v_fst_2525_);
v_snd_2526_ = lean_ctor_get(v_x_2512_, 1);
lean_inc(v_snd_2526_);
lean_dec_ref(v_x_2512_);
lean_inc(v___y_2523_);
lean_inc_ref(v___y_2522_);
lean_inc(v___y_2521_);
lean_inc_ref(v___y_2520_);
lean_inc(v___y_2519_);
lean_inc_ref(v___y_2518_);
lean_inc(v___y_2517_);
lean_inc_ref(v___y_2516_);
lean_inc(v___y_2515_);
lean_inc(v___y_2514_);
lean_inc(v___y_2513_);
v___x_2527_ = lean_apply_14(v_f_2511_, v_fst_2525_, v_snd_2526_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, lean_box(0));
return v___x_2527_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___lam__0___boxed(lean_object* v_f_2528_, lean_object* v_x_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_){
_start:
{
lean_object* v_res_2542_; 
v_res_2542_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___lam__0(v_f_2528_, v_x_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_);
lean_dec(v___y_2540_);
lean_dec_ref(v___y_2539_);
lean_dec(v___y_2538_);
lean_dec_ref(v___y_2537_);
lean_dec(v___y_2536_);
lean_dec_ref(v___y_2535_);
lean_dec(v___y_2534_);
lean_dec_ref(v___y_2533_);
lean_dec(v___y_2532_);
lean_dec(v___y_2531_);
lean_dec(v___y_2530_);
return v_res_2542_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__2(void){
_start:
{
lean_object* v___x_2546_; lean_object* v___f_2547_; 
v___x_2546_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___f_2547_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2547_, 0, v___x_2546_);
return v___f_2547_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__3(void){
_start:
{
lean_object* v___f_2548_; lean_object* v___f_2549_; 
v___f_2548_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__2, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__2);
v___f_2549_ = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2549_, 0, v___f_2548_);
lean_closure_set(v___f_2549_, 1, v___f_2548_);
return v___f_2549_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf(lean_object* v_u_2550_, lean_object* v_v_2551_, lean_object* v_f_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_){
_start:
{
lean_object* v___x_2565_; lean_object* v_toApplicative_2566_; lean_object* v_toFunctor_2567_; lean_object* v_toSeq_2568_; lean_object* v_toSeqLeft_2569_; lean_object* v_toSeqRight_2570_; lean_object* v___f_2571_; lean_object* v___f_2572_; lean_object* v___f_2573_; lean_object* v___f_2574_; lean_object* v___x_2575_; lean_object* v___f_2576_; lean_object* v___f_2577_; lean_object* v___f_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v_toApplicative_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2643_; 
v___x_2565_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__1, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__1);
v_toApplicative_2566_ = lean_ctor_get(v___x_2565_, 0);
v_toFunctor_2567_ = lean_ctor_get(v_toApplicative_2566_, 0);
v_toSeq_2568_ = lean_ctor_get(v_toApplicative_2566_, 2);
v_toSeqLeft_2569_ = lean_ctor_get(v_toApplicative_2566_, 3);
v_toSeqRight_2570_ = lean_ctor_get(v_toApplicative_2566_, 4);
v___f_2571_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__2));
v___f_2572_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__3));
lean_inc_ref_n(v_toFunctor_2567_, 2);
v___f_2573_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2573_, 0, v_toFunctor_2567_);
v___f_2574_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2574_, 0, v_toFunctor_2567_);
v___x_2575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2575_, 0, v___f_2573_);
lean_ctor_set(v___x_2575_, 1, v___f_2574_);
lean_inc(v_toSeqRight_2570_);
v___f_2576_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2576_, 0, v_toSeqRight_2570_);
lean_inc(v_toSeqLeft_2569_);
v___f_2577_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2577_, 0, v_toSeqLeft_2569_);
lean_inc(v_toSeq_2568_);
v___f_2578_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2578_, 0, v_toSeq_2568_);
v___x_2579_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2579_, 0, v___x_2575_);
lean_ctor_set(v___x_2579_, 1, v___f_2571_);
lean_ctor_set(v___x_2579_, 2, v___f_2578_);
lean_ctor_set(v___x_2579_, 3, v___f_2577_);
lean_ctor_set(v___x_2579_, 4, v___f_2576_);
v___x_2580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2580_, 0, v___x_2579_);
lean_ctor_set(v___x_2580_, 1, v___f_2572_);
v___x_2581_ = l_StateRefT_x27_instMonad___redArg(v___x_2580_);
v_toApplicative_2582_ = lean_ctor_get(v___x_2581_, 0);
v_isSharedCheck_2643_ = !lean_is_exclusive(v___x_2581_);
if (v_isSharedCheck_2643_ == 0)
{
lean_object* v_unused_2644_; 
v_unused_2644_ = lean_ctor_get(v___x_2581_, 1);
lean_dec(v_unused_2644_);
v___x_2584_ = v___x_2581_;
v_isShared_2585_ = v_isSharedCheck_2643_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_toApplicative_2582_);
lean_dec(v___x_2581_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2643_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
lean_object* v_toFunctor_2586_; lean_object* v_toSeq_2587_; lean_object* v_toSeqLeft_2588_; lean_object* v_toSeqRight_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2641_; 
v_toFunctor_2586_ = lean_ctor_get(v_toApplicative_2582_, 0);
v_toSeq_2587_ = lean_ctor_get(v_toApplicative_2582_, 2);
v_toSeqLeft_2588_ = lean_ctor_get(v_toApplicative_2582_, 3);
v_toSeqRight_2589_ = lean_ctor_get(v_toApplicative_2582_, 4);
v_isSharedCheck_2641_ = !lean_is_exclusive(v_toApplicative_2582_);
if (v_isSharedCheck_2641_ == 0)
{
lean_object* v_unused_2642_; 
v_unused_2642_ = lean_ctor_get(v_toApplicative_2582_, 1);
lean_dec(v_unused_2642_);
v___x_2591_ = v_toApplicative_2582_;
v_isShared_2592_ = v_isSharedCheck_2641_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_toSeqRight_2589_);
lean_inc(v_toSeqLeft_2588_);
lean_inc(v_toSeq_2587_);
lean_inc(v_toFunctor_2586_);
lean_dec(v_toApplicative_2582_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2641_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v___f_2593_; lean_object* v___f_2594_; lean_object* v___f_2595_; lean_object* v___f_2596_; lean_object* v___x_2597_; lean_object* v___f_2598_; lean_object* v___f_2599_; lean_object* v___f_2600_; lean_object* v___x_2602_; 
v___f_2593_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__4));
v___f_2594_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__5));
lean_inc_ref(v_toFunctor_2586_);
v___f_2595_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2595_, 0, v_toFunctor_2586_);
v___f_2596_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2596_, 0, v_toFunctor_2586_);
v___x_2597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2597_, 0, v___f_2595_);
lean_ctor_set(v___x_2597_, 1, v___f_2596_);
v___f_2598_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2598_, 0, v_toSeqRight_2589_);
v___f_2599_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2599_, 0, v_toSeqLeft_2588_);
v___f_2600_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2600_, 0, v_toSeq_2587_);
if (v_isShared_2592_ == 0)
{
lean_ctor_set(v___x_2591_, 4, v___f_2598_);
lean_ctor_set(v___x_2591_, 3, v___f_2599_);
lean_ctor_set(v___x_2591_, 2, v___f_2600_);
lean_ctor_set(v___x_2591_, 1, v___f_2593_);
lean_ctor_set(v___x_2591_, 0, v___x_2597_);
v___x_2602_ = v___x_2591_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2640_; 
v_reuseFailAlloc_2640_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2640_, 0, v___x_2597_);
lean_ctor_set(v_reuseFailAlloc_2640_, 1, v___f_2593_);
lean_ctor_set(v_reuseFailAlloc_2640_, 2, v___f_2600_);
lean_ctor_set(v_reuseFailAlloc_2640_, 3, v___f_2599_);
lean_ctor_set(v_reuseFailAlloc_2640_, 4, v___f_2598_);
v___x_2602_ = v_reuseFailAlloc_2640_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
lean_object* v___x_2604_; 
if (v_isShared_2585_ == 0)
{
lean_ctor_set(v___x_2584_, 1, v___f_2594_);
lean_ctor_set(v___x_2584_, 0, v___x_2602_);
v___x_2604_ = v___x_2584_;
goto v_reusejp_2603_;
}
else
{
lean_object* v_reuseFailAlloc_2639_; 
v_reuseFailAlloc_2639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2639_, 0, v___x_2602_);
lean_ctor_set(v_reuseFailAlloc_2639_, 1, v___f_2594_);
v___x_2604_ = v_reuseFailAlloc_2639_;
goto v_reusejp_2603_;
}
v_reusejp_2603_:
{
lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___f_2612_; lean_object* v___x_2613_; 
v___x_2605_ = l_StateRefT_x27_instMonad___redArg(v___x_2604_);
v___x_2606_ = l_ReaderT_instMonad___redArg(v___x_2605_);
v___x_2607_ = l_StateRefT_x27_instMonad___redArg(v___x_2606_);
v___x_2608_ = l_ReaderT_instMonad___redArg(v___x_2607_);
v___x_2609_ = l_ReaderT_instMonad___redArg(v___x_2608_);
v___x_2610_ = l_StateRefT_x27_instMonad___redArg(v___x_2609_);
v___x_2611_ = l_ReaderT_instMonad___redArg(v___x_2610_);
v___f_2612_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__1));
v___x_2613_ = l_Lean_Meta_Grind_Order_getStruct(v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_, v_a_2563_);
if (lean_obj_tag(v___x_2613_) == 0)
{
lean_object* v_a_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2630_; 
v_a_2614_ = lean_ctor_get(v___x_2613_, 0);
v_isSharedCheck_2630_ = !lean_is_exclusive(v___x_2613_);
if (v_isSharedCheck_2630_ == 0)
{
v___x_2616_ = v___x_2613_;
v_isShared_2617_ = v_isSharedCheck_2630_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_a_2614_);
lean_dec(v___x_2613_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2630_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
lean_object* v___f_2618_; lean_object* v_cnstrsOf_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; 
v___f_2618_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__3);
v_cnstrsOf_2619_ = lean_ctor_get(v_a_2614_, 17);
lean_inc_ref(v_cnstrsOf_2619_);
lean_dec(v_a_2614_);
v___x_2620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2620_, 0, v_u_2550_);
lean_ctor_set(v___x_2620_, 1, v_v_2551_);
v___x_2621_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_2618_, v___f_2612_, v_cnstrsOf_2619_, v___x_2620_);
lean_dec_ref(v_cnstrsOf_2619_);
if (lean_obj_tag(v___x_2621_) == 1)
{
lean_object* v_val_2622_; lean_object* v___f_2623_; lean_object* v___x_1496__overap_2624_; lean_object* v___x_2625_; 
lean_del_object(v___x_2616_);
v_val_2622_ = lean_ctor_get(v___x_2621_, 0);
lean_inc(v_val_2622_);
lean_dec_ref(v___x_2621_);
v___f_2623_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___lam__0___boxed), 14, 1);
lean_closure_set(v___f_2623_, 0, v_f_2552_);
v___x_1496__overap_2624_ = l_List_forM___redArg(v___x_2611_, v_val_2622_, v___f_2623_);
lean_inc(v_a_2563_);
lean_inc_ref(v_a_2562_);
lean_inc(v_a_2561_);
lean_inc_ref(v_a_2560_);
lean_inc(v_a_2559_);
lean_inc_ref(v_a_2558_);
lean_inc(v_a_2557_);
lean_inc_ref(v_a_2556_);
lean_inc(v_a_2555_);
lean_inc(v_a_2554_);
lean_inc(v_a_2553_);
v___x_2625_ = lean_apply_12(v___x_1496__overap_2624_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_, v_a_2563_, lean_box(0));
return v___x_2625_;
}
else
{
lean_object* v___x_2626_; lean_object* v___x_2628_; 
lean_dec(v___x_2621_);
lean_dec_ref(v___x_2611_);
lean_dec_ref(v_f_2552_);
v___x_2626_ = lean_box(0);
if (v_isShared_2617_ == 0)
{
lean_ctor_set(v___x_2616_, 0, v___x_2626_);
v___x_2628_ = v___x_2616_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2629_; 
v_reuseFailAlloc_2629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2629_, 0, v___x_2626_);
v___x_2628_ = v_reuseFailAlloc_2629_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
return v___x_2628_;
}
}
}
}
else
{
lean_object* v_a_2631_; lean_object* v___x_2633_; uint8_t v_isShared_2634_; uint8_t v_isSharedCheck_2638_; 
lean_dec_ref(v___x_2611_);
lean_dec_ref(v_f_2552_);
lean_dec(v_v_2551_);
lean_dec(v_u_2550_);
v_a_2631_ = lean_ctor_get(v___x_2613_, 0);
v_isSharedCheck_2638_ = !lean_is_exclusive(v___x_2613_);
if (v_isSharedCheck_2638_ == 0)
{
v___x_2633_ = v___x_2613_;
v_isShared_2634_ = v_isSharedCheck_2638_;
goto v_resetjp_2632_;
}
else
{
lean_inc(v_a_2631_);
lean_dec(v___x_2613_);
v___x_2633_ = lean_box(0);
v_isShared_2634_ = v_isSharedCheck_2638_;
goto v_resetjp_2632_;
}
v_resetjp_2632_:
{
lean_object* v___x_2636_; 
if (v_isShared_2634_ == 0)
{
v___x_2636_ = v___x_2633_;
goto v_reusejp_2635_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v_a_2631_);
v___x_2636_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2635_;
}
v_reusejp_2635_:
{
return v___x_2636_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___boxed(lean_object* v_u_2645_, lean_object* v_v_2646_, lean_object* v_f_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_){
_start:
{
lean_object* v_res_2660_; 
v_res_2660_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf(v_u_2645_, v_v_2646_, v_f_2647_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_, v_a_2656_, v_a_2657_, v_a_2658_);
lean_dec(v_a_2658_);
lean_dec_ref(v_a_2657_);
lean_dec(v_a_2656_);
lean_dec_ref(v_a_2655_);
lean_dec(v_a_2654_);
lean_dec_ref(v_a_2653_);
lean_dec(v_a_2652_);
lean_dec_ref(v_a_2651_);
lean_dec(v_a_2650_);
lean_dec(v_a_2649_);
lean_dec(v_a_2648_);
return v_res_2660_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___redArg(lean_object* v_e_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_){
_start:
{
lean_object* v___x_2665_; 
v___x_2665_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_2662_, v_a_2663_);
if (lean_obj_tag(v___x_2665_) == 0)
{
lean_object* v_a_2666_; lean_object* v___x_2668_; uint8_t v_isShared_2669_; uint8_t v_isSharedCheck_2688_; 
v_a_2666_ = lean_ctor_get(v___x_2665_, 0);
v_isSharedCheck_2688_ = !lean_is_exclusive(v___x_2665_);
if (v_isSharedCheck_2688_ == 0)
{
v___x_2668_ = v___x_2665_;
v_isShared_2669_ = v_isSharedCheck_2688_;
goto v_resetjp_2667_;
}
else
{
lean_inc(v_a_2666_);
lean_dec(v___x_2665_);
v___x_2668_ = lean_box(0);
v_isShared_2669_ = v_isSharedCheck_2688_;
goto v_resetjp_2667_;
}
v_resetjp_2667_:
{
lean_object* v_termMapInv_2670_; lean_object* v___x_2671_; 
v_termMapInv_2670_ = lean_ctor_get(v_a_2666_, 4);
lean_inc_ref(v_termMapInv_2670_);
lean_dec(v_a_2666_);
v___x_2671_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMapInv_2670_, v_e_2661_);
lean_dec_ref(v_termMapInv_2670_);
if (lean_obj_tag(v___x_2671_) == 1)
{
lean_object* v_val_2672_; lean_object* v___x_2674_; uint8_t v_isShared_2675_; uint8_t v_isSharedCheck_2683_; 
v_val_2672_ = lean_ctor_get(v___x_2671_, 0);
v_isSharedCheck_2683_ = !lean_is_exclusive(v___x_2671_);
if (v_isSharedCheck_2683_ == 0)
{
v___x_2674_ = v___x_2671_;
v_isShared_2675_ = v_isSharedCheck_2683_;
goto v_resetjp_2673_;
}
else
{
lean_inc(v_val_2672_);
lean_dec(v___x_2671_);
v___x_2674_ = lean_box(0);
v_isShared_2675_ = v_isSharedCheck_2683_;
goto v_resetjp_2673_;
}
v_resetjp_2673_:
{
lean_object* v_fst_2676_; lean_object* v___x_2678_; 
v_fst_2676_ = lean_ctor_get(v_val_2672_, 0);
lean_inc(v_fst_2676_);
lean_dec(v_val_2672_);
if (v_isShared_2675_ == 0)
{
lean_ctor_set(v___x_2674_, 0, v_fst_2676_);
v___x_2678_ = v___x_2674_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v_fst_2676_);
v___x_2678_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2677_;
}
v_reusejp_2677_:
{
lean_object* v___x_2680_; 
if (v_isShared_2669_ == 0)
{
lean_ctor_set(v___x_2668_, 0, v___x_2678_);
v___x_2680_ = v___x_2668_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v___x_2678_);
v___x_2680_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
return v___x_2680_;
}
}
}
}
else
{
lean_object* v___x_2684_; lean_object* v___x_2686_; 
lean_dec(v___x_2671_);
v___x_2684_ = lean_box(0);
if (v_isShared_2669_ == 0)
{
lean_ctor_set(v___x_2668_, 0, v___x_2684_);
v___x_2686_ = v___x_2668_;
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
lean_object* v_a_2689_; lean_object* v___x_2691_; uint8_t v_isShared_2692_; uint8_t v_isSharedCheck_2696_; 
v_a_2689_ = lean_ctor_get(v___x_2665_, 0);
v_isSharedCheck_2696_ = !lean_is_exclusive(v___x_2665_);
if (v_isSharedCheck_2696_ == 0)
{
v___x_2691_ = v___x_2665_;
v_isShared_2692_ = v_isSharedCheck_2696_;
goto v_resetjp_2690_;
}
else
{
lean_inc(v_a_2689_);
lean_dec(v___x_2665_);
v___x_2691_ = lean_box(0);
v_isShared_2692_ = v_isSharedCheck_2696_;
goto v_resetjp_2690_;
}
v_resetjp_2690_:
{
lean_object* v___x_2694_; 
if (v_isShared_2692_ == 0)
{
v___x_2694_ = v___x_2691_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v_a_2689_);
v___x_2694_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
return v___x_2694_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___redArg___boxed(lean_object* v_e_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_, lean_object* v_a_2700_){
_start:
{
lean_object* v_res_2701_; 
v_res_2701_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___redArg(v_e_2697_, v_a_2698_, v_a_2699_);
lean_dec_ref(v_a_2699_);
lean_dec(v_a_2698_);
lean_dec_ref(v_e_2697_);
return v_res_2701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f(lean_object* v_e_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_){
_start:
{
lean_object* v___x_2714_; 
v___x_2714_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___redArg(v_e_2702_, v_a_2703_, v_a_2711_);
return v___x_2714_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___boxed(lean_object* v_e_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_){
_start:
{
lean_object* v_res_2727_; 
v_res_2727_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f(v_e_2715_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_, v_a_2720_, v_a_2721_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_);
lean_dec(v_a_2725_);
lean_dec_ref(v_a_2724_);
lean_dec(v_a_2723_);
lean_dec_ref(v_a_2722_);
lean_dec(v_a_2721_);
lean_dec_ref(v_a_2720_);
lean_dec(v_a_2719_);
lean_dec_ref(v_a_2718_);
lean_dec(v_a_2717_);
lean_dec(v_a_2716_);
lean_dec_ref(v_e_2715_);
return v_res_2727_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq(lean_object* v_u_2728_, lean_object* v_v_2729_, lean_object* v_k_2730_, lean_object* v_a_2731_, lean_object* v_a_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_, lean_object* v_a_2738_, lean_object* v_a_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_){
_start:
{
lean_object* v___y_2744_; lean_object* v___y_2745_; lean_object* v___y_2746_; uint8_t v___x_2786_; 
v___x_2786_ = lean_nat_dec_eq(v_u_2728_, v_v_2729_);
if (v___x_2786_ == 0)
{
lean_object* v___x_2787_; 
v___x_2787_ = l_Lean_Meta_Grind_Order_isPartialOrder(v_a_2731_, v_a_2732_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_, v_a_2737_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_);
if (lean_obj_tag(v___x_2787_) == 0)
{
lean_object* v_a_2788_; lean_object* v___x_2790_; uint8_t v_isShared_2791_; uint8_t v_isSharedCheck_2924_; 
v_a_2788_ = lean_ctor_get(v___x_2787_, 0);
v_isSharedCheck_2924_ = !lean_is_exclusive(v___x_2787_);
if (v_isSharedCheck_2924_ == 0)
{
v___x_2790_ = v___x_2787_;
v_isShared_2791_ = v_isSharedCheck_2924_;
goto v_resetjp_2789_;
}
else
{
lean_inc(v_a_2788_);
lean_dec(v___x_2787_);
v___x_2790_ = lean_box(0);
v_isShared_2791_ = v_isSharedCheck_2924_;
goto v_resetjp_2789_;
}
v_resetjp_2789_:
{
uint8_t v___x_2797_; 
v___x_2797_ = lean_unbox(v_a_2788_);
lean_dec(v_a_2788_);
if (v___x_2797_ == 0)
{
lean_object* v___x_2798_; lean_object* v___x_2799_; 
lean_del_object(v___x_2790_);
lean_dec(v_v_2729_);
lean_dec(v_u_2728_);
v___x_2798_ = lean_box(0);
v___x_2799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2799_, 0, v___x_2798_);
return v___x_2799_;
}
else
{
uint8_t v___x_2800_; 
v___x_2800_ = l_Lean_Meta_Grind_Order_Weight_isZero(v_k_2730_);
if (v___x_2800_ == 0)
{
lean_dec(v_v_2729_);
lean_dec(v_u_2728_);
goto v___jp_2792_;
}
else
{
if (v___x_2786_ == 0)
{
lean_object* v___x_2801_; 
lean_del_object(v___x_2790_);
v___x_2801_ = l_Lean_Meta_Grind_Order_getDist_x3f(v_v_2729_, v_u_2728_, v_a_2731_, v_a_2732_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_, v_a_2737_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_);
if (lean_obj_tag(v___x_2801_) == 0)
{
lean_object* v_a_2802_; lean_object* v___x_2804_; uint8_t v_isShared_2805_; uint8_t v_isSharedCheck_2915_; 
v_a_2802_ = lean_ctor_get(v___x_2801_, 0);
v_isSharedCheck_2915_ = !lean_is_exclusive(v___x_2801_);
if (v_isSharedCheck_2915_ == 0)
{
v___x_2804_ = v___x_2801_;
v_isShared_2805_ = v_isSharedCheck_2915_;
goto v_resetjp_2803_;
}
else
{
lean_inc(v_a_2802_);
lean_dec(v___x_2801_);
v___x_2804_ = lean_box(0);
v_isShared_2805_ = v_isSharedCheck_2915_;
goto v_resetjp_2803_;
}
v_resetjp_2803_:
{
if (lean_obj_tag(v_a_2802_) == 1)
{
lean_object* v_val_2806_; uint8_t v___x_2807_; 
v_val_2806_ = lean_ctor_get(v_a_2802_, 0);
lean_inc(v_val_2806_);
lean_dec_ref(v_a_2802_);
v___x_2807_ = l_Lean_Meta_Grind_Order_Weight_isZero(v_val_2806_);
lean_dec(v_val_2806_);
if (v___x_2807_ == 0)
{
lean_object* v___x_2808_; lean_object* v___x_2810_; 
lean_dec(v_v_2729_);
lean_dec(v_u_2728_);
v___x_2808_ = lean_box(0);
if (v_isShared_2805_ == 0)
{
lean_ctor_set(v___x_2804_, 0, v___x_2808_);
v___x_2810_ = v___x_2804_;
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
lean_del_object(v___x_2804_);
v___x_2812_ = l_Lean_Meta_Grind_Order_getExpr(v_u_2728_, v_a_2731_, v_a_2732_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_, v_a_2737_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_);
if (lean_obj_tag(v___x_2812_) == 0)
{
lean_object* v_a_2813_; lean_object* v___x_2814_; 
v_a_2813_ = lean_ctor_get(v___x_2812_, 0);
lean_inc(v_a_2813_);
lean_dec_ref(v___x_2812_);
v___x_2814_ = l_Lean_Meta_Grind_Order_getExpr(v_v_2729_, v_a_2731_, v_a_2732_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_, v_a_2737_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_);
if (lean_obj_tag(v___x_2814_) == 0)
{
lean_object* v_a_2815_; lean_object* v___y_2817_; lean_object* v___x_2891_; 
v_a_2815_ = lean_ctor_get(v___x_2814_, 0);
lean_inc(v_a_2815_);
lean_dec_ref(v___x_2814_);
v___x_2891_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_a_2813_, v_a_2732_);
if (lean_obj_tag(v___x_2891_) == 0)
{
lean_object* v_a_2892_; uint8_t v___x_2893_; 
v_a_2892_ = lean_ctor_get(v___x_2891_, 0);
lean_inc(v_a_2892_);
v___x_2893_ = lean_unbox(v_a_2892_);
lean_dec(v_a_2892_);
if (v___x_2893_ == 0)
{
v___y_2817_ = v___x_2891_;
goto v___jp_2816_;
}
else
{
lean_object* v___x_2894_; 
lean_dec_ref(v___x_2891_);
v___x_2894_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_a_2815_, v_a_2732_);
v___y_2817_ = v___x_2894_;
goto v___jp_2816_;
}
}
else
{
v___y_2817_ = v___x_2891_;
goto v___jp_2816_;
}
v___jp_2816_:
{
if (lean_obj_tag(v___y_2817_) == 0)
{
lean_object* v_a_2818_; uint8_t v___x_2819_; 
v_a_2818_ = lean_ctor_get(v___y_2817_, 0);
lean_inc(v_a_2818_);
lean_dec_ref(v___y_2817_);
v___x_2819_ = lean_unbox(v_a_2818_);
lean_dec(v_a_2818_);
if (v___x_2819_ == 0)
{
lean_object* v___x_2820_; 
v___x_2820_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___redArg(v_a_2813_, v_a_2732_, v_a_2740_);
lean_dec(v_a_2813_);
if (lean_obj_tag(v___x_2820_) == 0)
{
lean_object* v_a_2821_; lean_object* v___x_2823_; uint8_t v_isShared_2824_; uint8_t v_isSharedCheck_2853_; 
v_a_2821_ = lean_ctor_get(v___x_2820_, 0);
v_isSharedCheck_2853_ = !lean_is_exclusive(v___x_2820_);
if (v_isSharedCheck_2853_ == 0)
{
v___x_2823_ = v___x_2820_;
v_isShared_2824_ = v_isSharedCheck_2853_;
goto v_resetjp_2822_;
}
else
{
lean_inc(v_a_2821_);
lean_dec(v___x_2820_);
v___x_2823_ = lean_box(0);
v_isShared_2824_ = v_isSharedCheck_2853_;
goto v_resetjp_2822_;
}
v_resetjp_2822_:
{
if (lean_obj_tag(v_a_2821_) == 1)
{
lean_object* v_val_2825_; lean_object* v___x_2826_; 
lean_del_object(v___x_2823_);
v_val_2825_ = lean_ctor_get(v_a_2821_, 0);
lean_inc(v_val_2825_);
lean_dec_ref(v_a_2821_);
v___x_2826_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___redArg(v_a_2815_, v_a_2732_, v_a_2740_);
lean_dec(v_a_2815_);
if (lean_obj_tag(v___x_2826_) == 0)
{
lean_object* v_a_2827_; lean_object* v___x_2829_; uint8_t v_isShared_2830_; uint8_t v_isSharedCheck_2840_; 
v_a_2827_ = lean_ctor_get(v___x_2826_, 0);
v_isSharedCheck_2840_ = !lean_is_exclusive(v___x_2826_);
if (v_isSharedCheck_2840_ == 0)
{
v___x_2829_ = v___x_2826_;
v_isShared_2830_ = v_isSharedCheck_2840_;
goto v_resetjp_2828_;
}
else
{
lean_inc(v_a_2827_);
lean_dec(v___x_2826_);
v___x_2829_ = lean_box(0);
v_isShared_2830_ = v_isSharedCheck_2840_;
goto v_resetjp_2828_;
}
v_resetjp_2828_:
{
if (lean_obj_tag(v_a_2827_) == 1)
{
lean_object* v_val_2831_; lean_object* v___x_2832_; 
lean_del_object(v___x_2829_);
v_val_2831_ = lean_ctor_get(v_a_2827_, 0);
lean_inc(v_val_2831_);
lean_dec_ref(v_a_2827_);
v___x_2832_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_val_2825_, v_a_2732_);
if (lean_obj_tag(v___x_2832_) == 0)
{
lean_object* v_a_2833_; uint8_t v___x_2834_; 
v_a_2833_ = lean_ctor_get(v___x_2832_, 0);
lean_inc(v_a_2833_);
v___x_2834_ = lean_unbox(v_a_2833_);
lean_dec(v_a_2833_);
if (v___x_2834_ == 0)
{
v___y_2744_ = v_val_2831_;
v___y_2745_ = v_val_2825_;
v___y_2746_ = v___x_2832_;
goto v___jp_2743_;
}
else
{
lean_object* v___x_2835_; 
lean_dec_ref(v___x_2832_);
v___x_2835_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_val_2831_, v_a_2732_);
v___y_2744_ = v_val_2831_;
v___y_2745_ = v_val_2825_;
v___y_2746_ = v___x_2835_;
goto v___jp_2743_;
}
}
else
{
v___y_2744_ = v_val_2831_;
v___y_2745_ = v_val_2825_;
v___y_2746_ = v___x_2832_;
goto v___jp_2743_;
}
}
else
{
lean_object* v___x_2836_; lean_object* v___x_2838_; 
lean_dec(v_a_2827_);
lean_dec(v_val_2825_);
lean_dec(v_v_2729_);
lean_dec(v_u_2728_);
v___x_2836_ = lean_box(0);
if (v_isShared_2830_ == 0)
{
lean_ctor_set(v___x_2829_, 0, v___x_2836_);
v___x_2838_ = v___x_2829_;
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
lean_dec(v_val_2825_);
lean_dec(v_v_2729_);
lean_dec(v_u_2728_);
v_a_2841_ = lean_ctor_get(v___x_2826_, 0);
v_isSharedCheck_2848_ = !lean_is_exclusive(v___x_2826_);
if (v_isSharedCheck_2848_ == 0)
{
v___x_2843_ = v___x_2826_;
v_isShared_2844_ = v_isSharedCheck_2848_;
goto v_resetjp_2842_;
}
else
{
lean_inc(v_a_2841_);
lean_dec(v___x_2826_);
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
lean_object* v___x_2849_; lean_object* v___x_2851_; 
lean_dec(v_a_2821_);
lean_dec(v_a_2815_);
lean_dec(v_v_2729_);
lean_dec(v_u_2728_);
v___x_2849_ = lean_box(0);
if (v_isShared_2824_ == 0)
{
lean_ctor_set(v___x_2823_, 0, v___x_2849_);
v___x_2851_ = v___x_2823_;
goto v_reusejp_2850_;
}
else
{
lean_object* v_reuseFailAlloc_2852_; 
v_reuseFailAlloc_2852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2852_, 0, v___x_2849_);
v___x_2851_ = v_reuseFailAlloc_2852_;
goto v_reusejp_2850_;
}
v_reusejp_2850_:
{
return v___x_2851_;
}
}
}
}
else
{
lean_object* v_a_2854_; lean_object* v___x_2856_; uint8_t v_isShared_2857_; uint8_t v_isSharedCheck_2861_; 
lean_dec(v_a_2815_);
lean_dec(v_v_2729_);
lean_dec(v_u_2728_);
v_a_2854_ = lean_ctor_get(v___x_2820_, 0);
v_isSharedCheck_2861_ = !lean_is_exclusive(v___x_2820_);
if (v_isSharedCheck_2861_ == 0)
{
v___x_2856_ = v___x_2820_;
v_isShared_2857_ = v_isSharedCheck_2861_;
goto v_resetjp_2855_;
}
else
{
lean_inc(v_a_2854_);
lean_dec(v___x_2820_);
v___x_2856_ = lean_box(0);
v_isShared_2857_ = v_isSharedCheck_2861_;
goto v_resetjp_2855_;
}
v_resetjp_2855_:
{
lean_object* v___x_2859_; 
if (v_isShared_2857_ == 0)
{
v___x_2859_ = v___x_2856_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2860_; 
v_reuseFailAlloc_2860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2860_, 0, v_a_2854_);
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
lean_object* v___x_2862_; 
v___x_2862_ = l_Lean_Meta_Grind_isEqv___redArg(v_a_2813_, v_a_2815_, v_a_2732_);
lean_dec(v_a_2815_);
lean_dec(v_a_2813_);
if (lean_obj_tag(v___x_2862_) == 0)
{
lean_object* v_a_2863_; lean_object* v___x_2865_; uint8_t v_isShared_2866_; uint8_t v_isSharedCheck_2874_; 
v_a_2863_ = lean_ctor_get(v___x_2862_, 0);
v_isSharedCheck_2874_ = !lean_is_exclusive(v___x_2862_);
if (v_isSharedCheck_2874_ == 0)
{
v___x_2865_ = v___x_2862_;
v_isShared_2866_ = v_isSharedCheck_2874_;
goto v_resetjp_2864_;
}
else
{
lean_inc(v_a_2863_);
lean_dec(v___x_2862_);
v___x_2865_ = lean_box(0);
v_isShared_2866_ = v_isSharedCheck_2874_;
goto v_resetjp_2864_;
}
v_resetjp_2864_:
{
uint8_t v___x_2867_; 
v___x_2867_ = lean_unbox(v_a_2863_);
lean_dec(v_a_2863_);
if (v___x_2867_ == 0)
{
lean_object* v___x_2868_; lean_object* v___x_2869_; 
lean_del_object(v___x_2865_);
v___x_2868_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2868_, 0, v_u_2728_);
lean_ctor_set(v___x_2868_, 1, v_v_2729_);
v___x_2869_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate(v___x_2868_, v_a_2731_, v_a_2732_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_, v_a_2737_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_);
return v___x_2869_;
}
else
{
lean_object* v___x_2870_; lean_object* v___x_2872_; 
lean_dec(v_v_2729_);
lean_dec(v_u_2728_);
v___x_2870_ = lean_box(0);
if (v_isShared_2866_ == 0)
{
lean_ctor_set(v___x_2865_, 0, v___x_2870_);
v___x_2872_ = v___x_2865_;
goto v_reusejp_2871_;
}
else
{
lean_object* v_reuseFailAlloc_2873_; 
v_reuseFailAlloc_2873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2873_, 0, v___x_2870_);
v___x_2872_ = v_reuseFailAlloc_2873_;
goto v_reusejp_2871_;
}
v_reusejp_2871_:
{
return v___x_2872_;
}
}
}
}
else
{
lean_object* v_a_2875_; lean_object* v___x_2877_; uint8_t v_isShared_2878_; uint8_t v_isSharedCheck_2882_; 
lean_dec(v_v_2729_);
lean_dec(v_u_2728_);
v_a_2875_ = lean_ctor_get(v___x_2862_, 0);
v_isSharedCheck_2882_ = !lean_is_exclusive(v___x_2862_);
if (v_isSharedCheck_2882_ == 0)
{
v___x_2877_ = v___x_2862_;
v_isShared_2878_ = v_isSharedCheck_2882_;
goto v_resetjp_2876_;
}
else
{
lean_inc(v_a_2875_);
lean_dec(v___x_2862_);
v___x_2877_ = lean_box(0);
v_isShared_2878_ = v_isSharedCheck_2882_;
goto v_resetjp_2876_;
}
v_resetjp_2876_:
{
lean_object* v___x_2880_; 
if (v_isShared_2878_ == 0)
{
v___x_2880_ = v___x_2877_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v_a_2875_);
v___x_2880_ = v_reuseFailAlloc_2881_;
goto v_reusejp_2879_;
}
v_reusejp_2879_:
{
return v___x_2880_;
}
}
}
}
}
else
{
lean_object* v_a_2883_; lean_object* v___x_2885_; uint8_t v_isShared_2886_; uint8_t v_isSharedCheck_2890_; 
lean_dec(v_a_2815_);
lean_dec(v_a_2813_);
lean_dec(v_v_2729_);
lean_dec(v_u_2728_);
v_a_2883_ = lean_ctor_get(v___y_2817_, 0);
v_isSharedCheck_2890_ = !lean_is_exclusive(v___y_2817_);
if (v_isSharedCheck_2890_ == 0)
{
v___x_2885_ = v___y_2817_;
v_isShared_2886_ = v_isSharedCheck_2890_;
goto v_resetjp_2884_;
}
else
{
lean_inc(v_a_2883_);
lean_dec(v___y_2817_);
v___x_2885_ = lean_box(0);
v_isShared_2886_ = v_isSharedCheck_2890_;
goto v_resetjp_2884_;
}
v_resetjp_2884_:
{
lean_object* v___x_2888_; 
if (v_isShared_2886_ == 0)
{
v___x_2888_ = v___x_2885_;
goto v_reusejp_2887_;
}
else
{
lean_object* v_reuseFailAlloc_2889_; 
v_reuseFailAlloc_2889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2889_, 0, v_a_2883_);
v___x_2888_ = v_reuseFailAlloc_2889_;
goto v_reusejp_2887_;
}
v_reusejp_2887_:
{
return v___x_2888_;
}
}
}
}
}
else
{
lean_object* v_a_2895_; lean_object* v___x_2897_; uint8_t v_isShared_2898_; uint8_t v_isSharedCheck_2902_; 
lean_dec(v_a_2813_);
lean_dec(v_v_2729_);
lean_dec(v_u_2728_);
v_a_2895_ = lean_ctor_get(v___x_2814_, 0);
v_isSharedCheck_2902_ = !lean_is_exclusive(v___x_2814_);
if (v_isSharedCheck_2902_ == 0)
{
v___x_2897_ = v___x_2814_;
v_isShared_2898_ = v_isSharedCheck_2902_;
goto v_resetjp_2896_;
}
else
{
lean_inc(v_a_2895_);
lean_dec(v___x_2814_);
v___x_2897_ = lean_box(0);
v_isShared_2898_ = v_isSharedCheck_2902_;
goto v_resetjp_2896_;
}
v_resetjp_2896_:
{
lean_object* v___x_2900_; 
if (v_isShared_2898_ == 0)
{
v___x_2900_ = v___x_2897_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2901_; 
v_reuseFailAlloc_2901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2901_, 0, v_a_2895_);
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
lean_dec(v_v_2729_);
lean_dec(v_u_2728_);
v_a_2903_ = lean_ctor_get(v___x_2812_, 0);
v_isSharedCheck_2910_ = !lean_is_exclusive(v___x_2812_);
if (v_isSharedCheck_2910_ == 0)
{
v___x_2905_ = v___x_2812_;
v_isShared_2906_ = v_isSharedCheck_2910_;
goto v_resetjp_2904_;
}
else
{
lean_inc(v_a_2903_);
lean_dec(v___x_2812_);
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
}
else
{
lean_object* v___x_2911_; lean_object* v___x_2913_; 
lean_dec(v_a_2802_);
lean_dec(v_v_2729_);
lean_dec(v_u_2728_);
v___x_2911_ = lean_box(0);
if (v_isShared_2805_ == 0)
{
lean_ctor_set(v___x_2804_, 0, v___x_2911_);
v___x_2913_ = v___x_2804_;
goto v_reusejp_2912_;
}
else
{
lean_object* v_reuseFailAlloc_2914_; 
v_reuseFailAlloc_2914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2914_, 0, v___x_2911_);
v___x_2913_ = v_reuseFailAlloc_2914_;
goto v_reusejp_2912_;
}
v_reusejp_2912_:
{
return v___x_2913_;
}
}
}
}
else
{
lean_object* v_a_2916_; lean_object* v___x_2918_; uint8_t v_isShared_2919_; uint8_t v_isSharedCheck_2923_; 
lean_dec(v_v_2729_);
lean_dec(v_u_2728_);
v_a_2916_ = lean_ctor_get(v___x_2801_, 0);
v_isSharedCheck_2923_ = !lean_is_exclusive(v___x_2801_);
if (v_isSharedCheck_2923_ == 0)
{
v___x_2918_ = v___x_2801_;
v_isShared_2919_ = v_isSharedCheck_2923_;
goto v_resetjp_2917_;
}
else
{
lean_inc(v_a_2916_);
lean_dec(v___x_2801_);
v___x_2918_ = lean_box(0);
v_isShared_2919_ = v_isSharedCheck_2923_;
goto v_resetjp_2917_;
}
v_resetjp_2917_:
{
lean_object* v___x_2921_; 
if (v_isShared_2919_ == 0)
{
v___x_2921_ = v___x_2918_;
goto v_reusejp_2920_;
}
else
{
lean_object* v_reuseFailAlloc_2922_; 
v_reuseFailAlloc_2922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2922_, 0, v_a_2916_);
v___x_2921_ = v_reuseFailAlloc_2922_;
goto v_reusejp_2920_;
}
v_reusejp_2920_:
{
return v___x_2921_;
}
}
}
}
else
{
lean_dec(v_v_2729_);
lean_dec(v_u_2728_);
goto v___jp_2792_;
}
}
}
v___jp_2792_:
{
lean_object* v___x_2793_; lean_object* v___x_2795_; 
v___x_2793_ = lean_box(0);
if (v_isShared_2791_ == 0)
{
lean_ctor_set(v___x_2790_, 0, v___x_2793_);
v___x_2795_ = v___x_2790_;
goto v_reusejp_2794_;
}
else
{
lean_object* v_reuseFailAlloc_2796_; 
v_reuseFailAlloc_2796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2796_, 0, v___x_2793_);
v___x_2795_ = v_reuseFailAlloc_2796_;
goto v_reusejp_2794_;
}
v_reusejp_2794_:
{
return v___x_2795_;
}
}
}
}
else
{
lean_object* v_a_2925_; lean_object* v___x_2927_; uint8_t v_isShared_2928_; uint8_t v_isSharedCheck_2932_; 
lean_dec(v_v_2729_);
lean_dec(v_u_2728_);
v_a_2925_ = lean_ctor_get(v___x_2787_, 0);
v_isSharedCheck_2932_ = !lean_is_exclusive(v___x_2787_);
if (v_isSharedCheck_2932_ == 0)
{
v___x_2927_ = v___x_2787_;
v_isShared_2928_ = v_isSharedCheck_2932_;
goto v_resetjp_2926_;
}
else
{
lean_inc(v_a_2925_);
lean_dec(v___x_2787_);
v___x_2927_ = lean_box(0);
v_isShared_2928_ = v_isSharedCheck_2932_;
goto v_resetjp_2926_;
}
v_resetjp_2926_:
{
lean_object* v___x_2930_; 
if (v_isShared_2928_ == 0)
{
v___x_2930_ = v___x_2927_;
goto v_reusejp_2929_;
}
else
{
lean_object* v_reuseFailAlloc_2931_; 
v_reuseFailAlloc_2931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2931_, 0, v_a_2925_);
v___x_2930_ = v_reuseFailAlloc_2931_;
goto v_reusejp_2929_;
}
v_reusejp_2929_:
{
return v___x_2930_;
}
}
}
}
else
{
lean_object* v___x_2933_; lean_object* v___x_2934_; 
lean_dec(v_v_2729_);
lean_dec(v_u_2728_);
v___x_2933_ = lean_box(0);
v___x_2934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2934_, 0, v___x_2933_);
return v___x_2934_;
}
v___jp_2743_:
{
if (lean_obj_tag(v___y_2746_) == 0)
{
lean_object* v_a_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2777_; 
v_a_2747_ = lean_ctor_get(v___y_2746_, 0);
v_isSharedCheck_2777_ = !lean_is_exclusive(v___y_2746_);
if (v_isSharedCheck_2777_ == 0)
{
v___x_2749_ = v___y_2746_;
v_isShared_2750_ = v_isSharedCheck_2777_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_a_2747_);
lean_dec(v___y_2746_);
v___x_2749_ = lean_box(0);
v_isShared_2750_ = v_isSharedCheck_2777_;
goto v_resetjp_2748_;
}
v_resetjp_2748_:
{
uint8_t v___x_2751_; 
v___x_2751_ = lean_unbox(v_a_2747_);
lean_dec(v_a_2747_);
if (v___x_2751_ == 0)
{
lean_object* v___x_2752_; lean_object* v___x_2754_; 
lean_dec_ref(v___y_2745_);
lean_dec_ref(v___y_2744_);
lean_dec(v_v_2729_);
lean_dec(v_u_2728_);
v___x_2752_ = lean_box(0);
if (v_isShared_2750_ == 0)
{
lean_ctor_set(v___x_2749_, 0, v___x_2752_);
v___x_2754_ = v___x_2749_;
goto v_reusejp_2753_;
}
else
{
lean_object* v_reuseFailAlloc_2755_; 
v_reuseFailAlloc_2755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2755_, 0, v___x_2752_);
v___x_2754_ = v_reuseFailAlloc_2755_;
goto v_reusejp_2753_;
}
v_reusejp_2753_:
{
return v___x_2754_;
}
}
else
{
lean_object* v___x_2756_; 
lean_del_object(v___x_2749_);
v___x_2756_ = l_Lean_Meta_Grind_isEqv___redArg(v___y_2745_, v___y_2744_, v_a_2732_);
lean_dec_ref(v___y_2744_);
lean_dec_ref(v___y_2745_);
if (lean_obj_tag(v___x_2756_) == 0)
{
lean_object* v_a_2757_; lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2768_; 
v_a_2757_ = lean_ctor_get(v___x_2756_, 0);
v_isSharedCheck_2768_ = !lean_is_exclusive(v___x_2756_);
if (v_isSharedCheck_2768_ == 0)
{
v___x_2759_ = v___x_2756_;
v_isShared_2760_ = v_isSharedCheck_2768_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_a_2757_);
lean_dec(v___x_2756_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2768_;
goto v_resetjp_2758_;
}
v_resetjp_2758_:
{
uint8_t v___x_2761_; 
v___x_2761_ = lean_unbox(v_a_2757_);
lean_dec(v_a_2757_);
if (v___x_2761_ == 0)
{
lean_object* v___x_2762_; lean_object* v___x_2763_; 
lean_del_object(v___x_2759_);
v___x_2762_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2762_, 0, v_u_2728_);
lean_ctor_set(v___x_2762_, 1, v_v_2729_);
v___x_2763_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate(v___x_2762_, v_a_2731_, v_a_2732_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_, v_a_2737_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_);
return v___x_2763_;
}
else
{
lean_object* v___x_2764_; lean_object* v___x_2766_; 
lean_dec(v_v_2729_);
lean_dec(v_u_2728_);
v___x_2764_ = lean_box(0);
if (v_isShared_2760_ == 0)
{
lean_ctor_set(v___x_2759_, 0, v___x_2764_);
v___x_2766_ = v___x_2759_;
goto v_reusejp_2765_;
}
else
{
lean_object* v_reuseFailAlloc_2767_; 
v_reuseFailAlloc_2767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2767_, 0, v___x_2764_);
v___x_2766_ = v_reuseFailAlloc_2767_;
goto v_reusejp_2765_;
}
v_reusejp_2765_:
{
return v___x_2766_;
}
}
}
}
else
{
lean_object* v_a_2769_; lean_object* v___x_2771_; uint8_t v_isShared_2772_; uint8_t v_isSharedCheck_2776_; 
lean_dec(v_v_2729_);
lean_dec(v_u_2728_);
v_a_2769_ = lean_ctor_get(v___x_2756_, 0);
v_isSharedCheck_2776_ = !lean_is_exclusive(v___x_2756_);
if (v_isSharedCheck_2776_ == 0)
{
v___x_2771_ = v___x_2756_;
v_isShared_2772_ = v_isSharedCheck_2776_;
goto v_resetjp_2770_;
}
else
{
lean_inc(v_a_2769_);
lean_dec(v___x_2756_);
v___x_2771_ = lean_box(0);
v_isShared_2772_ = v_isSharedCheck_2776_;
goto v_resetjp_2770_;
}
v_resetjp_2770_:
{
lean_object* v___x_2774_; 
if (v_isShared_2772_ == 0)
{
v___x_2774_ = v___x_2771_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v_a_2769_);
v___x_2774_ = v_reuseFailAlloc_2775_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
return v___x_2774_;
}
}
}
}
}
}
else
{
lean_object* v_a_2778_; lean_object* v___x_2780_; uint8_t v_isShared_2781_; uint8_t v_isSharedCheck_2785_; 
lean_dec_ref(v___y_2745_);
lean_dec_ref(v___y_2744_);
lean_dec(v_v_2729_);
lean_dec(v_u_2728_);
v_a_2778_ = lean_ctor_get(v___y_2746_, 0);
v_isSharedCheck_2785_ = !lean_is_exclusive(v___y_2746_);
if (v_isSharedCheck_2785_ == 0)
{
v___x_2780_ = v___y_2746_;
v_isShared_2781_ = v_isSharedCheck_2785_;
goto v_resetjp_2779_;
}
else
{
lean_inc(v_a_2778_);
lean_dec(v___y_2746_);
v___x_2780_ = lean_box(0);
v_isShared_2781_ = v_isSharedCheck_2785_;
goto v_resetjp_2779_;
}
v_resetjp_2779_:
{
lean_object* v___x_2783_; 
if (v_isShared_2781_ == 0)
{
v___x_2783_ = v___x_2780_;
goto v_reusejp_2782_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2784_, 0, v_a_2778_);
v___x_2783_ = v_reuseFailAlloc_2784_;
goto v_reusejp_2782_;
}
v_reusejp_2782_:
{
return v___x_2783_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq___boxed(lean_object* v_u_2935_, lean_object* v_v_2936_, lean_object* v_k_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_, lean_object* v_a_2943_, lean_object* v_a_2944_, lean_object* v_a_2945_, lean_object* v_a_2946_, lean_object* v_a_2947_, lean_object* v_a_2948_, lean_object* v_a_2949_){
_start:
{
lean_object* v_res_2950_; 
v_res_2950_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq(v_u_2935_, v_v_2936_, v_k_2937_, v_a_2938_, v_a_2939_, v_a_2940_, v_a_2941_, v_a_2942_, v_a_2943_, v_a_2944_, v_a_2945_, v_a_2946_, v_a_2947_, v_a_2948_);
lean_dec(v_a_2948_);
lean_dec_ref(v_a_2947_);
lean_dec(v_a_2946_);
lean_dec_ref(v_a_2945_);
lean_dec(v_a_2944_);
lean_dec_ref(v_a_2943_);
lean_dec(v_a_2942_);
lean_dec_ref(v_a_2941_);
lean_dec(v_a_2940_);
lean_dec(v_a_2939_);
lean_dec(v_a_2938_);
lean_dec_ref(v_k_2937_);
return v_res_2950_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_2951_, lean_object* v_vals_2952_, lean_object* v_i_2953_, lean_object* v_k_2954_){
_start:
{
uint8_t v___y_2956_; lean_object* v___x_2962_; uint8_t v___x_2963_; 
v___x_2962_ = lean_array_get_size(v_keys_2951_);
v___x_2963_ = lean_nat_dec_lt(v_i_2953_, v___x_2962_);
if (v___x_2963_ == 0)
{
lean_object* v___x_2964_; 
lean_dec(v_i_2953_);
v___x_2964_ = lean_box(0);
return v___x_2964_;
}
else
{
lean_object* v_fst_2965_; lean_object* v_snd_2966_; lean_object* v_k_x27_2967_; lean_object* v_fst_2968_; lean_object* v_snd_2969_; uint8_t v___x_2970_; 
v_fst_2965_ = lean_ctor_get(v_k_2954_, 0);
v_snd_2966_ = lean_ctor_get(v_k_2954_, 1);
v_k_x27_2967_ = lean_array_fget_borrowed(v_keys_2951_, v_i_2953_);
v_fst_2968_ = lean_ctor_get(v_k_x27_2967_, 0);
v_snd_2969_ = lean_ctor_get(v_k_x27_2967_, 1);
v___x_2970_ = lean_nat_dec_eq(v_fst_2965_, v_fst_2968_);
if (v___x_2970_ == 0)
{
v___y_2956_ = v___x_2970_;
goto v___jp_2955_;
}
else
{
uint8_t v___x_2971_; 
v___x_2971_ = lean_nat_dec_eq(v_snd_2966_, v_snd_2969_);
v___y_2956_ = v___x_2971_;
goto v___jp_2955_;
}
}
v___jp_2955_:
{
if (v___y_2956_ == 0)
{
lean_object* v___x_2957_; lean_object* v___x_2958_; 
v___x_2957_ = lean_unsigned_to_nat(1u);
v___x_2958_ = lean_nat_add(v_i_2953_, v___x_2957_);
lean_dec(v_i_2953_);
v_i_2953_ = v___x_2958_;
goto _start;
}
else
{
lean_object* v___x_2960_; lean_object* v___x_2961_; 
v___x_2960_ = lean_array_fget_borrowed(v_vals_2952_, v_i_2953_);
lean_dec(v_i_2953_);
lean_inc(v___x_2960_);
v___x_2961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2961_, 0, v___x_2960_);
return v___x_2961_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_2972_, lean_object* v_vals_2973_, lean_object* v_i_2974_, lean_object* v_k_2975_){
_start:
{
lean_object* v_res_2976_; 
v_res_2976_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1___redArg(v_keys_2972_, v_vals_2973_, v_i_2974_, v_k_2975_);
lean_dec_ref(v_k_2975_);
lean_dec_ref(v_vals_2973_);
lean_dec_ref(v_keys_2972_);
return v_res_2976_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0___redArg(lean_object* v_x_2977_, size_t v_x_2978_, lean_object* v_x_2979_){
_start:
{
if (lean_obj_tag(v_x_2977_) == 0)
{
lean_object* v_es_2980_; lean_object* v___x_2981_; size_t v___x_2982_; size_t v___x_2983_; size_t v___x_2984_; lean_object* v_j_2985_; lean_object* v___x_2986_; 
v_es_2980_ = lean_ctor_get(v_x_2977_, 0);
v___x_2981_ = lean_box(2);
v___x_2982_ = ((size_t)5ULL);
v___x_2983_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg___closed__1);
v___x_2984_ = lean_usize_land(v_x_2978_, v___x_2983_);
v_j_2985_ = lean_usize_to_nat(v___x_2984_);
v___x_2986_ = lean_array_get_borrowed(v___x_2981_, v_es_2980_, v_j_2985_);
lean_dec(v_j_2985_);
switch(lean_obj_tag(v___x_2986_))
{
case 0:
{
lean_object* v_key_2987_; lean_object* v_val_2988_; uint8_t v___y_2990_; lean_object* v_fst_2993_; lean_object* v_snd_2994_; lean_object* v_fst_2995_; lean_object* v_snd_2996_; uint8_t v___x_2997_; 
v_key_2987_ = lean_ctor_get(v___x_2986_, 0);
v_val_2988_ = lean_ctor_get(v___x_2986_, 1);
v_fst_2993_ = lean_ctor_get(v_x_2979_, 0);
v_snd_2994_ = lean_ctor_get(v_x_2979_, 1);
v_fst_2995_ = lean_ctor_get(v_key_2987_, 0);
v_snd_2996_ = lean_ctor_get(v_key_2987_, 1);
v___x_2997_ = lean_nat_dec_eq(v_fst_2993_, v_fst_2995_);
if (v___x_2997_ == 0)
{
v___y_2990_ = v___x_2997_;
goto v___jp_2989_;
}
else
{
uint8_t v___x_2998_; 
v___x_2998_ = lean_nat_dec_eq(v_snd_2994_, v_snd_2996_);
v___y_2990_ = v___x_2998_;
goto v___jp_2989_;
}
v___jp_2989_:
{
if (v___y_2990_ == 0)
{
lean_object* v___x_2991_; 
v___x_2991_ = lean_box(0);
return v___x_2991_;
}
else
{
lean_object* v___x_2992_; 
lean_inc(v_val_2988_);
v___x_2992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2992_, 0, v_val_2988_);
return v___x_2992_;
}
}
}
case 1:
{
lean_object* v_node_2999_; size_t v___x_3000_; 
v_node_2999_ = lean_ctor_get(v___x_2986_, 0);
v___x_3000_ = lean_usize_shift_right(v_x_2978_, v___x_2982_);
v_x_2977_ = v_node_2999_;
v_x_2978_ = v___x_3000_;
goto _start;
}
default: 
{
lean_object* v___x_3002_; 
v___x_3002_ = lean_box(0);
return v___x_3002_;
}
}
}
else
{
lean_object* v_ks_3003_; lean_object* v_vs_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; 
v_ks_3003_ = lean_ctor_get(v_x_2977_, 0);
v_vs_3004_ = lean_ctor_get(v_x_2977_, 1);
v___x_3005_ = lean_unsigned_to_nat(0u);
v___x_3006_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1___redArg(v_ks_3003_, v_vs_3004_, v___x_3005_, v_x_2979_);
return v___x_3006_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0___redArg___boxed(lean_object* v_x_3007_, lean_object* v_x_3008_, lean_object* v_x_3009_){
_start:
{
size_t v_x_3958__boxed_3010_; lean_object* v_res_3011_; 
v_x_3958__boxed_3010_ = lean_unbox_usize(v_x_3008_);
lean_dec(v_x_3008_);
v_res_3011_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0___redArg(v_x_3007_, v_x_3958__boxed_3010_, v_x_3009_);
lean_dec_ref(v_x_3009_);
lean_dec_ref(v_x_3007_);
return v_res_3011_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0___redArg(lean_object* v_x_3012_, lean_object* v_x_3013_){
_start:
{
lean_object* v_fst_3014_; lean_object* v_snd_3015_; uint64_t v___x_3016_; uint64_t v___x_3017_; uint64_t v___x_3018_; size_t v___x_3019_; lean_object* v___x_3020_; 
v_fst_3014_ = lean_ctor_get(v_x_3013_, 0);
v_snd_3015_ = lean_ctor_get(v_x_3013_, 1);
v___x_3016_ = lean_uint64_of_nat(v_fst_3014_);
v___x_3017_ = lean_uint64_of_nat(v_snd_3015_);
v___x_3018_ = lean_uint64_mix_hash(v___x_3016_, v___x_3017_);
v___x_3019_ = lean_uint64_to_usize(v___x_3018_);
v___x_3020_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0___redArg(v_x_3012_, v___x_3019_, v_x_3013_);
return v___x_3020_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0___redArg___boxed(lean_object* v_x_3021_, lean_object* v_x_3022_){
_start:
{
lean_object* v_res_3023_; 
v_res_3023_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0___redArg(v_x_3021_, v_x_3022_);
lean_dec_ref(v_x_3022_);
lean_dec_ref(v_x_3021_);
return v_res_3023_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__1(lean_object* v_u_3024_, lean_object* v_v_3025_, lean_object* v_k_3026_, lean_object* v_as_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_){
_start:
{
if (lean_obj_tag(v_as_3027_) == 0)
{
lean_object* v___x_3040_; lean_object* v___x_3041_; 
lean_dec_ref(v_k_3026_);
lean_dec(v_v_3025_);
lean_dec(v_u_3024_);
v___x_3040_ = lean_box(0);
v___x_3041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3041_, 0, v___x_3040_);
return v___x_3041_;
}
else
{
lean_object* v_head_3042_; lean_object* v_tail_3043_; lean_object* v_fst_3044_; lean_object* v_snd_3045_; lean_object* v___x_3046_; 
v_head_3042_ = lean_ctor_get(v_as_3027_, 0);
lean_inc(v_head_3042_);
v_tail_3043_ = lean_ctor_get(v_as_3027_, 1);
lean_inc(v_tail_3043_);
lean_dec_ref(v_as_3027_);
v_fst_3044_ = lean_ctor_get(v_head_3042_, 0);
lean_inc(v_fst_3044_);
v_snd_3045_ = lean_ctor_get(v_head_3042_, 1);
lean_inc(v_snd_3045_);
lean_dec(v_head_3042_);
lean_inc_ref(v_k_3026_);
lean_inc(v_v_3025_);
lean_inc(v_u_3024_);
v___x_3046_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse(v_u_3024_, v_v_3025_, v_k_3026_, v_fst_3044_, v_snd_3045_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_, v___y_3032_, v___y_3033_, v___y_3034_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_);
if (lean_obj_tag(v___x_3046_) == 0)
{
lean_dec_ref(v___x_3046_);
v_as_3027_ = v_tail_3043_;
goto _start;
}
else
{
lean_dec(v_tail_3043_);
lean_dec_ref(v_k_3026_);
lean_dec(v_v_3025_);
lean_dec(v_u_3024_);
return v___x_3046_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__1___boxed(lean_object* v_u_3048_, lean_object* v_v_3049_, lean_object* v_k_3050_, lean_object* v_as_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_){
_start:
{
lean_object* v_res_3064_; 
v_res_3064_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__1(v_u_3048_, v_v_3049_, v_k_3050_, v_as_3051_, v___y_3052_, v___y_3053_, v___y_3054_, v___y_3055_, v___y_3056_, v___y_3057_, v___y_3058_, v___y_3059_, v___y_3060_, v___y_3061_, v___y_3062_);
lean_dec(v___y_3062_);
lean_dec_ref(v___y_3061_);
lean_dec(v___y_3060_);
lean_dec_ref(v___y_3059_);
lean_dec(v___y_3058_);
lean_dec_ref(v___y_3057_);
lean_dec(v___y_3056_);
lean_dec_ref(v___y_3055_);
lean_dec(v___y_3054_);
lean_dec(v___y_3053_);
lean_dec(v___y_3052_);
return v_res_3064_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__2(lean_object* v_u_3065_, lean_object* v_v_3066_, lean_object* v_k_3067_, lean_object* v_as_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_){
_start:
{
if (lean_obj_tag(v_as_3068_) == 0)
{
lean_object* v___x_3081_; lean_object* v___x_3082_; 
lean_dec_ref(v_k_3067_);
lean_dec(v_v_3066_);
lean_dec(v_u_3065_);
v___x_3081_ = lean_box(0);
v___x_3082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3082_, 0, v___x_3081_);
return v___x_3082_;
}
else
{
lean_object* v_head_3083_; lean_object* v_tail_3084_; lean_object* v_fst_3085_; lean_object* v_snd_3086_; lean_object* v___x_3087_; 
v_head_3083_ = lean_ctor_get(v_as_3068_, 0);
lean_inc(v_head_3083_);
v_tail_3084_ = lean_ctor_get(v_as_3068_, 1);
lean_inc(v_tail_3084_);
lean_dec_ref(v_as_3068_);
v_fst_3085_ = lean_ctor_get(v_head_3083_, 0);
lean_inc(v_fst_3085_);
v_snd_3086_ = lean_ctor_get(v_head_3083_, 1);
lean_inc(v_snd_3086_);
lean_dec(v_head_3083_);
lean_inc_ref(v_k_3067_);
lean_inc(v_v_3066_);
lean_inc(v_u_3065_);
v___x_3087_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue(v_u_3065_, v_v_3066_, v_k_3067_, v_fst_3085_, v_snd_3086_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_);
if (lean_obj_tag(v___x_3087_) == 0)
{
lean_dec_ref(v___x_3087_);
v_as_3068_ = v_tail_3084_;
goto _start;
}
else
{
lean_dec(v_tail_3084_);
lean_dec_ref(v_k_3067_);
lean_dec(v_v_3066_);
lean_dec(v_u_3065_);
return v___x_3087_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__2___boxed(lean_object* v_u_3089_, lean_object* v_v_3090_, lean_object* v_k_3091_, lean_object* v_as_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_){
_start:
{
lean_object* v_res_3105_; 
v_res_3105_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__2(v_u_3089_, v_v_3090_, v_k_3091_, v_as_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_, v___y_3103_);
lean_dec(v___y_3103_);
lean_dec_ref(v___y_3102_);
lean_dec(v___y_3101_);
lean_dec_ref(v___y_3100_);
lean_dec(v___y_3099_);
lean_dec_ref(v___y_3098_);
lean_dec(v___y_3097_);
lean_dec_ref(v___y_3096_);
lean_dec(v___y_3095_);
lean_dec(v___y_3094_);
lean_dec(v___y_3093_);
return v_res_3105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate(lean_object* v_u_3106_, lean_object* v_v_3107_, lean_object* v_k_3108_, lean_object* v_a_3109_, lean_object* v_a_3110_, lean_object* v_a_3111_, lean_object* v_a_3112_, lean_object* v_a_3113_, lean_object* v_a_3114_, lean_object* v_a_3115_, lean_object* v_a_3116_, lean_object* v_a_3117_, lean_object* v_a_3118_, lean_object* v_a_3119_){
_start:
{
lean_object* v___x_3139_; 
v___x_3139_ = l_Lean_Meta_Grind_Order_getStruct(v_a_3109_, v_a_3110_, v_a_3111_, v_a_3112_, v_a_3113_, v_a_3114_, v_a_3115_, v_a_3116_, v_a_3117_, v_a_3118_, v_a_3119_);
if (lean_obj_tag(v___x_3139_) == 0)
{
lean_object* v_a_3140_; lean_object* v_cnstrsOf_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; 
v_a_3140_ = lean_ctor_get(v___x_3139_, 0);
lean_inc(v_a_3140_);
lean_dec_ref(v___x_3139_);
v_cnstrsOf_3141_ = lean_ctor_get(v_a_3140_, 17);
lean_inc_ref(v_cnstrsOf_3141_);
lean_dec(v_a_3140_);
lean_inc(v_v_3107_);
lean_inc(v_u_3106_);
v___x_3142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3142_, 0, v_u_3106_);
lean_ctor_set(v___x_3142_, 1, v_v_3107_);
v___x_3143_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0___redArg(v_cnstrsOf_3141_, v___x_3142_);
lean_dec_ref(v___x_3142_);
lean_dec_ref(v_cnstrsOf_3141_);
if (lean_obj_tag(v___x_3143_) == 1)
{
lean_object* v_val_3144_; lean_object* v___x_3145_; 
v_val_3144_ = lean_ctor_get(v___x_3143_, 0);
lean_inc(v_val_3144_);
lean_dec_ref(v___x_3143_);
lean_inc_ref(v_k_3108_);
lean_inc(v_v_3107_);
lean_inc(v_u_3106_);
v___x_3145_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__2(v_u_3106_, v_v_3107_, v_k_3108_, v_val_3144_, v_a_3109_, v_a_3110_, v_a_3111_, v_a_3112_, v_a_3113_, v_a_3114_, v_a_3115_, v_a_3116_, v_a_3117_, v_a_3118_, v_a_3119_);
if (lean_obj_tag(v___x_3145_) == 0)
{
lean_dec_ref(v___x_3145_);
goto v___jp_3121_;
}
else
{
lean_dec_ref(v_k_3108_);
lean_dec(v_v_3107_);
lean_dec(v_u_3106_);
return v___x_3145_;
}
}
else
{
lean_dec(v___x_3143_);
goto v___jp_3121_;
}
}
else
{
lean_object* v_a_3146_; lean_object* v___x_3148_; uint8_t v_isShared_3149_; uint8_t v_isSharedCheck_3153_; 
lean_dec_ref(v_k_3108_);
lean_dec(v_v_3107_);
lean_dec(v_u_3106_);
v_a_3146_ = lean_ctor_get(v___x_3139_, 0);
v_isSharedCheck_3153_ = !lean_is_exclusive(v___x_3139_);
if (v_isSharedCheck_3153_ == 0)
{
v___x_3148_ = v___x_3139_;
v_isShared_3149_ = v_isSharedCheck_3153_;
goto v_resetjp_3147_;
}
else
{
lean_inc(v_a_3146_);
lean_dec(v___x_3139_);
v___x_3148_ = lean_box(0);
v_isShared_3149_ = v_isSharedCheck_3153_;
goto v_resetjp_3147_;
}
v_resetjp_3147_:
{
lean_object* v___x_3151_; 
if (v_isShared_3149_ == 0)
{
v___x_3151_ = v___x_3148_;
goto v_reusejp_3150_;
}
else
{
lean_object* v_reuseFailAlloc_3152_; 
v_reuseFailAlloc_3152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3152_, 0, v_a_3146_);
v___x_3151_ = v_reuseFailAlloc_3152_;
goto v_reusejp_3150_;
}
v_reusejp_3150_:
{
return v___x_3151_;
}
}
}
v___jp_3121_:
{
lean_object* v___x_3122_; 
v___x_3122_ = l_Lean_Meta_Grind_Order_getStruct(v_a_3109_, v_a_3110_, v_a_3111_, v_a_3112_, v_a_3113_, v_a_3114_, v_a_3115_, v_a_3116_, v_a_3117_, v_a_3118_, v_a_3119_);
if (lean_obj_tag(v___x_3122_) == 0)
{
lean_object* v_a_3123_; lean_object* v_cnstrsOf_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; 
v_a_3123_ = lean_ctor_get(v___x_3122_, 0);
lean_inc(v_a_3123_);
lean_dec_ref(v___x_3122_);
v_cnstrsOf_3124_ = lean_ctor_get(v_a_3123_, 17);
lean_inc_ref(v_cnstrsOf_3124_);
lean_dec(v_a_3123_);
lean_inc(v_u_3106_);
lean_inc(v_v_3107_);
v___x_3125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3125_, 0, v_v_3107_);
lean_ctor_set(v___x_3125_, 1, v_u_3106_);
v___x_3126_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0___redArg(v_cnstrsOf_3124_, v___x_3125_);
lean_dec_ref(v___x_3125_);
lean_dec_ref(v_cnstrsOf_3124_);
if (lean_obj_tag(v___x_3126_) == 1)
{
lean_object* v_val_3127_; lean_object* v___x_3128_; 
v_val_3127_ = lean_ctor_get(v___x_3126_, 0);
lean_inc(v_val_3127_);
lean_dec_ref(v___x_3126_);
lean_inc_ref(v_k_3108_);
lean_inc(v_v_3107_);
lean_inc(v_u_3106_);
v___x_3128_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__1(v_u_3106_, v_v_3107_, v_k_3108_, v_val_3127_, v_a_3109_, v_a_3110_, v_a_3111_, v_a_3112_, v_a_3113_, v_a_3114_, v_a_3115_, v_a_3116_, v_a_3117_, v_a_3118_, v_a_3119_);
if (lean_obj_tag(v___x_3128_) == 0)
{
lean_object* v___x_3129_; 
lean_dec_ref(v___x_3128_);
v___x_3129_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq(v_u_3106_, v_v_3107_, v_k_3108_, v_a_3109_, v_a_3110_, v_a_3111_, v_a_3112_, v_a_3113_, v_a_3114_, v_a_3115_, v_a_3116_, v_a_3117_, v_a_3118_, v_a_3119_);
lean_dec_ref(v_k_3108_);
return v___x_3129_;
}
else
{
lean_dec_ref(v_k_3108_);
lean_dec(v_v_3107_);
lean_dec(v_u_3106_);
return v___x_3128_;
}
}
else
{
lean_object* v___x_3130_; 
lean_dec(v___x_3126_);
v___x_3130_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq(v_u_3106_, v_v_3107_, v_k_3108_, v_a_3109_, v_a_3110_, v_a_3111_, v_a_3112_, v_a_3113_, v_a_3114_, v_a_3115_, v_a_3116_, v_a_3117_, v_a_3118_, v_a_3119_);
lean_dec_ref(v_k_3108_);
return v___x_3130_;
}
}
else
{
lean_object* v_a_3131_; lean_object* v___x_3133_; uint8_t v_isShared_3134_; uint8_t v_isSharedCheck_3138_; 
lean_dec_ref(v_k_3108_);
lean_dec(v_v_3107_);
lean_dec(v_u_3106_);
v_a_3131_ = lean_ctor_get(v___x_3122_, 0);
v_isSharedCheck_3138_ = !lean_is_exclusive(v___x_3122_);
if (v_isSharedCheck_3138_ == 0)
{
v___x_3133_ = v___x_3122_;
v_isShared_3134_ = v_isSharedCheck_3138_;
goto v_resetjp_3132_;
}
else
{
lean_inc(v_a_3131_);
lean_dec(v___x_3122_);
v___x_3133_ = lean_box(0);
v_isShared_3134_ = v_isSharedCheck_3138_;
goto v_resetjp_3132_;
}
v_resetjp_3132_:
{
lean_object* v___x_3136_; 
if (v_isShared_3134_ == 0)
{
v___x_3136_ = v___x_3133_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3137_; 
v_reuseFailAlloc_3137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3137_, 0, v_a_3131_);
v___x_3136_ = v_reuseFailAlloc_3137_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
return v___x_3136_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate___boxed(lean_object* v_u_3154_, lean_object* v_v_3155_, lean_object* v_k_3156_, lean_object* v_a_3157_, lean_object* v_a_3158_, lean_object* v_a_3159_, lean_object* v_a_3160_, lean_object* v_a_3161_, lean_object* v_a_3162_, lean_object* v_a_3163_, lean_object* v_a_3164_, lean_object* v_a_3165_, lean_object* v_a_3166_, lean_object* v_a_3167_, lean_object* v_a_3168_){
_start:
{
lean_object* v_res_3169_; 
v_res_3169_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate(v_u_3154_, v_v_3155_, v_k_3156_, v_a_3157_, v_a_3158_, v_a_3159_, v_a_3160_, v_a_3161_, v_a_3162_, v_a_3163_, v_a_3164_, v_a_3165_, v_a_3166_, v_a_3167_);
lean_dec(v_a_3167_);
lean_dec_ref(v_a_3166_);
lean_dec(v_a_3165_);
lean_dec_ref(v_a_3164_);
lean_dec(v_a_3163_);
lean_dec_ref(v_a_3162_);
lean_dec(v_a_3161_);
lean_dec_ref(v_a_3160_);
lean_dec(v_a_3159_);
lean_dec(v_a_3158_);
lean_dec(v_a_3157_);
return v_res_3169_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0(lean_object* v_00_u03b2_3170_, lean_object* v_x_3171_, lean_object* v_x_3172_){
_start:
{
lean_object* v___x_3173_; 
v___x_3173_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0___redArg(v_x_3171_, v_x_3172_);
return v___x_3173_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0___boxed(lean_object* v_00_u03b2_3174_, lean_object* v_x_3175_, lean_object* v_x_3176_){
_start:
{
lean_object* v_res_3177_; 
v_res_3177_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0(v_00_u03b2_3174_, v_x_3175_, v_x_3176_);
lean_dec_ref(v_x_3176_);
lean_dec_ref(v_x_3175_);
return v_res_3177_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0(lean_object* v_00_u03b2_3178_, lean_object* v_x_3179_, size_t v_x_3180_, lean_object* v_x_3181_){
_start:
{
lean_object* v___x_3182_; 
v___x_3182_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0___redArg(v_x_3179_, v_x_3180_, v_x_3181_);
return v___x_3182_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3183_, lean_object* v_x_3184_, lean_object* v_x_3185_, lean_object* v_x_3186_){
_start:
{
size_t v_x_4226__boxed_3187_; lean_object* v_res_3188_; 
v_x_4226__boxed_3187_ = lean_unbox_usize(v_x_3185_);
lean_dec(v_x_3185_);
v_res_3188_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0(v_00_u03b2_3183_, v_x_3184_, v_x_4226__boxed_3187_, v_x_3186_);
lean_dec_ref(v_x_3186_);
lean_dec_ref(v_x_3184_);
return v_res_3188_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3189_, lean_object* v_keys_3190_, lean_object* v_vals_3191_, lean_object* v_heq_3192_, lean_object* v_i_3193_, lean_object* v_k_3194_){
_start:
{
lean_object* v___x_3195_; 
v___x_3195_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1___redArg(v_keys_3190_, v_vals_3191_, v_i_3193_, v_k_3194_);
return v___x_3195_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_3196_, lean_object* v_keys_3197_, lean_object* v_vals_3198_, lean_object* v_heq_3199_, lean_object* v_i_3200_, lean_object* v_k_3201_){
_start:
{
lean_object* v_res_3202_; 
v_res_3202_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1(v_00_u03b2_3196_, v_keys_3197_, v_vals_3198_, v_heq_3199_, v_i_3200_, v_k_3201_);
lean_dec_ref(v_k_3201_);
lean_dec_ref(v_vals_3198_);
lean_dec_ref(v_keys_3197_);
return v_res_3202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_updateIfShorter(lean_object* v_u_3203_, lean_object* v_v_3204_, lean_object* v_k_3205_, lean_object* v_w_3206_, lean_object* v_a_3207_, lean_object* v_a_3208_, lean_object* v_a_3209_, lean_object* v_a_3210_, lean_object* v_a_3211_, lean_object* v_a_3212_, lean_object* v_a_3213_, lean_object* v_a_3214_, lean_object* v_a_3215_, lean_object* v_a_3216_, lean_object* v_a_3217_){
_start:
{
lean_object* v___x_3219_; 
v___x_3219_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isShorter(v_u_3203_, v_v_3204_, v_k_3205_, v_a_3207_, v_a_3208_, v_a_3209_, v_a_3210_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_, v_a_3217_);
if (lean_obj_tag(v___x_3219_) == 0)
{
lean_object* v_a_3220_; lean_object* v___x_3222_; uint8_t v_isShared_3223_; uint8_t v_isSharedCheck_3242_; 
v_a_3220_ = lean_ctor_get(v___x_3219_, 0);
v_isSharedCheck_3242_ = !lean_is_exclusive(v___x_3219_);
if (v_isSharedCheck_3242_ == 0)
{
v___x_3222_ = v___x_3219_;
v_isShared_3223_ = v_isSharedCheck_3242_;
goto v_resetjp_3221_;
}
else
{
lean_inc(v_a_3220_);
lean_dec(v___x_3219_);
v___x_3222_ = lean_box(0);
v_isShared_3223_ = v_isSharedCheck_3242_;
goto v_resetjp_3221_;
}
v_resetjp_3221_:
{
uint8_t v___x_3224_; 
v___x_3224_ = lean_unbox(v_a_3220_);
lean_dec(v_a_3220_);
if (v___x_3224_ == 0)
{
lean_object* v___x_3225_; lean_object* v___x_3227_; 
lean_dec_ref(v_k_3205_);
lean_dec(v_v_3204_);
lean_dec(v_u_3203_);
v___x_3225_ = lean_box(0);
if (v_isShared_3223_ == 0)
{
lean_ctor_set(v___x_3222_, 0, v___x_3225_);
v___x_3227_ = v___x_3222_;
goto v_reusejp_3226_;
}
else
{
lean_object* v_reuseFailAlloc_3228_; 
v_reuseFailAlloc_3228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3228_, 0, v___x_3225_);
v___x_3227_ = v_reuseFailAlloc_3228_;
goto v_reusejp_3226_;
}
v_reusejp_3226_:
{
return v___x_3227_;
}
}
else
{
lean_object* v___x_3229_; 
lean_del_object(v___x_3222_);
lean_inc_ref(v_k_3205_);
lean_inc(v_v_3204_);
lean_inc(v_u_3203_);
v___x_3229_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist___redArg(v_u_3203_, v_v_3204_, v_k_3205_, v_a_3207_, v_a_3208_);
if (lean_obj_tag(v___x_3229_) == 0)
{
lean_object* v___x_3230_; 
lean_dec_ref(v___x_3229_);
v___x_3230_ = l_Lean_Meta_Grind_Order_getProof(v_w_3206_, v_v_3204_, v_a_3207_, v_a_3208_, v_a_3209_, v_a_3210_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_, v_a_3217_);
if (lean_obj_tag(v___x_3230_) == 0)
{
lean_object* v_a_3231_; lean_object* v___x_3232_; 
v_a_3231_ = lean_ctor_get(v___x_3230_, 0);
lean_inc(v_a_3231_);
lean_dec_ref(v___x_3230_);
lean_inc(v_v_3204_);
lean_inc(v_u_3203_);
v___x_3232_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___redArg(v_u_3203_, v_v_3204_, v_a_3231_, v_a_3207_, v_a_3208_);
if (lean_obj_tag(v___x_3232_) == 0)
{
lean_object* v___x_3233_; 
lean_dec_ref(v___x_3232_);
v___x_3233_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate(v_u_3203_, v_v_3204_, v_k_3205_, v_a_3207_, v_a_3208_, v_a_3209_, v_a_3210_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_, v_a_3217_);
return v___x_3233_;
}
else
{
lean_dec_ref(v_k_3205_);
lean_dec(v_v_3204_);
lean_dec(v_u_3203_);
return v___x_3232_;
}
}
else
{
lean_object* v_a_3234_; lean_object* v___x_3236_; uint8_t v_isShared_3237_; uint8_t v_isSharedCheck_3241_; 
lean_dec_ref(v_k_3205_);
lean_dec(v_v_3204_);
lean_dec(v_u_3203_);
v_a_3234_ = lean_ctor_get(v___x_3230_, 0);
v_isSharedCheck_3241_ = !lean_is_exclusive(v___x_3230_);
if (v_isSharedCheck_3241_ == 0)
{
v___x_3236_ = v___x_3230_;
v_isShared_3237_ = v_isSharedCheck_3241_;
goto v_resetjp_3235_;
}
else
{
lean_inc(v_a_3234_);
lean_dec(v___x_3230_);
v___x_3236_ = lean_box(0);
v_isShared_3237_ = v_isSharedCheck_3241_;
goto v_resetjp_3235_;
}
v_resetjp_3235_:
{
lean_object* v___x_3239_; 
if (v_isShared_3237_ == 0)
{
v___x_3239_ = v___x_3236_;
goto v_reusejp_3238_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v_a_3234_);
v___x_3239_ = v_reuseFailAlloc_3240_;
goto v_reusejp_3238_;
}
v_reusejp_3238_:
{
return v___x_3239_;
}
}
}
}
else
{
lean_dec_ref(v_k_3205_);
lean_dec(v_v_3204_);
lean_dec(v_u_3203_);
return v___x_3229_;
}
}
}
}
else
{
lean_object* v_a_3243_; lean_object* v___x_3245_; uint8_t v_isShared_3246_; uint8_t v_isSharedCheck_3250_; 
lean_dec_ref(v_k_3205_);
lean_dec(v_v_3204_);
lean_dec(v_u_3203_);
v_a_3243_ = lean_ctor_get(v___x_3219_, 0);
v_isSharedCheck_3250_ = !lean_is_exclusive(v___x_3219_);
if (v_isSharedCheck_3250_ == 0)
{
v___x_3245_ = v___x_3219_;
v_isShared_3246_ = v_isSharedCheck_3250_;
goto v_resetjp_3244_;
}
else
{
lean_inc(v_a_3243_);
lean_dec(v___x_3219_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_updateIfShorter___boxed(lean_object* v_u_3251_, lean_object* v_v_3252_, lean_object* v_k_3253_, lean_object* v_w_3254_, lean_object* v_a_3255_, lean_object* v_a_3256_, lean_object* v_a_3257_, lean_object* v_a_3258_, lean_object* v_a_3259_, lean_object* v_a_3260_, lean_object* v_a_3261_, lean_object* v_a_3262_, lean_object* v_a_3263_, lean_object* v_a_3264_, lean_object* v_a_3265_, lean_object* v_a_3266_){
_start:
{
lean_object* v_res_3267_; 
v_res_3267_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_updateIfShorter(v_u_3251_, v_v_3252_, v_k_3253_, v_w_3254_, v_a_3255_, v_a_3256_, v_a_3257_, v_a_3258_, v_a_3259_, v_a_3260_, v_a_3261_, v_a_3262_, v_a_3263_, v_a_3264_, v_a_3265_);
lean_dec(v_a_3265_);
lean_dec_ref(v_a_3264_);
lean_dec(v_a_3263_);
lean_dec_ref(v_a_3262_);
lean_dec(v_a_3261_);
lean_dec_ref(v_a_3260_);
lean_dec(v_a_3259_);
lean_dec_ref(v_a_3258_);
lean_dec(v_a_3257_);
lean_dec(v_a_3256_);
lean_dec(v_a_3255_);
lean_dec(v_w_3254_);
return v_res_3267_;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0(lean_object* v___x_3268_, lean_object* v_i_3269_, lean_object* v_v_3270_, lean_object* v_x_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_){
_start:
{
if (lean_obj_tag(v_x_3271_) == 0)
{
lean_object* v___x_3284_; lean_object* v___x_3285_; 
lean_dec(v_i_3269_);
v___x_3284_ = lean_box(0);
v___x_3285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3285_, 0, v___x_3284_);
return v___x_3285_;
}
else
{
lean_object* v_key_3286_; lean_object* v_value_3287_; lean_object* v_tail_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; 
v_key_3286_ = lean_ctor_get(v_x_3271_, 0);
lean_inc(v_key_3286_);
v_value_3287_ = lean_ctor_get(v_x_3271_, 1);
lean_inc(v_value_3287_);
v_tail_3288_ = lean_ctor_get(v_x_3271_, 2);
lean_inc(v_tail_3288_);
lean_dec_ref(v_x_3271_);
v___x_3289_ = l_Lean_Meta_Grind_Order_Weight_add(v___x_3268_, v_value_3287_);
lean_inc(v_i_3269_);
v___x_3290_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_updateIfShorter(v_i_3269_, v_key_3286_, v___x_3289_, v_v_3270_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_);
if (lean_obj_tag(v___x_3290_) == 0)
{
lean_dec_ref(v___x_3290_);
v_x_3271_ = v_tail_3288_;
goto _start;
}
else
{
lean_dec(v_tail_3288_);
lean_dec(v_i_3269_);
return v___x_3290_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0___boxed(lean_object* v___x_3292_, lean_object* v_i_3293_, lean_object* v_v_3294_, lean_object* v_x_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_){
_start:
{
lean_object* v_res_3308_; 
v_res_3308_ = l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0(v___x_3292_, v_i_3293_, v_v_3294_, v_x_3295_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_);
lean_dec(v___y_3306_);
lean_dec_ref(v___y_3305_);
lean_dec(v___y_3304_);
lean_dec_ref(v___y_3303_);
lean_dec(v___y_3302_);
lean_dec_ref(v___y_3301_);
lean_dec(v___y_3300_);
lean_dec_ref(v___y_3299_);
lean_dec(v___y_3298_);
lean_dec(v___y_3297_);
lean_dec(v___y_3296_);
lean_dec(v_v_3294_);
lean_dec_ref(v___x_3292_);
return v_res_3308_;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__1(lean_object* v_k_3309_, lean_object* v_v_3310_, lean_object* v_u_3311_, lean_object* v_x_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_){
_start:
{
if (lean_obj_tag(v_x_3312_) == 0)
{
lean_object* v___x_3325_; lean_object* v___x_3326_; 
lean_dec(v_v_3310_);
lean_dec_ref(v_k_3309_);
v___x_3325_ = lean_box(0);
v___x_3326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3326_, 0, v___x_3325_);
return v___x_3326_;
}
else
{
lean_object* v_key_3327_; lean_object* v_value_3328_; lean_object* v_tail_3329_; lean_object* v___y_3331_; lean_object* v___x_3333_; lean_object* v___x_3334_; 
v_key_3327_ = lean_ctor_get(v_x_3312_, 0);
lean_inc_n(v_key_3327_, 2);
v_value_3328_ = lean_ctor_get(v_x_3312_, 1);
lean_inc(v_value_3328_);
v_tail_3329_ = lean_ctor_get(v_x_3312_, 2);
lean_inc(v_tail_3329_);
lean_dec_ref(v_x_3312_);
lean_inc_ref(v_k_3309_);
v___x_3333_ = l_Lean_Meta_Grind_Order_Weight_add(v_value_3328_, v_k_3309_);
lean_dec(v_value_3328_);
lean_inc_ref(v___x_3333_);
lean_inc(v_v_3310_);
v___x_3334_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_updateIfShorter(v_key_3327_, v_v_3310_, v___x_3333_, v_u_3311_, v___y_3313_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_);
if (lean_obj_tag(v___x_3334_) == 0)
{
lean_object* v___x_3335_; 
lean_dec_ref(v___x_3334_);
v___x_3335_ = l_Lean_Meta_Grind_Order_getStruct(v___y_3313_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_);
if (lean_obj_tag(v___x_3335_) == 0)
{
lean_object* v_a_3336_; lean_object* v_targets_3337_; lean_object* v_size_3338_; lean_object* v___x_3339_; uint8_t v___x_3340_; 
v_a_3336_ = lean_ctor_get(v___x_3335_, 0);
lean_inc(v_a_3336_);
lean_dec_ref(v___x_3335_);
v_targets_3337_ = lean_ctor_get(v_a_3336_, 19);
lean_inc_ref(v_targets_3337_);
lean_dec(v_a_3336_);
v_size_3338_ = lean_ctor_get(v_targets_3337_, 2);
v___x_3339_ = lean_box(0);
v___x_3340_ = lean_nat_dec_lt(v_v_3310_, v_size_3338_);
if (v___x_3340_ == 0)
{
lean_object* v___x_3341_; lean_object* v___x_3342_; 
lean_dec_ref(v_targets_3337_);
v___x_3341_ = l_outOfBounds___redArg(v___x_3339_);
v___x_3342_ = l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0(v___x_3333_, v_key_3327_, v_v_3310_, v___x_3341_, v___y_3313_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_);
lean_dec_ref(v___x_3333_);
v___y_3331_ = v___x_3342_;
goto v___jp_3330_;
}
else
{
lean_object* v___x_3343_; lean_object* v___x_3344_; 
v___x_3343_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3339_, v_targets_3337_, v_v_3310_);
lean_dec_ref(v_targets_3337_);
v___x_3344_ = l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0(v___x_3333_, v_key_3327_, v_v_3310_, v___x_3343_, v___y_3313_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_);
lean_dec_ref(v___x_3333_);
v___y_3331_ = v___x_3344_;
goto v___jp_3330_;
}
}
else
{
lean_object* v_a_3345_; lean_object* v___x_3347_; uint8_t v_isShared_3348_; uint8_t v_isSharedCheck_3352_; 
lean_dec_ref(v___x_3333_);
lean_dec(v_tail_3329_);
lean_dec(v_key_3327_);
lean_dec(v_v_3310_);
lean_dec_ref(v_k_3309_);
v_a_3345_ = lean_ctor_get(v___x_3335_, 0);
v_isSharedCheck_3352_ = !lean_is_exclusive(v___x_3335_);
if (v_isSharedCheck_3352_ == 0)
{
v___x_3347_ = v___x_3335_;
v_isShared_3348_ = v_isSharedCheck_3352_;
goto v_resetjp_3346_;
}
else
{
lean_inc(v_a_3345_);
lean_dec(v___x_3335_);
v___x_3347_ = lean_box(0);
v_isShared_3348_ = v_isSharedCheck_3352_;
goto v_resetjp_3346_;
}
v_resetjp_3346_:
{
lean_object* v___x_3350_; 
if (v_isShared_3348_ == 0)
{
v___x_3350_ = v___x_3347_;
goto v_reusejp_3349_;
}
else
{
lean_object* v_reuseFailAlloc_3351_; 
v_reuseFailAlloc_3351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3351_, 0, v_a_3345_);
v___x_3350_ = v_reuseFailAlloc_3351_;
goto v_reusejp_3349_;
}
v_reusejp_3349_:
{
return v___x_3350_;
}
}
}
}
else
{
lean_dec_ref(v___x_3333_);
lean_dec(v_key_3327_);
v___y_3331_ = v___x_3334_;
goto v___jp_3330_;
}
v___jp_3330_:
{
if (lean_obj_tag(v___y_3331_) == 0)
{
lean_dec_ref(v___y_3331_);
v_x_3312_ = v_tail_3329_;
goto _start;
}
else
{
lean_dec(v_tail_3329_);
lean_dec(v_v_3310_);
lean_dec_ref(v_k_3309_);
return v___y_3331_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__1___boxed(lean_object* v_k_3353_, lean_object* v_v_3354_, lean_object* v_u_3355_, lean_object* v_x_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_){
_start:
{
lean_object* v_res_3369_; 
v_res_3369_ = l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__1(v_k_3353_, v_v_3354_, v_u_3355_, v_x_3356_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_, v___y_3367_);
lean_dec(v___y_3367_);
lean_dec_ref(v___y_3366_);
lean_dec(v___y_3365_);
lean_dec_ref(v___y_3364_);
lean_dec(v___y_3363_);
lean_dec_ref(v___y_3362_);
lean_dec(v___y_3361_);
lean_dec_ref(v___y_3360_);
lean_dec(v___y_3359_);
lean_dec(v___y_3358_);
lean_dec(v___y_3357_);
lean_dec(v_u_3355_);
return v_res_3369_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update(lean_object* v_u_3370_, lean_object* v_v_3371_, lean_object* v_k_3372_, lean_object* v_a_3373_, lean_object* v_a_3374_, lean_object* v_a_3375_, lean_object* v_a_3376_, lean_object* v_a_3377_, lean_object* v_a_3378_, lean_object* v_a_3379_, lean_object* v_a_3380_, lean_object* v_a_3381_, lean_object* v_a_3382_, lean_object* v_a_3383_){
_start:
{
lean_object* v___y_3386_; lean_object* v___x_3405_; 
v___x_3405_ = l_Lean_Meta_Grind_Order_getStruct(v_a_3373_, v_a_3374_, v_a_3375_, v_a_3376_, v_a_3377_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_);
if (lean_obj_tag(v___x_3405_) == 0)
{
lean_object* v_a_3406_; lean_object* v_targets_3407_; lean_object* v_size_3408_; lean_object* v___x_3409_; uint8_t v___x_3410_; 
v_a_3406_ = lean_ctor_get(v___x_3405_, 0);
lean_inc(v_a_3406_);
lean_dec_ref(v___x_3405_);
v_targets_3407_ = lean_ctor_get(v_a_3406_, 19);
lean_inc_ref(v_targets_3407_);
lean_dec(v_a_3406_);
v_size_3408_ = lean_ctor_get(v_targets_3407_, 2);
v___x_3409_ = lean_box(0);
v___x_3410_ = lean_nat_dec_lt(v_v_3371_, v_size_3408_);
if (v___x_3410_ == 0)
{
lean_object* v___x_3411_; lean_object* v___x_3412_; 
lean_dec_ref(v_targets_3407_);
v___x_3411_ = l_outOfBounds___redArg(v___x_3409_);
lean_inc(v_u_3370_);
v___x_3412_ = l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0(v_k_3372_, v_u_3370_, v_v_3371_, v___x_3411_, v_a_3373_, v_a_3374_, v_a_3375_, v_a_3376_, v_a_3377_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_);
v___y_3386_ = v___x_3412_;
goto v___jp_3385_;
}
else
{
lean_object* v___x_3413_; lean_object* v___x_3414_; 
v___x_3413_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3409_, v_targets_3407_, v_v_3371_);
lean_dec_ref(v_targets_3407_);
lean_inc(v_u_3370_);
v___x_3414_ = l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0(v_k_3372_, v_u_3370_, v_v_3371_, v___x_3413_, v_a_3373_, v_a_3374_, v_a_3375_, v_a_3376_, v_a_3377_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_);
v___y_3386_ = v___x_3414_;
goto v___jp_3385_;
}
}
else
{
lean_object* v_a_3415_; lean_object* v___x_3417_; uint8_t v_isShared_3418_; uint8_t v_isSharedCheck_3422_; 
lean_dec_ref(v_k_3372_);
lean_dec(v_v_3371_);
lean_dec(v_u_3370_);
v_a_3415_ = lean_ctor_get(v___x_3405_, 0);
v_isSharedCheck_3422_ = !lean_is_exclusive(v___x_3405_);
if (v_isSharedCheck_3422_ == 0)
{
v___x_3417_ = v___x_3405_;
v_isShared_3418_ = v_isSharedCheck_3422_;
goto v_resetjp_3416_;
}
else
{
lean_inc(v_a_3415_);
lean_dec(v___x_3405_);
v___x_3417_ = lean_box(0);
v_isShared_3418_ = v_isSharedCheck_3422_;
goto v_resetjp_3416_;
}
v_resetjp_3416_:
{
lean_object* v___x_3420_; 
if (v_isShared_3418_ == 0)
{
v___x_3420_ = v___x_3417_;
goto v_reusejp_3419_;
}
else
{
lean_object* v_reuseFailAlloc_3421_; 
v_reuseFailAlloc_3421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3421_, 0, v_a_3415_);
v___x_3420_ = v_reuseFailAlloc_3421_;
goto v_reusejp_3419_;
}
v_reusejp_3419_:
{
return v___x_3420_;
}
}
}
v___jp_3385_:
{
if (lean_obj_tag(v___y_3386_) == 0)
{
lean_object* v___x_3387_; 
lean_dec_ref(v___y_3386_);
v___x_3387_ = l_Lean_Meta_Grind_Order_getStruct(v_a_3373_, v_a_3374_, v_a_3375_, v_a_3376_, v_a_3377_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_);
if (lean_obj_tag(v___x_3387_) == 0)
{
lean_object* v_a_3388_; lean_object* v_sources_3389_; lean_object* v_size_3390_; lean_object* v___x_3391_; uint8_t v___x_3392_; 
v_a_3388_ = lean_ctor_get(v___x_3387_, 0);
lean_inc(v_a_3388_);
lean_dec_ref(v___x_3387_);
v_sources_3389_ = lean_ctor_get(v_a_3388_, 18);
lean_inc_ref(v_sources_3389_);
lean_dec(v_a_3388_);
v_size_3390_ = lean_ctor_get(v_sources_3389_, 2);
v___x_3391_ = lean_box(0);
v___x_3392_ = lean_nat_dec_lt(v_u_3370_, v_size_3390_);
if (v___x_3392_ == 0)
{
lean_object* v___x_3393_; lean_object* v___x_3394_; 
lean_dec_ref(v_sources_3389_);
v___x_3393_ = l_outOfBounds___redArg(v___x_3391_);
v___x_3394_ = l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__1(v_k_3372_, v_v_3371_, v_u_3370_, v___x_3393_, v_a_3373_, v_a_3374_, v_a_3375_, v_a_3376_, v_a_3377_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_);
lean_dec(v_u_3370_);
return v___x_3394_;
}
else
{
lean_object* v___x_3395_; lean_object* v___x_3396_; 
v___x_3395_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3391_, v_sources_3389_, v_u_3370_);
lean_dec_ref(v_sources_3389_);
v___x_3396_ = l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__1(v_k_3372_, v_v_3371_, v_u_3370_, v___x_3395_, v_a_3373_, v_a_3374_, v_a_3375_, v_a_3376_, v_a_3377_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_);
lean_dec(v_u_3370_);
return v___x_3396_;
}
}
else
{
lean_object* v_a_3397_; lean_object* v___x_3399_; uint8_t v_isShared_3400_; uint8_t v_isSharedCheck_3404_; 
lean_dec_ref(v_k_3372_);
lean_dec(v_v_3371_);
lean_dec(v_u_3370_);
v_a_3397_ = lean_ctor_get(v___x_3387_, 0);
v_isSharedCheck_3404_ = !lean_is_exclusive(v___x_3387_);
if (v_isSharedCheck_3404_ == 0)
{
v___x_3399_ = v___x_3387_;
v_isShared_3400_ = v_isSharedCheck_3404_;
goto v_resetjp_3398_;
}
else
{
lean_inc(v_a_3397_);
lean_dec(v___x_3387_);
v___x_3399_ = lean_box(0);
v_isShared_3400_ = v_isSharedCheck_3404_;
goto v_resetjp_3398_;
}
v_resetjp_3398_:
{
lean_object* v___x_3402_; 
if (v_isShared_3400_ == 0)
{
v___x_3402_ = v___x_3399_;
goto v_reusejp_3401_;
}
else
{
lean_object* v_reuseFailAlloc_3403_; 
v_reuseFailAlloc_3403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3403_, 0, v_a_3397_);
v___x_3402_ = v_reuseFailAlloc_3403_;
goto v_reusejp_3401_;
}
v_reusejp_3401_:
{
return v___x_3402_;
}
}
}
}
else
{
lean_dec_ref(v_k_3372_);
lean_dec(v_v_3371_);
lean_dec(v_u_3370_);
return v___y_3386_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update___boxed(lean_object* v_u_3423_, lean_object* v_v_3424_, lean_object* v_k_3425_, lean_object* v_a_3426_, lean_object* v_a_3427_, lean_object* v_a_3428_, lean_object* v_a_3429_, lean_object* v_a_3430_, lean_object* v_a_3431_, lean_object* v_a_3432_, lean_object* v_a_3433_, lean_object* v_a_3434_, lean_object* v_a_3435_, lean_object* v_a_3436_, lean_object* v_a_3437_){
_start:
{
lean_object* v_res_3438_; 
v_res_3438_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update(v_u_3423_, v_v_3424_, v_k_3425_, v_a_3426_, v_a_3427_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_, v_a_3435_, v_a_3436_);
lean_dec(v_a_3436_);
lean_dec_ref(v_a_3435_);
lean_dec(v_a_3434_);
lean_dec_ref(v_a_3433_);
lean_dec(v_a_3432_);
lean_dec_ref(v_a_3431_);
lean_dec(v_a_3430_);
lean_dec_ref(v_a_3429_);
lean_dec(v_a_3428_);
lean_dec(v_a_3427_);
lean_dec(v_a_3426_);
return v_res_3438_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_addEdge___closed__2(void){
_start:
{
lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; 
v___x_3445_ = ((lean_object*)(l_Lean_Meta_Grind_Order_addEdge___closed__1));
v___x_3446_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__6));
v___x_3447_ = l_Lean_Name_append(v___x_3446_, v___x_3445_);
return v___x_3447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_addEdge(lean_object* v_u_3448_, lean_object* v_v_3449_, lean_object* v_k_3450_, lean_object* v_h_3451_, lean_object* v_a_3452_, lean_object* v_a_3453_, lean_object* v_a_3454_, lean_object* v_a_3455_, lean_object* v_a_3456_, lean_object* v_a_3457_, lean_object* v_a_3458_, lean_object* v_a_3459_, lean_object* v_a_3460_, lean_object* v_a_3461_, lean_object* v_a_3462_){
_start:
{
lean_object* v___y_3465_; lean_object* v___y_3466_; lean_object* v___y_3467_; lean_object* v___y_3468_; lean_object* v___y_3469_; lean_object* v___y_3470_; lean_object* v___y_3471_; lean_object* v___y_3472_; lean_object* v___y_3473_; lean_object* v___y_3474_; lean_object* v___y_3475_; lean_object* v___y_3502_; lean_object* v___y_3503_; lean_object* v___y_3504_; lean_object* v___y_3505_; lean_object* v___y_3506_; lean_object* v___y_3507_; lean_object* v___y_3508_; lean_object* v___y_3509_; lean_object* v___y_3510_; lean_object* v___y_3511_; lean_object* v___y_3512_; lean_object* v___x_3539_; 
v___x_3539_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_3453_);
if (lean_obj_tag(v___x_3539_) == 0)
{
lean_object* v_a_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3616_; 
v_a_3540_ = lean_ctor_get(v___x_3539_, 0);
v_isSharedCheck_3616_ = !lean_is_exclusive(v___x_3539_);
if (v_isSharedCheck_3616_ == 0)
{
v___x_3542_ = v___x_3539_;
v_isShared_3543_ = v_isSharedCheck_3616_;
goto v_resetjp_3541_;
}
else
{
lean_inc(v_a_3540_);
lean_dec(v___x_3539_);
v___x_3542_ = lean_box(0);
v_isShared_3543_ = v_isSharedCheck_3616_;
goto v_resetjp_3541_;
}
v_resetjp_3541_:
{
uint8_t v___x_3544_; 
v___x_3544_ = lean_unbox(v_a_3540_);
lean_dec(v_a_3540_);
if (v___x_3544_ == 0)
{
uint8_t v___x_3545_; 
lean_del_object(v___x_3542_);
v___x_3545_ = lean_nat_dec_eq(v_u_3448_, v_v_3449_);
if (v___x_3545_ == 0)
{
lean_object* v_options_3546_; uint8_t v_hasTrace_3547_; 
v_options_3546_ = lean_ctor_get(v_a_3461_, 2);
v_hasTrace_3547_ = lean_ctor_get_uint8(v_options_3546_, sizeof(void*)*1);
if (v_hasTrace_3547_ == 0)
{
v___y_3502_ = v_a_3452_;
v___y_3503_ = v_a_3453_;
v___y_3504_ = v_a_3454_;
v___y_3505_ = v_a_3455_;
v___y_3506_ = v_a_3456_;
v___y_3507_ = v_a_3457_;
v___y_3508_ = v_a_3458_;
v___y_3509_ = v_a_3459_;
v___y_3510_ = v_a_3460_;
v___y_3511_ = v_a_3461_;
v___y_3512_ = v_a_3462_;
goto v___jp_3501_;
}
else
{
lean_object* v_inheritedTraceOptions_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; uint8_t v___x_3551_; 
v_inheritedTraceOptions_3548_ = lean_ctor_get(v_a_3461_, 13);
v___x_3549_ = ((lean_object*)(l_Lean_Meta_Grind_Order_addEdge___closed__1));
v___x_3550_ = lean_obj_once(&l_Lean_Meta_Grind_Order_addEdge___closed__2, &l_Lean_Meta_Grind_Order_addEdge___closed__2_once, _init_l_Lean_Meta_Grind_Order_addEdge___closed__2);
v___x_3551_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3548_, v_options_3546_, v___x_3550_);
if (v___x_3551_ == 0)
{
v___y_3502_ = v_a_3452_;
v___y_3503_ = v_a_3453_;
v___y_3504_ = v_a_3454_;
v___y_3505_ = v_a_3455_;
v___y_3506_ = v_a_3456_;
v___y_3507_ = v_a_3457_;
v___y_3508_ = v_a_3458_;
v___y_3509_ = v_a_3459_;
v___y_3510_ = v_a_3460_;
v___y_3511_ = v_a_3461_;
v___y_3512_ = v_a_3462_;
goto v___jp_3501_;
}
else
{
lean_object* v___x_3552_; 
v___x_3552_ = l_Lean_Meta_Grind_Order_getExpr(v_u_3448_, v_a_3452_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_, v_a_3462_);
if (lean_obj_tag(v___x_3552_) == 0)
{
lean_object* v_a_3553_; lean_object* v___x_3554_; 
v_a_3553_ = lean_ctor_get(v___x_3552_, 0);
lean_inc(v_a_3553_);
lean_dec_ref(v___x_3552_);
v___x_3554_ = l_Lean_Meta_Grind_Order_getExpr(v_v_3449_, v_a_3452_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_, v_a_3462_);
if (lean_obj_tag(v___x_3554_) == 0)
{
lean_object* v_a_3555_; lean_object* v_k_3556_; uint8_t v_strict_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___y_3565_; 
v_a_3555_ = lean_ctor_get(v___x_3554_, 0);
lean_inc(v_a_3555_);
lean_dec_ref(v___x_3554_);
v_k_3556_ = lean_ctor_get(v_k_3450_, 0);
v_strict_3557_ = lean_ctor_get_uint8(v_k_3450_, sizeof(void*)*1);
v___x_3558_ = l_Lean_MessageData_ofExpr(v_a_3553_);
v___x_3559_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4);
v___x_3560_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3560_, 0, v___x_3558_);
lean_ctor_set(v___x_3560_, 1, v___x_3559_);
v___x_3561_ = l_Lean_MessageData_ofExpr(v_a_3555_);
v___x_3562_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3562_, 0, v___x_3560_);
lean_ctor_set(v___x_3562_, 1, v___x_3561_);
v___x_3563_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3563_, 0, v___x_3562_);
lean_ctor_set(v___x_3563_, 1, v___x_3559_);
if (v_strict_3557_ == 0)
{
lean_object* v___x_3570_; 
v___x_3570_ = l_Int_repr(v_k_3556_);
v___y_3565_ = v___x_3570_;
goto v___jp_3564_;
}
else
{
lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; 
v___x_3571_ = l_Int_repr(v_k_3556_);
v___x_3572_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5));
v___x_3573_ = lean_string_append(v___x_3571_, v___x_3572_);
v___y_3565_ = v___x_3573_;
goto v___jp_3564_;
}
v___jp_3564_:
{
lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; 
v___x_3566_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3566_, 0, v___y_3565_);
v___x_3567_ = l_Lean_MessageData_ofFormat(v___x_3566_);
v___x_3568_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3568_, 0, v___x_3563_);
lean_ctor_set(v___x_3568_, 1, v___x_3567_);
v___x_3569_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(v___x_3549_, v___x_3568_, v_a_3459_, v_a_3460_, v_a_3461_, v_a_3462_);
if (lean_obj_tag(v___x_3569_) == 0)
{
lean_dec_ref(v___x_3569_);
v___y_3502_ = v_a_3452_;
v___y_3503_ = v_a_3453_;
v___y_3504_ = v_a_3454_;
v___y_3505_ = v_a_3455_;
v___y_3506_ = v_a_3456_;
v___y_3507_ = v_a_3457_;
v___y_3508_ = v_a_3458_;
v___y_3509_ = v_a_3459_;
v___y_3510_ = v_a_3460_;
v___y_3511_ = v_a_3461_;
v___y_3512_ = v_a_3462_;
goto v___jp_3501_;
}
else
{
lean_dec_ref(v_h_3451_);
lean_dec_ref(v_k_3450_);
lean_dec(v_v_3449_);
lean_dec(v_u_3448_);
return v___x_3569_;
}
}
}
else
{
lean_object* v_a_3574_; lean_object* v___x_3576_; uint8_t v_isShared_3577_; uint8_t v_isSharedCheck_3581_; 
lean_dec(v_a_3553_);
lean_dec_ref(v_h_3451_);
lean_dec_ref(v_k_3450_);
lean_dec(v_v_3449_);
lean_dec(v_u_3448_);
v_a_3574_ = lean_ctor_get(v___x_3554_, 0);
v_isSharedCheck_3581_ = !lean_is_exclusive(v___x_3554_);
if (v_isSharedCheck_3581_ == 0)
{
v___x_3576_ = v___x_3554_;
v_isShared_3577_ = v_isSharedCheck_3581_;
goto v_resetjp_3575_;
}
else
{
lean_inc(v_a_3574_);
lean_dec(v___x_3554_);
v___x_3576_ = lean_box(0);
v_isShared_3577_ = v_isSharedCheck_3581_;
goto v_resetjp_3575_;
}
v_resetjp_3575_:
{
lean_object* v___x_3579_; 
if (v_isShared_3577_ == 0)
{
v___x_3579_ = v___x_3576_;
goto v_reusejp_3578_;
}
else
{
lean_object* v_reuseFailAlloc_3580_; 
v_reuseFailAlloc_3580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3580_, 0, v_a_3574_);
v___x_3579_ = v_reuseFailAlloc_3580_;
goto v_reusejp_3578_;
}
v_reusejp_3578_:
{
return v___x_3579_;
}
}
}
}
else
{
lean_object* v_a_3582_; lean_object* v___x_3584_; uint8_t v_isShared_3585_; uint8_t v_isSharedCheck_3589_; 
lean_dec_ref(v_h_3451_);
lean_dec_ref(v_k_3450_);
lean_dec(v_v_3449_);
lean_dec(v_u_3448_);
v_a_3582_ = lean_ctor_get(v___x_3552_, 0);
v_isSharedCheck_3589_ = !lean_is_exclusive(v___x_3552_);
if (v_isSharedCheck_3589_ == 0)
{
v___x_3584_ = v___x_3552_;
v_isShared_3585_ = v_isSharedCheck_3589_;
goto v_resetjp_3583_;
}
else
{
lean_inc(v_a_3582_);
lean_dec(v___x_3552_);
v___x_3584_ = lean_box(0);
v_isShared_3585_ = v_isSharedCheck_3589_;
goto v_resetjp_3583_;
}
v_resetjp_3583_:
{
lean_object* v___x_3587_; 
if (v_isShared_3585_ == 0)
{
v___x_3587_ = v___x_3584_;
goto v_reusejp_3586_;
}
else
{
lean_object* v_reuseFailAlloc_3588_; 
v_reuseFailAlloc_3588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3588_, 0, v_a_3582_);
v___x_3587_ = v_reuseFailAlloc_3588_;
goto v_reusejp_3586_;
}
v_reusejp_3586_:
{
return v___x_3587_;
}
}
}
}
}
}
else
{
uint8_t v___x_3590_; 
lean_dec(v_v_3449_);
v___x_3590_ = l_Lean_Meta_Grind_Order_Weight_isNeg(v_k_3450_);
if (v___x_3590_ == 0)
{
lean_dec_ref(v_h_3451_);
lean_dec_ref(v_k_3450_);
lean_dec(v_u_3448_);
goto v___jp_3536_;
}
else
{
lean_object* v___x_3591_; 
v___x_3591_ = l_Lean_Meta_Grind_Order_getExpr(v_u_3448_, v_a_3452_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_, v_a_3462_);
lean_dec(v_u_3448_);
if (lean_obj_tag(v___x_3591_) == 0)
{
lean_object* v_a_3592_; lean_object* v___x_3593_; 
v_a_3592_ = lean_ctor_get(v___x_3591_, 0);
lean_inc(v_a_3592_);
lean_dec_ref(v___x_3591_);
v___x_3593_ = l_Lean_Meta_Grind_Order_mkSelfUnsatProof(v_a_3592_, v_k_3450_, v_h_3451_, v_a_3452_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_, v_a_3462_);
lean_dec_ref(v_k_3450_);
if (lean_obj_tag(v___x_3593_) == 0)
{
lean_object* v_a_3594_; lean_object* v___x_3595_; 
v_a_3594_ = lean_ctor_get(v___x_3593_, 0);
lean_inc(v_a_3594_);
lean_dec_ref(v___x_3593_);
v___x_3595_ = l_Lean_Meta_Grind_closeGoal(v_a_3594_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_, v_a_3462_);
if (lean_obj_tag(v___x_3595_) == 0)
{
lean_dec_ref(v___x_3595_);
goto v___jp_3536_;
}
else
{
return v___x_3595_;
}
}
else
{
lean_object* v_a_3596_; lean_object* v___x_3598_; uint8_t v_isShared_3599_; uint8_t v_isSharedCheck_3603_; 
v_a_3596_ = lean_ctor_get(v___x_3593_, 0);
v_isSharedCheck_3603_ = !lean_is_exclusive(v___x_3593_);
if (v_isSharedCheck_3603_ == 0)
{
v___x_3598_ = v___x_3593_;
v_isShared_3599_ = v_isSharedCheck_3603_;
goto v_resetjp_3597_;
}
else
{
lean_inc(v_a_3596_);
lean_dec(v___x_3593_);
v___x_3598_ = lean_box(0);
v_isShared_3599_ = v_isSharedCheck_3603_;
goto v_resetjp_3597_;
}
v_resetjp_3597_:
{
lean_object* v___x_3601_; 
if (v_isShared_3599_ == 0)
{
v___x_3601_ = v___x_3598_;
goto v_reusejp_3600_;
}
else
{
lean_object* v_reuseFailAlloc_3602_; 
v_reuseFailAlloc_3602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3602_, 0, v_a_3596_);
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
lean_dec_ref(v_h_3451_);
lean_dec_ref(v_k_3450_);
v_a_3604_ = lean_ctor_get(v___x_3591_, 0);
v_isSharedCheck_3611_ = !lean_is_exclusive(v___x_3591_);
if (v_isSharedCheck_3611_ == 0)
{
v___x_3606_ = v___x_3591_;
v_isShared_3607_ = v_isSharedCheck_3611_;
goto v_resetjp_3605_;
}
else
{
lean_inc(v_a_3604_);
lean_dec(v___x_3591_);
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
}
}
}
else
{
lean_object* v___x_3612_; lean_object* v___x_3614_; 
lean_dec_ref(v_h_3451_);
lean_dec_ref(v_k_3450_);
lean_dec(v_v_3449_);
lean_dec(v_u_3448_);
v___x_3612_ = lean_box(0);
if (v_isShared_3543_ == 0)
{
lean_ctor_set(v___x_3542_, 0, v___x_3612_);
v___x_3614_ = v___x_3542_;
goto v_reusejp_3613_;
}
else
{
lean_object* v_reuseFailAlloc_3615_; 
v_reuseFailAlloc_3615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3615_, 0, v___x_3612_);
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
else
{
lean_object* v_a_3617_; lean_object* v___x_3619_; uint8_t v_isShared_3620_; uint8_t v_isSharedCheck_3624_; 
lean_dec_ref(v_h_3451_);
lean_dec_ref(v_k_3450_);
lean_dec(v_v_3449_);
lean_dec(v_u_3448_);
v_a_3617_ = lean_ctor_get(v___x_3539_, 0);
v_isSharedCheck_3624_ = !lean_is_exclusive(v___x_3539_);
if (v_isSharedCheck_3624_ == 0)
{
v___x_3619_ = v___x_3539_;
v_isShared_3620_ = v_isSharedCheck_3624_;
goto v_resetjp_3618_;
}
else
{
lean_inc(v_a_3617_);
lean_dec(v___x_3539_);
v___x_3619_ = lean_box(0);
v_isShared_3620_ = v_isSharedCheck_3624_;
goto v_resetjp_3618_;
}
v_resetjp_3618_:
{
lean_object* v___x_3622_; 
if (v_isShared_3620_ == 0)
{
v___x_3622_ = v___x_3619_;
goto v_reusejp_3621_;
}
else
{
lean_object* v_reuseFailAlloc_3623_; 
v_reuseFailAlloc_3623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3623_, 0, v_a_3617_);
v___x_3622_ = v_reuseFailAlloc_3623_;
goto v_reusejp_3621_;
}
v_reusejp_3621_:
{
return v___x_3622_;
}
}
}
v___jp_3464_:
{
lean_object* v___x_3476_; 
v___x_3476_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isShorter(v_u_3448_, v_v_3449_, v_k_3450_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_);
if (lean_obj_tag(v___x_3476_) == 0)
{
lean_object* v_a_3477_; lean_object* v___x_3479_; uint8_t v_isShared_3480_; uint8_t v_isSharedCheck_3492_; 
v_a_3477_ = lean_ctor_get(v___x_3476_, 0);
v_isSharedCheck_3492_ = !lean_is_exclusive(v___x_3476_);
if (v_isSharedCheck_3492_ == 0)
{
v___x_3479_ = v___x_3476_;
v_isShared_3480_ = v_isSharedCheck_3492_;
goto v_resetjp_3478_;
}
else
{
lean_inc(v_a_3477_);
lean_dec(v___x_3476_);
v___x_3479_ = lean_box(0);
v_isShared_3480_ = v_isSharedCheck_3492_;
goto v_resetjp_3478_;
}
v_resetjp_3478_:
{
uint8_t v___x_3481_; 
v___x_3481_ = lean_unbox(v_a_3477_);
lean_dec(v_a_3477_);
if (v___x_3481_ == 0)
{
lean_object* v___x_3482_; lean_object* v___x_3484_; 
lean_dec_ref(v_h_3451_);
lean_dec_ref(v_k_3450_);
lean_dec(v_v_3449_);
lean_dec(v_u_3448_);
v___x_3482_ = lean_box(0);
if (v_isShared_3480_ == 0)
{
lean_ctor_set(v___x_3479_, 0, v___x_3482_);
v___x_3484_ = v___x_3479_;
goto v_reusejp_3483_;
}
else
{
lean_object* v_reuseFailAlloc_3485_; 
v_reuseFailAlloc_3485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3485_, 0, v___x_3482_);
v___x_3484_ = v_reuseFailAlloc_3485_;
goto v_reusejp_3483_;
}
v_reusejp_3483_:
{
return v___x_3484_;
}
}
else
{
lean_object* v___x_3486_; 
lean_del_object(v___x_3479_);
lean_inc_ref(v_k_3450_);
lean_inc(v_v_3449_);
lean_inc(v_u_3448_);
v___x_3486_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist___redArg(v_u_3448_, v_v_3449_, v_k_3450_, v___y_3465_, v___y_3466_);
if (lean_obj_tag(v___x_3486_) == 0)
{
lean_object* v___x_3487_; lean_object* v___x_3488_; 
lean_dec_ref(v___x_3486_);
lean_inc_ref(v_k_3450_);
lean_inc_n(v_u_3448_, 2);
v___x_3487_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3487_, 0, v_u_3448_);
lean_ctor_set(v___x_3487_, 1, v_k_3450_);
lean_ctor_set(v___x_3487_, 2, v_h_3451_);
lean_inc(v_v_3449_);
v___x_3488_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___redArg(v_u_3448_, v_v_3449_, v___x_3487_, v___y_3465_, v___y_3466_);
if (lean_obj_tag(v___x_3488_) == 0)
{
lean_object* v___x_3489_; 
lean_dec_ref(v___x_3488_);
lean_inc_ref(v_k_3450_);
lean_inc(v_v_3449_);
lean_inc(v_u_3448_);
v___x_3489_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate(v_u_3448_, v_v_3449_, v_k_3450_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_);
if (lean_obj_tag(v___x_3489_) == 0)
{
lean_object* v___x_3490_; 
lean_dec_ref(v___x_3489_);
v___x_3490_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update(v_u_3448_, v_v_3449_, v_k_3450_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_);
if (lean_obj_tag(v___x_3490_) == 0)
{
lean_object* v___x_3491_; 
lean_dec_ref(v___x_3490_);
v___x_3491_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending(v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_);
return v___x_3491_;
}
else
{
return v___x_3490_;
}
}
else
{
lean_dec_ref(v_k_3450_);
lean_dec(v_v_3449_);
lean_dec(v_u_3448_);
return v___x_3489_;
}
}
else
{
lean_dec_ref(v_k_3450_);
lean_dec(v_v_3449_);
lean_dec(v_u_3448_);
return v___x_3488_;
}
}
else
{
lean_dec_ref(v_h_3451_);
lean_dec_ref(v_k_3450_);
lean_dec(v_v_3449_);
lean_dec(v_u_3448_);
return v___x_3486_;
}
}
}
}
else
{
lean_object* v_a_3493_; lean_object* v___x_3495_; uint8_t v_isShared_3496_; uint8_t v_isSharedCheck_3500_; 
lean_dec_ref(v_h_3451_);
lean_dec_ref(v_k_3450_);
lean_dec(v_v_3449_);
lean_dec(v_u_3448_);
v_a_3493_ = lean_ctor_get(v___x_3476_, 0);
v_isSharedCheck_3500_ = !lean_is_exclusive(v___x_3476_);
if (v_isSharedCheck_3500_ == 0)
{
v___x_3495_ = v___x_3476_;
v_isShared_3496_ = v_isSharedCheck_3500_;
goto v_resetjp_3494_;
}
else
{
lean_inc(v_a_3493_);
lean_dec(v___x_3476_);
v___x_3495_ = lean_box(0);
v_isShared_3496_ = v_isSharedCheck_3500_;
goto v_resetjp_3494_;
}
v_resetjp_3494_:
{
lean_object* v___x_3498_; 
if (v_isShared_3496_ == 0)
{
v___x_3498_ = v___x_3495_;
goto v_reusejp_3497_;
}
else
{
lean_object* v_reuseFailAlloc_3499_; 
v_reuseFailAlloc_3499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3499_, 0, v_a_3493_);
v___x_3498_ = v_reuseFailAlloc_3499_;
goto v_reusejp_3497_;
}
v_reusejp_3497_:
{
return v___x_3498_;
}
}
}
}
v___jp_3501_:
{
lean_object* v___x_3513_; 
v___x_3513_ = l_Lean_Meta_Grind_Order_getDist_x3f(v_v_3449_, v_u_3448_, v___y_3502_, v___y_3503_, v___y_3504_, v___y_3505_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_, v___y_3510_, v___y_3511_, v___y_3512_);
if (lean_obj_tag(v___x_3513_) == 0)
{
lean_object* v_a_3514_; 
v_a_3514_ = lean_ctor_get(v___x_3513_, 0);
lean_inc(v_a_3514_);
lean_dec_ref(v___x_3513_);
if (lean_obj_tag(v_a_3514_) == 1)
{
lean_object* v_val_3515_; lean_object* v___x_3516_; uint8_t v___x_3517_; 
v_val_3515_ = lean_ctor_get(v_a_3514_, 0);
lean_inc_n(v_val_3515_, 2);
lean_dec_ref(v_a_3514_);
v___x_3516_ = l_Lean_Meta_Grind_Order_Weight_add(v_k_3450_, v_val_3515_);
v___x_3517_ = l_Lean_Meta_Grind_Order_Weight_isNeg(v___x_3516_);
lean_dec_ref(v___x_3516_);
if (v___x_3517_ == 0)
{
lean_dec(v_val_3515_);
v___y_3465_ = v___y_3502_;
v___y_3466_ = v___y_3503_;
v___y_3467_ = v___y_3504_;
v___y_3468_ = v___y_3505_;
v___y_3469_ = v___y_3506_;
v___y_3470_ = v___y_3507_;
v___y_3471_ = v___y_3508_;
v___y_3472_ = v___y_3509_;
v___y_3473_ = v___y_3510_;
v___y_3474_ = v___y_3511_;
v___y_3475_ = v___y_3512_;
goto v___jp_3464_;
}
else
{
lean_object* v___x_3518_; 
v___x_3518_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setUnsat(v_u_3448_, v_v_3449_, v_k_3450_, v_h_3451_, v_val_3515_, v___y_3502_, v___y_3503_, v___y_3504_, v___y_3505_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_, v___y_3510_, v___y_3511_, v___y_3512_);
lean_dec(v_val_3515_);
lean_dec_ref(v_k_3450_);
lean_dec(v_v_3449_);
lean_dec(v_u_3448_);
if (lean_obj_tag(v___x_3518_) == 0)
{
lean_object* v___x_3520_; uint8_t v_isShared_3521_; uint8_t v_isSharedCheck_3526_; 
v_isSharedCheck_3526_ = !lean_is_exclusive(v___x_3518_);
if (v_isSharedCheck_3526_ == 0)
{
lean_object* v_unused_3527_; 
v_unused_3527_ = lean_ctor_get(v___x_3518_, 0);
lean_dec(v_unused_3527_);
v___x_3520_ = v___x_3518_;
v_isShared_3521_ = v_isSharedCheck_3526_;
goto v_resetjp_3519_;
}
else
{
lean_dec(v___x_3518_);
v___x_3520_ = lean_box(0);
v_isShared_3521_ = v_isSharedCheck_3526_;
goto v_resetjp_3519_;
}
v_resetjp_3519_:
{
lean_object* v___x_3522_; lean_object* v___x_3524_; 
v___x_3522_ = lean_box(0);
if (v_isShared_3521_ == 0)
{
lean_ctor_set(v___x_3520_, 0, v___x_3522_);
v___x_3524_ = v___x_3520_;
goto v_reusejp_3523_;
}
else
{
lean_object* v_reuseFailAlloc_3525_; 
v_reuseFailAlloc_3525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3525_, 0, v___x_3522_);
v___x_3524_ = v_reuseFailAlloc_3525_;
goto v_reusejp_3523_;
}
v_reusejp_3523_:
{
return v___x_3524_;
}
}
}
else
{
return v___x_3518_;
}
}
}
else
{
lean_dec(v_a_3514_);
v___y_3465_ = v___y_3502_;
v___y_3466_ = v___y_3503_;
v___y_3467_ = v___y_3504_;
v___y_3468_ = v___y_3505_;
v___y_3469_ = v___y_3506_;
v___y_3470_ = v___y_3507_;
v___y_3471_ = v___y_3508_;
v___y_3472_ = v___y_3509_;
v___y_3473_ = v___y_3510_;
v___y_3474_ = v___y_3511_;
v___y_3475_ = v___y_3512_;
goto v___jp_3464_;
}
}
else
{
lean_object* v_a_3528_; lean_object* v___x_3530_; uint8_t v_isShared_3531_; uint8_t v_isSharedCheck_3535_; 
lean_dec_ref(v_h_3451_);
lean_dec_ref(v_k_3450_);
lean_dec(v_v_3449_);
lean_dec(v_u_3448_);
v_a_3528_ = lean_ctor_get(v___x_3513_, 0);
v_isSharedCheck_3535_ = !lean_is_exclusive(v___x_3513_);
if (v_isSharedCheck_3535_ == 0)
{
v___x_3530_ = v___x_3513_;
v_isShared_3531_ = v_isSharedCheck_3535_;
goto v_resetjp_3529_;
}
else
{
lean_inc(v_a_3528_);
lean_dec(v___x_3513_);
v___x_3530_ = lean_box(0);
v_isShared_3531_ = v_isSharedCheck_3535_;
goto v_resetjp_3529_;
}
v_resetjp_3529_:
{
lean_object* v___x_3533_; 
if (v_isShared_3531_ == 0)
{
v___x_3533_ = v___x_3530_;
goto v_reusejp_3532_;
}
else
{
lean_object* v_reuseFailAlloc_3534_; 
v_reuseFailAlloc_3534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3534_, 0, v_a_3528_);
v___x_3533_ = v_reuseFailAlloc_3534_;
goto v_reusejp_3532_;
}
v_reusejp_3532_:
{
return v___x_3533_;
}
}
}
}
v___jp_3536_:
{
lean_object* v___x_3537_; lean_object* v___x_3538_; 
v___x_3537_ = lean_box(0);
v___x_3538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3538_, 0, v___x_3537_);
return v___x_3538_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_addEdge___boxed(lean_object* v_u_3625_, lean_object* v_v_3626_, lean_object* v_k_3627_, lean_object* v_h_3628_, lean_object* v_a_3629_, lean_object* v_a_3630_, lean_object* v_a_3631_, lean_object* v_a_3632_, lean_object* v_a_3633_, lean_object* v_a_3634_, lean_object* v_a_3635_, lean_object* v_a_3636_, lean_object* v_a_3637_, lean_object* v_a_3638_, lean_object* v_a_3639_, lean_object* v_a_3640_){
_start:
{
lean_object* v_res_3641_; 
v_res_3641_ = l_Lean_Meta_Grind_Order_addEdge(v_u_3625_, v_v_3626_, v_k_3627_, v_h_3628_, v_a_3629_, v_a_3630_, v_a_3631_, v_a_3632_, v_a_3633_, v_a_3634_, v_a_3635_, v_a_3636_, v_a_3637_, v_a_3638_, v_a_3639_);
lean_dec(v_a_3639_);
lean_dec_ref(v_a_3638_);
lean_dec(v_a_3637_);
lean_dec_ref(v_a_3636_);
lean_dec(v_a_3635_);
lean_dec_ref(v_a_3634_);
lean_dec(v_a_3633_);
lean_dec_ref(v_a_3632_);
lean_dec(v_a_3631_);
lean_dec(v_a_3630_);
lean_dec(v_a_3629_);
return v_res_3641_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__2(void){
_start:
{
lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; 
v___x_3648_ = lean_box(0);
v___x_3649_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__1));
v___x_3650_ = l_Lean_mkConst(v___x_3649_, v___x_3648_);
return v___x_3650_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5(void){
_start:
{
lean_object* v_cls_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; 
v_cls_3656_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__4));
v___x_3657_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__6));
v___x_3658_ = l_Lean_Name_append(v___x_3657_, v_cls_3656_);
return v___x_3658_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue(lean_object* v_c_3659_, lean_object* v_e_3660_, lean_object* v_he_3661_, lean_object* v_a_3662_, lean_object* v_a_3663_, lean_object* v_a_3664_, lean_object* v_a_3665_, lean_object* v_a_3666_, lean_object* v_a_3667_, lean_object* v_a_3668_, lean_object* v_a_3669_, lean_object* v_a_3670_, lean_object* v_a_3671_, lean_object* v_a_3672_){
_start:
{
lean_object* v___y_3675_; lean_object* v___y_3676_; lean_object* v___y_3677_; lean_object* v___y_3678_; lean_object* v___y_3679_; lean_object* v___y_3680_; lean_object* v___y_3681_; lean_object* v___y_3682_; lean_object* v___y_3683_; lean_object* v___y_3684_; lean_object* v___y_3685_; lean_object* v___y_3686_; lean_object* v___y_3687_; lean_object* v___y_3688_; lean_object* v___y_3689_; uint8_t v___y_3690_; lean_object* v_h_3694_; lean_object* v___y_3695_; lean_object* v___y_3696_; lean_object* v___y_3697_; lean_object* v___y_3698_; lean_object* v___y_3699_; lean_object* v___y_3700_; lean_object* v___y_3701_; lean_object* v___y_3702_; lean_object* v___y_3703_; lean_object* v___y_3704_; lean_object* v___y_3705_; lean_object* v___y_3716_; lean_object* v___y_3717_; lean_object* v___y_3718_; lean_object* v___y_3719_; lean_object* v___y_3720_; lean_object* v___y_3721_; lean_object* v___y_3722_; lean_object* v___y_3723_; lean_object* v___y_3724_; lean_object* v___y_3725_; lean_object* v___y_3726_; lean_object* v_options_3734_; uint8_t v_hasTrace_3735_; 
v_options_3734_ = lean_ctor_get(v_a_3671_, 2);
v_hasTrace_3735_ = lean_ctor_get_uint8(v_options_3734_, sizeof(void*)*1);
if (v_hasTrace_3735_ == 0)
{
v___y_3716_ = v_a_3662_;
v___y_3717_ = v_a_3663_;
v___y_3718_ = v_a_3664_;
v___y_3719_ = v_a_3665_;
v___y_3720_ = v_a_3666_;
v___y_3721_ = v_a_3667_;
v___y_3722_ = v_a_3668_;
v___y_3723_ = v_a_3669_;
v___y_3724_ = v_a_3670_;
v___y_3725_ = v_a_3671_;
v___y_3726_ = v_a_3672_;
goto v___jp_3715_;
}
else
{
lean_object* v_inheritedTraceOptions_3736_; lean_object* v_cls_3737_; lean_object* v___x_3738_; uint8_t v___x_3739_; 
v_inheritedTraceOptions_3736_ = lean_ctor_get(v_a_3671_, 13);
v_cls_3737_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__4));
v___x_3738_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5);
v___x_3739_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3736_, v_options_3734_, v___x_3738_);
if (v___x_3739_ == 0)
{
v___y_3716_ = v_a_3662_;
v___y_3717_ = v_a_3663_;
v___y_3718_ = v_a_3664_;
v___y_3719_ = v_a_3665_;
v___y_3720_ = v_a_3666_;
v___y_3721_ = v_a_3667_;
v___y_3722_ = v_a_3668_;
v___y_3723_ = v_a_3669_;
v___y_3724_ = v_a_3670_;
v___y_3725_ = v_a_3671_;
v___y_3726_ = v_a_3672_;
goto v___jp_3715_;
}
else
{
lean_object* v___x_3740_; 
v___x_3740_ = l_Lean_Meta_Grind_Order_Cnstr_pp(v_c_3659_, v_a_3662_, v_a_3663_, v_a_3664_, v_a_3665_, v_a_3666_, v_a_3667_, v_a_3668_, v_a_3669_, v_a_3670_, v_a_3671_, v_a_3672_);
if (lean_obj_tag(v___x_3740_) == 0)
{
lean_object* v_a_3741_; lean_object* v___x_3742_; 
v_a_3741_ = lean_ctor_get(v___x_3740_, 0);
lean_inc(v_a_3741_);
lean_dec_ref(v___x_3740_);
v___x_3742_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(v_cls_3737_, v_a_3741_, v_a_3669_, v_a_3670_, v_a_3671_, v_a_3672_);
if (lean_obj_tag(v___x_3742_) == 0)
{
lean_dec_ref(v___x_3742_);
v___y_3716_ = v_a_3662_;
v___y_3717_ = v_a_3663_;
v___y_3718_ = v_a_3664_;
v___y_3719_ = v_a_3665_;
v___y_3720_ = v_a_3666_;
v___y_3721_ = v_a_3667_;
v___y_3722_ = v_a_3668_;
v___y_3723_ = v_a_3669_;
v___y_3724_ = v_a_3670_;
v___y_3725_ = v_a_3671_;
v___y_3726_ = v_a_3672_;
goto v___jp_3715_;
}
else
{
lean_dec_ref(v_he_3661_);
lean_dec_ref(v_e_3660_);
lean_dec_ref(v_c_3659_);
return v___x_3742_;
}
}
else
{
lean_object* v_a_3743_; lean_object* v___x_3745_; uint8_t v_isShared_3746_; uint8_t v_isSharedCheck_3750_; 
lean_dec_ref(v_he_3661_);
lean_dec_ref(v_e_3660_);
lean_dec_ref(v_c_3659_);
v_a_3743_ = lean_ctor_get(v___x_3740_, 0);
v_isSharedCheck_3750_ = !lean_is_exclusive(v___x_3740_);
if (v_isSharedCheck_3750_ == 0)
{
v___x_3745_ = v___x_3740_;
v_isShared_3746_ = v_isSharedCheck_3750_;
goto v_resetjp_3744_;
}
else
{
lean_inc(v_a_3743_);
lean_dec(v___x_3740_);
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
}
}
v___jp_3674_:
{
lean_object* v___x_3691_; lean_object* v___x_3692_; 
v___x_3691_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3691_, 0, v___y_3680_);
lean_ctor_set_uint8(v___x_3691_, sizeof(void*)*1, v___y_3690_);
v___x_3692_ = l_Lean_Meta_Grind_Order_addEdge(v___y_3678_, v___y_3676_, v___x_3691_, v___y_3679_, v___y_3675_, v___y_3682_, v___y_3687_, v___y_3689_, v___y_3677_, v___y_3688_, v___y_3681_, v___y_3685_, v___y_3684_, v___y_3683_, v___y_3686_);
return v___x_3692_;
}
v___jp_3693_:
{
uint8_t v_kind_3706_; 
v_kind_3706_ = lean_ctor_get_uint8(v_c_3659_, sizeof(void*)*5);
if (v_kind_3706_ == 1)
{
lean_object* v_u_3707_; lean_object* v_v_3708_; lean_object* v_k_3709_; uint8_t v___x_3710_; 
v_u_3707_ = lean_ctor_get(v_c_3659_, 0);
lean_inc(v_u_3707_);
v_v_3708_ = lean_ctor_get(v_c_3659_, 1);
lean_inc(v_v_3708_);
v_k_3709_ = lean_ctor_get(v_c_3659_, 2);
lean_inc(v_k_3709_);
lean_dec_ref(v_c_3659_);
v___x_3710_ = 1;
v___y_3675_ = v___y_3695_;
v___y_3676_ = v_v_3708_;
v___y_3677_ = v___y_3699_;
v___y_3678_ = v_u_3707_;
v___y_3679_ = v_h_3694_;
v___y_3680_ = v_k_3709_;
v___y_3681_ = v___y_3701_;
v___y_3682_ = v___y_3696_;
v___y_3683_ = v___y_3704_;
v___y_3684_ = v___y_3703_;
v___y_3685_ = v___y_3702_;
v___y_3686_ = v___y_3705_;
v___y_3687_ = v___y_3697_;
v___y_3688_ = v___y_3700_;
v___y_3689_ = v___y_3698_;
v___y_3690_ = v___x_3710_;
goto v___jp_3674_;
}
else
{
lean_object* v_u_3711_; lean_object* v_v_3712_; lean_object* v_k_3713_; uint8_t v___x_3714_; 
v_u_3711_ = lean_ctor_get(v_c_3659_, 0);
lean_inc(v_u_3711_);
v_v_3712_ = lean_ctor_get(v_c_3659_, 1);
lean_inc(v_v_3712_);
v_k_3713_ = lean_ctor_get(v_c_3659_, 2);
lean_inc(v_k_3713_);
lean_dec_ref(v_c_3659_);
v___x_3714_ = 0;
v___y_3675_ = v___y_3695_;
v___y_3676_ = v_v_3712_;
v___y_3677_ = v___y_3699_;
v___y_3678_ = v_u_3711_;
v___y_3679_ = v_h_3694_;
v___y_3680_ = v_k_3713_;
v___y_3681_ = v___y_3701_;
v___y_3682_ = v___y_3696_;
v___y_3683_ = v___y_3704_;
v___y_3684_ = v___y_3703_;
v___y_3685_ = v___y_3702_;
v___y_3686_ = v___y_3705_;
v___y_3687_ = v___y_3697_;
v___y_3688_ = v___y_3700_;
v___y_3689_ = v___y_3698_;
v___y_3690_ = v___x_3714_;
goto v___jp_3674_;
}
}
v___jp_3715_:
{
lean_object* v_h_x3f_3727_; 
v_h_x3f_3727_ = lean_ctor_get(v_c_3659_, 4);
if (lean_obj_tag(v_h_x3f_3727_) == 1)
{
lean_object* v_e_3728_; lean_object* v_val_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; 
v_e_3728_ = lean_ctor_get(v_c_3659_, 3);
v_val_3729_ = lean_ctor_get(v_h_x3f_3727_, 0);
v___x_3730_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__2, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__2);
lean_inc_ref(v_e_3660_);
v___x_3731_ = l_Lean_Meta_mkOfEqTrueCore(v_e_3660_, v_he_3661_);
lean_inc(v_val_3729_);
lean_inc_ref(v_e_3728_);
v___x_3732_ = l_Lean_mkApp4(v___x_3730_, v_e_3660_, v_e_3728_, v_val_3729_, v___x_3731_);
v_h_3694_ = v___x_3732_;
v___y_3695_ = v___y_3716_;
v___y_3696_ = v___y_3717_;
v___y_3697_ = v___y_3718_;
v___y_3698_ = v___y_3719_;
v___y_3699_ = v___y_3720_;
v___y_3700_ = v___y_3721_;
v___y_3701_ = v___y_3722_;
v___y_3702_ = v___y_3723_;
v___y_3703_ = v___y_3724_;
v___y_3704_ = v___y_3725_;
v___y_3705_ = v___y_3726_;
goto v___jp_3693_;
}
else
{
lean_object* v___x_3733_; 
v___x_3733_ = l_Lean_Meta_mkOfEqTrueCore(v_e_3660_, v_he_3661_);
v_h_3694_ = v___x_3733_;
v___y_3695_ = v___y_3716_;
v___y_3696_ = v___y_3717_;
v___y_3697_ = v___y_3718_;
v___y_3698_ = v___y_3719_;
v___y_3699_ = v___y_3720_;
v___y_3700_ = v___y_3721_;
v___y_3701_ = v___y_3722_;
v___y_3702_ = v___y_3723_;
v___y_3703_ = v___y_3724_;
v___y_3704_ = v___y_3725_;
v___y_3705_ = v___y_3726_;
goto v___jp_3693_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___boxed(lean_object* v_c_3751_, lean_object* v_e_3752_, lean_object* v_he_3753_, lean_object* v_a_3754_, lean_object* v_a_3755_, lean_object* v_a_3756_, lean_object* v_a_3757_, lean_object* v_a_3758_, lean_object* v_a_3759_, lean_object* v_a_3760_, lean_object* v_a_3761_, lean_object* v_a_3762_, lean_object* v_a_3763_, lean_object* v_a_3764_, lean_object* v_a_3765_){
_start:
{
lean_object* v_res_3766_; 
v_res_3766_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue(v_c_3751_, v_e_3752_, v_he_3753_, v_a_3754_, v_a_3755_, v_a_3756_, v_a_3757_, v_a_3758_, v_a_3759_, v_a_3760_, v_a_3761_, v_a_3762_, v_a_3763_, v_a_3764_);
lean_dec(v_a_3764_);
lean_dec_ref(v_a_3763_);
lean_dec(v_a_3762_);
lean_dec_ref(v_a_3761_);
lean_dec(v_a_3760_);
lean_dec_ref(v_a_3759_);
lean_dec(v_a_3758_);
lean_dec_ref(v_a_3757_);
lean_dec(v_a_3756_);
lean_dec(v_a_3755_);
lean_dec(v_a_3754_);
return v_res_3766_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__2(void){
_start:
{
lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; 
v___x_3773_ = lean_box(0);
v___x_3774_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__1));
v___x_3775_ = l_Lean_mkConst(v___x_3774_, v___x_3773_);
return v___x_3775_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__3(void){
_start:
{
lean_object* v___x_3776_; lean_object* v___x_3777_; 
v___x_3776_ = lean_unsigned_to_nat(1u);
v___x_3777_ = lean_nat_to_int(v___x_3776_);
return v___x_3777_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4(void){
_start:
{
lean_object* v___x_3778_; lean_object* v___x_3779_; 
v___x_3778_ = lean_unsigned_to_nat(0u);
v___x_3779_ = lean_nat_to_int(v___x_3778_);
return v___x_3779_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__8(void){
_start:
{
lean_object* v___x_3785_; lean_object* v___x_3786_; 
v___x_3785_ = lean_unsigned_to_nat(0u);
v___x_3786_ = l_Lean_Level_ofNat(v___x_3785_);
return v___x_3786_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__9(void){
_start:
{
lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; 
v___x_3787_ = lean_box(0);
v___x_3788_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__8, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__8);
v___x_3789_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3789_, 0, v___x_3788_);
lean_ctor_set(v___x_3789_, 1, v___x_3787_);
return v___x_3789_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10(void){
_start:
{
lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; 
v___x_3790_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__9, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__9);
v___x_3791_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__7));
v___x_3792_ = l_Lean_Expr_const___override(v___x_3791_, v___x_3790_);
return v___x_3792_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13(void){
_start:
{
lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; 
v___x_3796_ = lean_box(0);
v___x_3797_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__12));
v___x_3798_ = l_Lean_Expr_const___override(v___x_3797_, v___x_3796_);
return v___x_3798_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16(void){
_start:
{
lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; 
v___x_3803_ = lean_box(0);
v___x_3804_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__15));
v___x_3805_ = l_Lean_Expr_const___override(v___x_3804_, v___x_3803_);
return v___x_3805_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__29(void){
_start:
{
lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; 
v___x_3842_ = lean_box(0);
v___x_3843_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__28));
v___x_3844_ = l_Lean_mkConst(v___x_3843_, v___x_3842_);
return v___x_3844_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__31(void){
_start:
{
lean_object* v___x_3846_; lean_object* v___x_3847_; 
v___x_3846_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__30));
v___x_3847_ = l_Lean_stringToMessageData(v___x_3846_);
return v___x_3847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse(lean_object* v_c_3848_, lean_object* v_e_3849_, lean_object* v_he_3850_, lean_object* v_a_3851_, lean_object* v_a_3852_, lean_object* v_a_3853_, lean_object* v_a_3854_, lean_object* v_a_3855_, lean_object* v_a_3856_, lean_object* v_a_3857_, lean_object* v_a_3858_, lean_object* v_a_3859_, lean_object* v_a_3860_, lean_object* v_a_3861_){
_start:
{
lean_object* v___y_3864_; lean_object* v___y_3865_; lean_object* v_k_x27_3866_; lean_object* v_h_3867_; uint8_t v_strict_3868_; lean_object* v___y_3869_; lean_object* v___y_3870_; lean_object* v___y_3871_; lean_object* v___y_3872_; lean_object* v___y_3873_; lean_object* v___y_3874_; lean_object* v___y_3875_; lean_object* v___y_3876_; lean_object* v___y_3877_; lean_object* v___y_3878_; lean_object* v___y_3879_; lean_object* v___y_3883_; lean_object* v___y_3884_; lean_object* v___y_3885_; lean_object* v___y_3886_; lean_object* v___y_3887_; lean_object* v___y_3888_; lean_object* v___y_3889_; lean_object* v___y_3890_; lean_object* v___y_3891_; lean_object* v___y_3892_; lean_object* v___y_3893_; lean_object* v___y_3894_; lean_object* v___y_3895_; lean_object* v___y_3896_; lean_object* v___y_3897_; lean_object* v___y_3898_; lean_object* v___y_3899_; lean_object* v___y_3900_; lean_object* v___y_3901_; lean_object* v___y_3902_; lean_object* v___y_3903_; lean_object* v___y_3907_; lean_object* v___y_3908_; lean_object* v___y_3909_; lean_object* v___y_3910_; lean_object* v___y_3911_; lean_object* v___y_3912_; lean_object* v___y_3913_; lean_object* v___y_3914_; lean_object* v___y_3915_; lean_object* v___y_3916_; lean_object* v___y_3917_; lean_object* v___y_3918_; lean_object* v___y_3919_; lean_object* v___y_3920_; lean_object* v___y_3921_; lean_object* v___y_3922_; lean_object* v___y_3923_; uint8_t v___y_3924_; lean_object* v___x_3970_; 
v___x_3970_ = l_Lean_Meta_Grind_Order_isLinearPreorder(v_a_3851_, v_a_3852_, v_a_3853_, v_a_3854_, v_a_3855_, v_a_3856_, v_a_3857_, v_a_3858_, v_a_3859_, v_a_3860_, v_a_3861_);
if (lean_obj_tag(v___x_3970_) == 0)
{
lean_object* v_a_3971_; lean_object* v___x_3973_; uint8_t v_isShared_3974_; uint8_t v_isSharedCheck_4292_; 
v_a_3971_ = lean_ctor_get(v___x_3970_, 0);
v_isSharedCheck_4292_ = !lean_is_exclusive(v___x_3970_);
if (v_isSharedCheck_4292_ == 0)
{
v___x_3973_ = v___x_3970_;
v_isShared_3974_ = v_isSharedCheck_4292_;
goto v_resetjp_3972_;
}
else
{
lean_inc(v_a_3971_);
lean_dec(v___x_3970_);
v___x_3973_ = lean_box(0);
v_isShared_3974_ = v_isSharedCheck_4292_;
goto v_resetjp_3972_;
}
v_resetjp_3972_:
{
lean_object* v___y_3976_; lean_object* v___y_3977_; lean_object* v___y_3978_; lean_object* v___y_3979_; lean_object* v___y_3980_; lean_object* v___y_3981_; lean_object* v___y_3982_; lean_object* v___y_3983_; lean_object* v___y_3984_; lean_object* v___y_3985_; lean_object* v___y_3986_; lean_object* v___y_3987_; lean_object* v___y_3988_; lean_object* v___y_3989_; lean_object* v___y_3990_; uint8_t v___y_3991_; lean_object* v___y_3992_; lean_object* v___y_3993_; lean_object* v___y_3994_; lean_object* v___y_3995_; lean_object* v___y_3996_; lean_object* v___y_4002_; lean_object* v___y_4003_; lean_object* v___y_4004_; lean_object* v___y_4005_; lean_object* v___y_4006_; lean_object* v___y_4007_; lean_object* v___y_4008_; lean_object* v___y_4009_; lean_object* v___y_4010_; lean_object* v___y_4011_; lean_object* v___y_4012_; lean_object* v___y_4013_; lean_object* v___y_4014_; lean_object* v___y_4015_; lean_object* v___y_4016_; uint8_t v___y_4017_; lean_object* v___y_4018_; lean_object* v___y_4019_; lean_object* v___y_4020_; lean_object* v___y_4021_; lean_object* v___y_4034_; lean_object* v___y_4035_; lean_object* v___y_4036_; lean_object* v___y_4037_; lean_object* v___y_4038_; lean_object* v___y_4039_; lean_object* v___y_4040_; lean_object* v___y_4041_; lean_object* v___y_4042_; lean_object* v___y_4043_; lean_object* v___y_4044_; lean_object* v___y_4045_; lean_object* v___y_4046_; uint8_t v___y_4047_; lean_object* v___y_4048_; lean_object* v___y_4049_; lean_object* v___y_4050_; lean_object* v_h_4093_; lean_object* v___y_4094_; lean_object* v___y_4095_; lean_object* v___y_4096_; lean_object* v___y_4097_; lean_object* v___y_4098_; lean_object* v___y_4099_; lean_object* v___y_4100_; lean_object* v___y_4101_; lean_object* v___y_4102_; lean_object* v___y_4103_; lean_object* v___y_4104_; lean_object* v___y_4250_; lean_object* v___y_4251_; lean_object* v___y_4252_; lean_object* v___y_4253_; lean_object* v___y_4254_; lean_object* v___y_4255_; lean_object* v___y_4256_; lean_object* v___y_4257_; lean_object* v___y_4258_; lean_object* v___y_4259_; lean_object* v___y_4260_; uint8_t v___x_4268_; 
v___x_4268_ = lean_unbox(v_a_3971_);
if (v___x_4268_ == 0)
{
lean_object* v___x_4269_; lean_object* v___x_4271_; 
lean_dec(v_a_3971_);
lean_dec_ref(v_he_3850_);
lean_dec_ref(v_e_3849_);
lean_dec_ref(v_c_3848_);
v___x_4269_ = lean_box(0);
if (v_isShared_3974_ == 0)
{
lean_ctor_set(v___x_3973_, 0, v___x_4269_);
v___x_4271_ = v___x_3973_;
goto v_reusejp_4270_;
}
else
{
lean_object* v_reuseFailAlloc_4272_; 
v_reuseFailAlloc_4272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4272_, 0, v___x_4269_);
v___x_4271_ = v_reuseFailAlloc_4272_;
goto v_reusejp_4270_;
}
v_reusejp_4270_:
{
return v___x_4271_;
}
}
else
{
lean_object* v_options_4273_; uint8_t v_hasTrace_4274_; 
lean_del_object(v___x_3973_);
v_options_4273_ = lean_ctor_get(v_a_3860_, 2);
v_hasTrace_4274_ = lean_ctor_get_uint8(v_options_4273_, sizeof(void*)*1);
if (v_hasTrace_4274_ == 0)
{
v___y_4250_ = v_a_3851_;
v___y_4251_ = v_a_3852_;
v___y_4252_ = v_a_3853_;
v___y_4253_ = v_a_3854_;
v___y_4254_ = v_a_3855_;
v___y_4255_ = v_a_3856_;
v___y_4256_ = v_a_3857_;
v___y_4257_ = v_a_3858_;
v___y_4258_ = v_a_3859_;
v___y_4259_ = v_a_3860_;
v___y_4260_ = v_a_3861_;
goto v___jp_4249_;
}
else
{
lean_object* v_inheritedTraceOptions_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; uint8_t v___x_4278_; 
v_inheritedTraceOptions_4275_ = lean_ctor_get(v_a_3860_, 13);
v___x_4276_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__4));
v___x_4277_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5);
v___x_4278_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4275_, v_options_4273_, v___x_4277_);
if (v___x_4278_ == 0)
{
v___y_4250_ = v_a_3851_;
v___y_4251_ = v_a_3852_;
v___y_4252_ = v_a_3853_;
v___y_4253_ = v_a_3854_;
v___y_4254_ = v_a_3855_;
v___y_4255_ = v_a_3856_;
v___y_4256_ = v_a_3857_;
v___y_4257_ = v_a_3858_;
v___y_4258_ = v_a_3859_;
v___y_4259_ = v_a_3860_;
v___y_4260_ = v_a_3861_;
goto v___jp_4249_;
}
else
{
lean_object* v___x_4279_; 
v___x_4279_ = l_Lean_Meta_Grind_Order_Cnstr_pp(v_c_3848_, v_a_3851_, v_a_3852_, v_a_3853_, v_a_3854_, v_a_3855_, v_a_3856_, v_a_3857_, v_a_3858_, v_a_3859_, v_a_3860_, v_a_3861_);
if (lean_obj_tag(v___x_4279_) == 0)
{
lean_object* v_a_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; lean_object* v___x_4283_; 
v_a_4280_ = lean_ctor_get(v___x_4279_, 0);
lean_inc(v_a_4280_);
lean_dec_ref(v___x_4279_);
v___x_4281_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__31, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__31_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__31);
v___x_4282_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4282_, 0, v___x_4281_);
lean_ctor_set(v___x_4282_, 1, v_a_4280_);
v___x_4283_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(v___x_4276_, v___x_4282_, v_a_3858_, v_a_3859_, v_a_3860_, v_a_3861_);
if (lean_obj_tag(v___x_4283_) == 0)
{
lean_dec_ref(v___x_4283_);
v___y_4250_ = v_a_3851_;
v___y_4251_ = v_a_3852_;
v___y_4252_ = v_a_3853_;
v___y_4253_ = v_a_3854_;
v___y_4254_ = v_a_3855_;
v___y_4255_ = v_a_3856_;
v___y_4256_ = v_a_3857_;
v___y_4257_ = v_a_3858_;
v___y_4258_ = v_a_3859_;
v___y_4259_ = v_a_3860_;
v___y_4260_ = v_a_3861_;
goto v___jp_4249_;
}
else
{
lean_dec(v_a_3971_);
lean_dec_ref(v_he_3850_);
lean_dec_ref(v_e_3849_);
lean_dec_ref(v_c_3848_);
return v___x_4283_;
}
}
else
{
lean_object* v_a_4284_; lean_object* v___x_4286_; uint8_t v_isShared_4287_; uint8_t v_isSharedCheck_4291_; 
lean_dec(v_a_3971_);
lean_dec_ref(v_he_3850_);
lean_dec_ref(v_e_3849_);
lean_dec_ref(v_c_3848_);
v_a_4284_ = lean_ctor_get(v___x_4279_, 0);
v_isSharedCheck_4291_ = !lean_is_exclusive(v___x_4279_);
if (v_isSharedCheck_4291_ == 0)
{
v___x_4286_ = v___x_4279_;
v_isShared_4287_ = v_isSharedCheck_4291_;
goto v_resetjp_4285_;
}
else
{
lean_inc(v_a_4284_);
lean_dec(v___x_4279_);
v___x_4286_ = lean_box(0);
v_isShared_4287_ = v_isSharedCheck_4291_;
goto v_resetjp_4285_;
}
v_resetjp_4285_:
{
lean_object* v___x_4289_; 
if (v_isShared_4287_ == 0)
{
v___x_4289_ = v___x_4286_;
goto v_reusejp_4288_;
}
else
{
lean_object* v_reuseFailAlloc_4290_; 
v_reuseFailAlloc_4290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4290_, 0, v_a_4284_);
v___x_4289_ = v_reuseFailAlloc_4290_;
goto v_reusejp_4288_;
}
v_reusejp_4288_:
{
return v___x_4289_;
}
}
}
}
}
}
v___jp_3975_:
{
lean_object* v___x_3997_; lean_object* v___x_3998_; 
v___x_3997_ = l_Lean_eagerReflBoolTrue;
lean_inc_ref(v___y_3996_);
v___x_3998_ = l_Lean_mkApp6(v___y_3994_, v___y_3979_, v___y_3977_, v___y_3995_, v___y_3996_, v___x_3997_, v___y_3986_);
if (v___y_3991_ == 0)
{
uint8_t v___x_3999_; 
v___x_3999_ = lean_unbox(v_a_3971_);
lean_dec(v_a_3971_);
v___y_3907_ = v___y_3976_;
v___y_3908_ = v___x_3997_;
v___y_3909_ = v___y_3978_;
v___y_3910_ = v___y_3980_;
v___y_3911_ = v___y_3981_;
v___y_3912_ = v___y_3982_;
v___y_3913_ = v___y_3983_;
v___y_3914_ = v___y_3984_;
v___y_3915_ = v___x_3998_;
v___y_3916_ = v___y_3987_;
v___y_3917_ = v___y_3985_;
v___y_3918_ = v___y_3988_;
v___y_3919_ = v___y_3996_;
v___y_3920_ = v___y_3989_;
v___y_3921_ = v___y_3990_;
v___y_3922_ = v___y_3992_;
v___y_3923_ = v___y_3993_;
v___y_3924_ = v___x_3999_;
goto v___jp_3906_;
}
else
{
uint8_t v___x_4000_; 
lean_dec(v_a_3971_);
v___x_4000_ = 0;
v___y_3907_ = v___y_3976_;
v___y_3908_ = v___x_3997_;
v___y_3909_ = v___y_3978_;
v___y_3910_ = v___y_3980_;
v___y_3911_ = v___y_3981_;
v___y_3912_ = v___y_3982_;
v___y_3913_ = v___y_3983_;
v___y_3914_ = v___y_3984_;
v___y_3915_ = v___x_3998_;
v___y_3916_ = v___y_3987_;
v___y_3917_ = v___y_3985_;
v___y_3918_ = v___y_3988_;
v___y_3919_ = v___y_3996_;
v___y_3920_ = v___y_3989_;
v___y_3921_ = v___y_3990_;
v___y_3922_ = v___y_3992_;
v___y_3923_ = v___y_3993_;
v___y_3924_ = v___x_4000_;
goto v___jp_3906_;
}
}
v___jp_4001_:
{
lean_object* v___x_4022_; uint8_t v___x_4023_; 
v___x_4022_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4);
v___x_4023_ = lean_int_dec_le(v___x_4022_, v___y_4002_);
if (v___x_4023_ == 0)
{
lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; 
v___x_4024_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10);
v___x_4025_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13);
v___x_4026_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16);
v___x_4027_ = lean_int_neg(v___y_4002_);
v___x_4028_ = l_Int_toNat(v___x_4027_);
lean_dec(v___x_4027_);
v___x_4029_ = l_Lean_instToExprInt_mkNat(v___x_4028_);
v___x_4030_ = l_Lean_mkApp3(v___x_4024_, v___x_4025_, v___x_4026_, v___x_4029_);
v___y_3976_ = v___y_4002_;
v___y_3977_ = v___y_4003_;
v___y_3978_ = v___y_4004_;
v___y_3979_ = v___y_4005_;
v___y_3980_ = v___y_4006_;
v___y_3981_ = v___y_4007_;
v___y_3982_ = v___y_4008_;
v___y_3983_ = v___y_4009_;
v___y_3984_ = v___y_4010_;
v___y_3985_ = v___y_4011_;
v___y_3986_ = v___y_4012_;
v___y_3987_ = v___y_4013_;
v___y_3988_ = v___y_4014_;
v___y_3989_ = v___y_4015_;
v___y_3990_ = v___y_4016_;
v___y_3991_ = v___y_4017_;
v___y_3992_ = v___y_4018_;
v___y_3993_ = v___y_4019_;
v___y_3994_ = v___y_4020_;
v___y_3995_ = v___y_4021_;
v___y_3996_ = v___x_4030_;
goto v___jp_3975_;
}
else
{
lean_object* v___x_4031_; lean_object* v___x_4032_; 
v___x_4031_ = l_Int_toNat(v___y_4002_);
v___x_4032_ = l_Lean_instToExprInt_mkNat(v___x_4031_);
v___y_3976_ = v___y_4002_;
v___y_3977_ = v___y_4003_;
v___y_3978_ = v___y_4004_;
v___y_3979_ = v___y_4005_;
v___y_3980_ = v___y_4006_;
v___y_3981_ = v___y_4007_;
v___y_3982_ = v___y_4008_;
v___y_3983_ = v___y_4009_;
v___y_3984_ = v___y_4010_;
v___y_3985_ = v___y_4011_;
v___y_3986_ = v___y_4012_;
v___y_3987_ = v___y_4013_;
v___y_3988_ = v___y_4014_;
v___y_3989_ = v___y_4015_;
v___y_3990_ = v___y_4016_;
v___y_3991_ = v___y_4017_;
v___y_3992_ = v___y_4018_;
v___y_3993_ = v___y_4019_;
v___y_3994_ = v___y_4020_;
v___y_3995_ = v___y_4021_;
v___y_3996_ = v___x_4032_;
goto v___jp_3975_;
}
}
v___jp_4033_:
{
lean_object* v___x_4051_; 
lean_inc(v___y_4050_);
v___x_4051_ = l_Lean_Meta_Grind_Order_mkLinearOrdRingPrefix(v___y_4050_, v___y_4045_, v___y_4034_, v___y_4048_, v___y_4044_, v___y_4038_, v___y_4049_, v___y_4036_, v___y_4039_, v___y_4043_, v___y_4046_, v___y_4037_);
if (lean_obj_tag(v___x_4051_) == 0)
{
lean_object* v_a_4052_; lean_object* v___x_4053_; 
v_a_4052_ = lean_ctor_get(v___x_4051_, 0);
lean_inc(v_a_4052_);
lean_dec_ref(v___x_4051_);
v___x_4053_ = l_Lean_Meta_Grind_Order_getExpr(v___y_4040_, v___y_4045_, v___y_4034_, v___y_4048_, v___y_4044_, v___y_4038_, v___y_4049_, v___y_4036_, v___y_4039_, v___y_4043_, v___y_4046_, v___y_4037_);
if (lean_obj_tag(v___x_4053_) == 0)
{
lean_object* v_a_4054_; lean_object* v___x_4055_; 
v_a_4054_ = lean_ctor_get(v___x_4053_, 0);
lean_inc(v_a_4054_);
lean_dec_ref(v___x_4053_);
v___x_4055_ = l_Lean_Meta_Grind_Order_getExpr(v___y_4042_, v___y_4045_, v___y_4034_, v___y_4048_, v___y_4044_, v___y_4038_, v___y_4049_, v___y_4036_, v___y_4039_, v___y_4043_, v___y_4046_, v___y_4037_);
if (lean_obj_tag(v___x_4055_) == 0)
{
lean_object* v_a_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; uint8_t v___x_4059_; 
v_a_4056_ = lean_ctor_get(v___x_4055_, 0);
lean_inc(v_a_4056_);
lean_dec_ref(v___x_4055_);
v___x_4057_ = lean_int_neg(v___y_4035_);
v___x_4058_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4);
v___x_4059_ = lean_int_dec_le(v___x_4058_, v___y_4035_);
if (v___x_4059_ == 0)
{
lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; 
lean_dec(v___y_4035_);
v___x_4060_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10);
v___x_4061_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13);
v___x_4062_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16);
v___x_4063_ = l_Int_toNat(v___x_4057_);
v___x_4064_ = l_Lean_instToExprInt_mkNat(v___x_4063_);
v___x_4065_ = l_Lean_mkApp3(v___x_4060_, v___x_4061_, v___x_4062_, v___x_4064_);
v___y_4002_ = v___x_4057_;
v___y_4003_ = v_a_4056_;
v___y_4004_ = v___y_4034_;
v___y_4005_ = v_a_4054_;
v___y_4006_ = v___y_4036_;
v___y_4007_ = v___y_4037_;
v___y_4008_ = v___y_4038_;
v___y_4009_ = v___y_4039_;
v___y_4010_ = v___y_4040_;
v___y_4011_ = v___y_4043_;
v___y_4012_ = v___y_4041_;
v___y_4013_ = v___y_4042_;
v___y_4014_ = v___y_4044_;
v___y_4015_ = v___y_4045_;
v___y_4016_ = v___y_4046_;
v___y_4017_ = v___y_4047_;
v___y_4018_ = v___y_4048_;
v___y_4019_ = v___y_4049_;
v___y_4020_ = v_a_4052_;
v___y_4021_ = v___x_4065_;
goto v___jp_4001_;
}
else
{
lean_object* v___x_4066_; lean_object* v___x_4067_; 
v___x_4066_ = l_Int_toNat(v___y_4035_);
lean_dec(v___y_4035_);
v___x_4067_ = l_Lean_instToExprInt_mkNat(v___x_4066_);
v___y_4002_ = v___x_4057_;
v___y_4003_ = v_a_4056_;
v___y_4004_ = v___y_4034_;
v___y_4005_ = v_a_4054_;
v___y_4006_ = v___y_4036_;
v___y_4007_ = v___y_4037_;
v___y_4008_ = v___y_4038_;
v___y_4009_ = v___y_4039_;
v___y_4010_ = v___y_4040_;
v___y_4011_ = v___y_4043_;
v___y_4012_ = v___y_4041_;
v___y_4013_ = v___y_4042_;
v___y_4014_ = v___y_4044_;
v___y_4015_ = v___y_4045_;
v___y_4016_ = v___y_4046_;
v___y_4017_ = v___y_4047_;
v___y_4018_ = v___y_4048_;
v___y_4019_ = v___y_4049_;
v___y_4020_ = v_a_4052_;
v___y_4021_ = v___x_4067_;
goto v___jp_4001_;
}
}
else
{
lean_object* v_a_4068_; lean_object* v___x_4070_; uint8_t v_isShared_4071_; uint8_t v_isSharedCheck_4075_; 
lean_dec(v_a_4054_);
lean_dec(v_a_4052_);
lean_dec(v___y_4042_);
lean_dec_ref(v___y_4041_);
lean_dec(v___y_4040_);
lean_dec(v___y_4035_);
lean_dec(v_a_3971_);
v_a_4068_ = lean_ctor_get(v___x_4055_, 0);
v_isSharedCheck_4075_ = !lean_is_exclusive(v___x_4055_);
if (v_isSharedCheck_4075_ == 0)
{
v___x_4070_ = v___x_4055_;
v_isShared_4071_ = v_isSharedCheck_4075_;
goto v_resetjp_4069_;
}
else
{
lean_inc(v_a_4068_);
lean_dec(v___x_4055_);
v___x_4070_ = lean_box(0);
v_isShared_4071_ = v_isSharedCheck_4075_;
goto v_resetjp_4069_;
}
v_resetjp_4069_:
{
lean_object* v___x_4073_; 
if (v_isShared_4071_ == 0)
{
v___x_4073_ = v___x_4070_;
goto v_reusejp_4072_;
}
else
{
lean_object* v_reuseFailAlloc_4074_; 
v_reuseFailAlloc_4074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4074_, 0, v_a_4068_);
v___x_4073_ = v_reuseFailAlloc_4074_;
goto v_reusejp_4072_;
}
v_reusejp_4072_:
{
return v___x_4073_;
}
}
}
}
else
{
lean_object* v_a_4076_; lean_object* v___x_4078_; uint8_t v_isShared_4079_; uint8_t v_isSharedCheck_4083_; 
lean_dec(v_a_4052_);
lean_dec(v___y_4042_);
lean_dec_ref(v___y_4041_);
lean_dec(v___y_4040_);
lean_dec(v___y_4035_);
lean_dec(v_a_3971_);
v_a_4076_ = lean_ctor_get(v___x_4053_, 0);
v_isSharedCheck_4083_ = !lean_is_exclusive(v___x_4053_);
if (v_isSharedCheck_4083_ == 0)
{
v___x_4078_ = v___x_4053_;
v_isShared_4079_ = v_isSharedCheck_4083_;
goto v_resetjp_4077_;
}
else
{
lean_inc(v_a_4076_);
lean_dec(v___x_4053_);
v___x_4078_ = lean_box(0);
v_isShared_4079_ = v_isSharedCheck_4083_;
goto v_resetjp_4077_;
}
v_resetjp_4077_:
{
lean_object* v___x_4081_; 
if (v_isShared_4079_ == 0)
{
v___x_4081_ = v___x_4078_;
goto v_reusejp_4080_;
}
else
{
lean_object* v_reuseFailAlloc_4082_; 
v_reuseFailAlloc_4082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4082_, 0, v_a_4076_);
v___x_4081_ = v_reuseFailAlloc_4082_;
goto v_reusejp_4080_;
}
v_reusejp_4080_:
{
return v___x_4081_;
}
}
}
}
else
{
lean_object* v_a_4084_; lean_object* v___x_4086_; uint8_t v_isShared_4087_; uint8_t v_isSharedCheck_4091_; 
lean_dec(v___y_4042_);
lean_dec_ref(v___y_4041_);
lean_dec(v___y_4040_);
lean_dec(v___y_4035_);
lean_dec(v_a_3971_);
v_a_4084_ = lean_ctor_get(v___x_4051_, 0);
v_isSharedCheck_4091_ = !lean_is_exclusive(v___x_4051_);
if (v_isSharedCheck_4091_ == 0)
{
v___x_4086_ = v___x_4051_;
v_isShared_4087_ = v_isSharedCheck_4091_;
goto v_resetjp_4085_;
}
else
{
lean_inc(v_a_4084_);
lean_dec(v___x_4051_);
v___x_4086_ = lean_box(0);
v_isShared_4087_ = v_isSharedCheck_4091_;
goto v_resetjp_4085_;
}
v_resetjp_4085_:
{
lean_object* v___x_4089_; 
if (v_isShared_4087_ == 0)
{
v___x_4089_ = v___x_4086_;
goto v_reusejp_4088_;
}
else
{
lean_object* v_reuseFailAlloc_4090_; 
v_reuseFailAlloc_4090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4090_, 0, v_a_4084_);
v___x_4089_ = v_reuseFailAlloc_4090_;
goto v_reusejp_4088_;
}
v_reusejp_4088_:
{
return v___x_4089_;
}
}
}
}
v___jp_4092_:
{
lean_object* v___x_4105_; 
v___x_4105_ = l_Lean_Meta_Grind_Order_isRing(v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_);
if (lean_obj_tag(v___x_4105_) == 0)
{
lean_object* v_a_4106_; uint8_t v___x_4107_; 
v_a_4106_ = lean_ctor_get(v___x_4105_, 0);
lean_inc(v_a_4106_);
lean_dec_ref(v___x_4105_);
v___x_4107_ = lean_unbox(v_a_4106_);
if (v___x_4107_ == 0)
{
uint8_t v_kind_4108_; 
v_kind_4108_ = lean_ctor_get_uint8(v_c_3848_, sizeof(void*)*5);
if (v_kind_4108_ == 1)
{
lean_object* v_u_4109_; lean_object* v_v_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; 
lean_dec(v_a_3971_);
v_u_4109_ = lean_ctor_get(v_c_3848_, 0);
lean_inc(v_u_4109_);
v_v_4110_ = lean_ctor_get(v_c_3848_, 1);
lean_inc(v_v_4110_);
lean_dec_ref(v_c_3848_);
v___x_4111_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__18));
v___x_4112_ = l_Lean_Meta_Grind_Order_mkLeLtLinearPrefix(v___x_4111_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_);
if (lean_obj_tag(v___x_4112_) == 0)
{
lean_object* v_a_4113_; lean_object* v___x_4114_; 
v_a_4113_ = lean_ctor_get(v___x_4112_, 0);
lean_inc(v_a_4113_);
lean_dec_ref(v___x_4112_);
v___x_4114_ = l_Lean_Meta_Grind_Order_getExpr(v_u_4109_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_);
if (lean_obj_tag(v___x_4114_) == 0)
{
lean_object* v_a_4115_; lean_object* v___x_4116_; 
v_a_4115_ = lean_ctor_get(v___x_4114_, 0);
lean_inc(v_a_4115_);
lean_dec_ref(v___x_4114_);
v___x_4116_ = l_Lean_Meta_Grind_Order_getExpr(v_v_4110_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_);
if (lean_obj_tag(v___x_4116_) == 0)
{
lean_object* v_a_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; uint8_t v___x_4121_; lean_object* v___x_4122_; 
v_a_4117_ = lean_ctor_get(v___x_4116_, 0);
lean_inc(v_a_4117_);
lean_dec_ref(v___x_4116_);
v___x_4118_ = l_Lean_mkApp3(v_a_4113_, v_a_4115_, v_a_4117_, v_h_4093_);
v___x_4119_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4);
v___x_4120_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4120_, 0, v___x_4119_);
v___x_4121_ = lean_unbox(v_a_4106_);
lean_dec(v_a_4106_);
lean_ctor_set_uint8(v___x_4120_, sizeof(void*)*1, v___x_4121_);
v___x_4122_ = l_Lean_Meta_Grind_Order_addEdge(v_v_4110_, v_u_4109_, v___x_4120_, v___x_4118_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_);
return v___x_4122_;
}
else
{
lean_object* v_a_4123_; lean_object* v___x_4125_; uint8_t v_isShared_4126_; uint8_t v_isSharedCheck_4130_; 
lean_dec(v_a_4115_);
lean_dec(v_a_4113_);
lean_dec(v_v_4110_);
lean_dec(v_u_4109_);
lean_dec(v_a_4106_);
lean_dec_ref(v_h_4093_);
v_a_4123_ = lean_ctor_get(v___x_4116_, 0);
v_isSharedCheck_4130_ = !lean_is_exclusive(v___x_4116_);
if (v_isSharedCheck_4130_ == 0)
{
v___x_4125_ = v___x_4116_;
v_isShared_4126_ = v_isSharedCheck_4130_;
goto v_resetjp_4124_;
}
else
{
lean_inc(v_a_4123_);
lean_dec(v___x_4116_);
v___x_4125_ = lean_box(0);
v_isShared_4126_ = v_isSharedCheck_4130_;
goto v_resetjp_4124_;
}
v_resetjp_4124_:
{
lean_object* v___x_4128_; 
if (v_isShared_4126_ == 0)
{
v___x_4128_ = v___x_4125_;
goto v_reusejp_4127_;
}
else
{
lean_object* v_reuseFailAlloc_4129_; 
v_reuseFailAlloc_4129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4129_, 0, v_a_4123_);
v___x_4128_ = v_reuseFailAlloc_4129_;
goto v_reusejp_4127_;
}
v_reusejp_4127_:
{
return v___x_4128_;
}
}
}
}
else
{
lean_object* v_a_4131_; lean_object* v___x_4133_; uint8_t v_isShared_4134_; uint8_t v_isSharedCheck_4138_; 
lean_dec(v_a_4113_);
lean_dec(v_v_4110_);
lean_dec(v_u_4109_);
lean_dec(v_a_4106_);
lean_dec_ref(v_h_4093_);
v_a_4131_ = lean_ctor_get(v___x_4114_, 0);
v_isSharedCheck_4138_ = !lean_is_exclusive(v___x_4114_);
if (v_isSharedCheck_4138_ == 0)
{
v___x_4133_ = v___x_4114_;
v_isShared_4134_ = v_isSharedCheck_4138_;
goto v_resetjp_4132_;
}
else
{
lean_inc(v_a_4131_);
lean_dec(v___x_4114_);
v___x_4133_ = lean_box(0);
v_isShared_4134_ = v_isSharedCheck_4138_;
goto v_resetjp_4132_;
}
v_resetjp_4132_:
{
lean_object* v___x_4136_; 
if (v_isShared_4134_ == 0)
{
v___x_4136_ = v___x_4133_;
goto v_reusejp_4135_;
}
else
{
lean_object* v_reuseFailAlloc_4137_; 
v_reuseFailAlloc_4137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4137_, 0, v_a_4131_);
v___x_4136_ = v_reuseFailAlloc_4137_;
goto v_reusejp_4135_;
}
v_reusejp_4135_:
{
return v___x_4136_;
}
}
}
}
else
{
lean_object* v_a_4139_; lean_object* v___x_4141_; uint8_t v_isShared_4142_; uint8_t v_isSharedCheck_4146_; 
lean_dec(v_v_4110_);
lean_dec(v_u_4109_);
lean_dec(v_a_4106_);
lean_dec_ref(v_h_4093_);
v_a_4139_ = lean_ctor_get(v___x_4112_, 0);
v_isSharedCheck_4146_ = !lean_is_exclusive(v___x_4112_);
if (v_isSharedCheck_4146_ == 0)
{
v___x_4141_ = v___x_4112_;
v_isShared_4142_ = v_isSharedCheck_4146_;
goto v_resetjp_4140_;
}
else
{
lean_inc(v_a_4139_);
lean_dec(v___x_4112_);
v___x_4141_ = lean_box(0);
v_isShared_4142_ = v_isSharedCheck_4146_;
goto v_resetjp_4140_;
}
v_resetjp_4140_:
{
lean_object* v___x_4144_; 
if (v_isShared_4142_ == 0)
{
v___x_4144_ = v___x_4141_;
goto v_reusejp_4143_;
}
else
{
lean_object* v_reuseFailAlloc_4145_; 
v_reuseFailAlloc_4145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4145_, 0, v_a_4139_);
v___x_4144_ = v_reuseFailAlloc_4145_;
goto v_reusejp_4143_;
}
v_reusejp_4143_:
{
return v___x_4144_;
}
}
}
}
else
{
lean_object* v_u_4147_; lean_object* v_v_4148_; lean_object* v___x_4149_; 
lean_dec(v_a_4106_);
v_u_4147_ = lean_ctor_get(v_c_3848_, 0);
lean_inc(v_u_4147_);
v_v_4148_ = lean_ctor_get(v_c_3848_, 1);
lean_inc(v_v_4148_);
lean_dec_ref(v_c_3848_);
v___x_4149_ = l_Lean_Meta_Grind_Order_hasLt(v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_);
if (lean_obj_tag(v___x_4149_) == 0)
{
lean_object* v_a_4150_; uint8_t v___x_4151_; 
v_a_4150_ = lean_ctor_get(v___x_4149_, 0);
lean_inc(v_a_4150_);
lean_dec_ref(v___x_4149_);
v___x_4151_ = lean_unbox(v_a_4150_);
if (v___x_4151_ == 0)
{
lean_object* v___x_4152_; lean_object* v___x_4153_; 
lean_dec(v_a_3971_);
v___x_4152_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__20));
v___x_4153_ = l_Lean_Meta_Grind_Order_mkLeLinearPrefix(v___x_4152_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_);
if (lean_obj_tag(v___x_4153_) == 0)
{
lean_object* v_a_4154_; lean_object* v___x_4155_; 
v_a_4154_ = lean_ctor_get(v___x_4153_, 0);
lean_inc(v_a_4154_);
lean_dec_ref(v___x_4153_);
v___x_4155_ = l_Lean_Meta_Grind_Order_getExpr(v_u_4147_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_);
if (lean_obj_tag(v___x_4155_) == 0)
{
lean_object* v_a_4156_; lean_object* v___x_4157_; 
v_a_4156_ = lean_ctor_get(v___x_4155_, 0);
lean_inc(v_a_4156_);
lean_dec_ref(v___x_4155_);
v___x_4157_ = l_Lean_Meta_Grind_Order_getExpr(v_v_4148_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_);
if (lean_obj_tag(v___x_4157_) == 0)
{
lean_object* v_a_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; uint8_t v___x_4162_; lean_object* v___x_4163_; 
v_a_4158_ = lean_ctor_get(v___x_4157_, 0);
lean_inc(v_a_4158_);
lean_dec_ref(v___x_4157_);
v___x_4159_ = l_Lean_mkApp3(v_a_4154_, v_a_4156_, v_a_4158_, v_h_4093_);
v___x_4160_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4);
v___x_4161_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4161_, 0, v___x_4160_);
v___x_4162_ = lean_unbox(v_a_4150_);
lean_dec(v_a_4150_);
lean_ctor_set_uint8(v___x_4161_, sizeof(void*)*1, v___x_4162_);
v___x_4163_ = l_Lean_Meta_Grind_Order_addEdge(v_v_4148_, v_u_4147_, v___x_4161_, v___x_4159_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_);
return v___x_4163_;
}
else
{
lean_object* v_a_4164_; lean_object* v___x_4166_; uint8_t v_isShared_4167_; uint8_t v_isSharedCheck_4171_; 
lean_dec(v_a_4156_);
lean_dec(v_a_4154_);
lean_dec(v_a_4150_);
lean_dec(v_v_4148_);
lean_dec(v_u_4147_);
lean_dec_ref(v_h_4093_);
v_a_4164_ = lean_ctor_get(v___x_4157_, 0);
v_isSharedCheck_4171_ = !lean_is_exclusive(v___x_4157_);
if (v_isSharedCheck_4171_ == 0)
{
v___x_4166_ = v___x_4157_;
v_isShared_4167_ = v_isSharedCheck_4171_;
goto v_resetjp_4165_;
}
else
{
lean_inc(v_a_4164_);
lean_dec(v___x_4157_);
v___x_4166_ = lean_box(0);
v_isShared_4167_ = v_isSharedCheck_4171_;
goto v_resetjp_4165_;
}
v_resetjp_4165_:
{
lean_object* v___x_4169_; 
if (v_isShared_4167_ == 0)
{
v___x_4169_ = v___x_4166_;
goto v_reusejp_4168_;
}
else
{
lean_object* v_reuseFailAlloc_4170_; 
v_reuseFailAlloc_4170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4170_, 0, v_a_4164_);
v___x_4169_ = v_reuseFailAlloc_4170_;
goto v_reusejp_4168_;
}
v_reusejp_4168_:
{
return v___x_4169_;
}
}
}
}
else
{
lean_object* v_a_4172_; lean_object* v___x_4174_; uint8_t v_isShared_4175_; uint8_t v_isSharedCheck_4179_; 
lean_dec(v_a_4154_);
lean_dec(v_a_4150_);
lean_dec(v_v_4148_);
lean_dec(v_u_4147_);
lean_dec_ref(v_h_4093_);
v_a_4172_ = lean_ctor_get(v___x_4155_, 0);
v_isSharedCheck_4179_ = !lean_is_exclusive(v___x_4155_);
if (v_isSharedCheck_4179_ == 0)
{
v___x_4174_ = v___x_4155_;
v_isShared_4175_ = v_isSharedCheck_4179_;
goto v_resetjp_4173_;
}
else
{
lean_inc(v_a_4172_);
lean_dec(v___x_4155_);
v___x_4174_ = lean_box(0);
v_isShared_4175_ = v_isSharedCheck_4179_;
goto v_resetjp_4173_;
}
v_resetjp_4173_:
{
lean_object* v___x_4177_; 
if (v_isShared_4175_ == 0)
{
v___x_4177_ = v___x_4174_;
goto v_reusejp_4176_;
}
else
{
lean_object* v_reuseFailAlloc_4178_; 
v_reuseFailAlloc_4178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4178_, 0, v_a_4172_);
v___x_4177_ = v_reuseFailAlloc_4178_;
goto v_reusejp_4176_;
}
v_reusejp_4176_:
{
return v___x_4177_;
}
}
}
}
else
{
lean_object* v_a_4180_; lean_object* v___x_4182_; uint8_t v_isShared_4183_; uint8_t v_isSharedCheck_4187_; 
lean_dec(v_a_4150_);
lean_dec(v_v_4148_);
lean_dec(v_u_4147_);
lean_dec_ref(v_h_4093_);
v_a_4180_ = lean_ctor_get(v___x_4153_, 0);
v_isSharedCheck_4187_ = !lean_is_exclusive(v___x_4153_);
if (v_isSharedCheck_4187_ == 0)
{
v___x_4182_ = v___x_4153_;
v_isShared_4183_ = v_isSharedCheck_4187_;
goto v_resetjp_4181_;
}
else
{
lean_inc(v_a_4180_);
lean_dec(v___x_4153_);
v___x_4182_ = lean_box(0);
v_isShared_4183_ = v_isSharedCheck_4187_;
goto v_resetjp_4181_;
}
v_resetjp_4181_:
{
lean_object* v___x_4185_; 
if (v_isShared_4183_ == 0)
{
v___x_4185_ = v___x_4182_;
goto v_reusejp_4184_;
}
else
{
lean_object* v_reuseFailAlloc_4186_; 
v_reuseFailAlloc_4186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4186_, 0, v_a_4180_);
v___x_4185_ = v_reuseFailAlloc_4186_;
goto v_reusejp_4184_;
}
v_reusejp_4184_:
{
return v___x_4185_;
}
}
}
}
else
{
lean_object* v___x_4188_; lean_object* v___x_4189_; 
lean_dec(v_a_4150_);
v___x_4188_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__22));
v___x_4189_ = l_Lean_Meta_Grind_Order_mkLeLtLinearPrefix(v___x_4188_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_);
if (lean_obj_tag(v___x_4189_) == 0)
{
lean_object* v_a_4190_; lean_object* v___x_4191_; 
v_a_4190_ = lean_ctor_get(v___x_4189_, 0);
lean_inc(v_a_4190_);
lean_dec_ref(v___x_4189_);
v___x_4191_ = l_Lean_Meta_Grind_Order_getExpr(v_u_4147_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_);
if (lean_obj_tag(v___x_4191_) == 0)
{
lean_object* v_a_4192_; lean_object* v___x_4193_; 
v_a_4192_ = lean_ctor_get(v___x_4191_, 0);
lean_inc(v_a_4192_);
lean_dec_ref(v___x_4191_);
v___x_4193_ = l_Lean_Meta_Grind_Order_getExpr(v_v_4148_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_);
if (lean_obj_tag(v___x_4193_) == 0)
{
lean_object* v_a_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; uint8_t v___x_4198_; lean_object* v___x_4199_; 
v_a_4194_ = lean_ctor_get(v___x_4193_, 0);
lean_inc(v_a_4194_);
lean_dec_ref(v___x_4193_);
v___x_4195_ = l_Lean_mkApp3(v_a_4190_, v_a_4192_, v_a_4194_, v_h_4093_);
v___x_4196_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4);
v___x_4197_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4197_, 0, v___x_4196_);
v___x_4198_ = lean_unbox(v_a_3971_);
lean_dec(v_a_3971_);
lean_ctor_set_uint8(v___x_4197_, sizeof(void*)*1, v___x_4198_);
v___x_4199_ = l_Lean_Meta_Grind_Order_addEdge(v_v_4148_, v_u_4147_, v___x_4197_, v___x_4195_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_);
return v___x_4199_;
}
else
{
lean_object* v_a_4200_; lean_object* v___x_4202_; uint8_t v_isShared_4203_; uint8_t v_isSharedCheck_4207_; 
lean_dec(v_a_4192_);
lean_dec(v_a_4190_);
lean_dec(v_v_4148_);
lean_dec(v_u_4147_);
lean_dec_ref(v_h_4093_);
lean_dec(v_a_3971_);
v_a_4200_ = lean_ctor_get(v___x_4193_, 0);
v_isSharedCheck_4207_ = !lean_is_exclusive(v___x_4193_);
if (v_isSharedCheck_4207_ == 0)
{
v___x_4202_ = v___x_4193_;
v_isShared_4203_ = v_isSharedCheck_4207_;
goto v_resetjp_4201_;
}
else
{
lean_inc(v_a_4200_);
lean_dec(v___x_4193_);
v___x_4202_ = lean_box(0);
v_isShared_4203_ = v_isSharedCheck_4207_;
goto v_resetjp_4201_;
}
v_resetjp_4201_:
{
lean_object* v___x_4205_; 
if (v_isShared_4203_ == 0)
{
v___x_4205_ = v___x_4202_;
goto v_reusejp_4204_;
}
else
{
lean_object* v_reuseFailAlloc_4206_; 
v_reuseFailAlloc_4206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4206_, 0, v_a_4200_);
v___x_4205_ = v_reuseFailAlloc_4206_;
goto v_reusejp_4204_;
}
v_reusejp_4204_:
{
return v___x_4205_;
}
}
}
}
else
{
lean_object* v_a_4208_; lean_object* v___x_4210_; uint8_t v_isShared_4211_; uint8_t v_isSharedCheck_4215_; 
lean_dec(v_a_4190_);
lean_dec(v_v_4148_);
lean_dec(v_u_4147_);
lean_dec_ref(v_h_4093_);
lean_dec(v_a_3971_);
v_a_4208_ = lean_ctor_get(v___x_4191_, 0);
v_isSharedCheck_4215_ = !lean_is_exclusive(v___x_4191_);
if (v_isSharedCheck_4215_ == 0)
{
v___x_4210_ = v___x_4191_;
v_isShared_4211_ = v_isSharedCheck_4215_;
goto v_resetjp_4209_;
}
else
{
lean_inc(v_a_4208_);
lean_dec(v___x_4191_);
v___x_4210_ = lean_box(0);
v_isShared_4211_ = v_isSharedCheck_4215_;
goto v_resetjp_4209_;
}
v_resetjp_4209_:
{
lean_object* v___x_4213_; 
if (v_isShared_4211_ == 0)
{
v___x_4213_ = v___x_4210_;
goto v_reusejp_4212_;
}
else
{
lean_object* v_reuseFailAlloc_4214_; 
v_reuseFailAlloc_4214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4214_, 0, v_a_4208_);
v___x_4213_ = v_reuseFailAlloc_4214_;
goto v_reusejp_4212_;
}
v_reusejp_4212_:
{
return v___x_4213_;
}
}
}
}
else
{
lean_object* v_a_4216_; lean_object* v___x_4218_; uint8_t v_isShared_4219_; uint8_t v_isSharedCheck_4223_; 
lean_dec(v_v_4148_);
lean_dec(v_u_4147_);
lean_dec_ref(v_h_4093_);
lean_dec(v_a_3971_);
v_a_4216_ = lean_ctor_get(v___x_4189_, 0);
v_isSharedCheck_4223_ = !lean_is_exclusive(v___x_4189_);
if (v_isSharedCheck_4223_ == 0)
{
v___x_4218_ = v___x_4189_;
v_isShared_4219_ = v_isSharedCheck_4223_;
goto v_resetjp_4217_;
}
else
{
lean_inc(v_a_4216_);
lean_dec(v___x_4189_);
v___x_4218_ = lean_box(0);
v_isShared_4219_ = v_isSharedCheck_4223_;
goto v_resetjp_4217_;
}
v_resetjp_4217_:
{
lean_object* v___x_4221_; 
if (v_isShared_4219_ == 0)
{
v___x_4221_ = v___x_4218_;
goto v_reusejp_4220_;
}
else
{
lean_object* v_reuseFailAlloc_4222_; 
v_reuseFailAlloc_4222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4222_, 0, v_a_4216_);
v___x_4221_ = v_reuseFailAlloc_4222_;
goto v_reusejp_4220_;
}
v_reusejp_4220_:
{
return v___x_4221_;
}
}
}
}
}
else
{
lean_object* v_a_4224_; lean_object* v___x_4226_; uint8_t v_isShared_4227_; uint8_t v_isSharedCheck_4231_; 
lean_dec(v_v_4148_);
lean_dec(v_u_4147_);
lean_dec_ref(v_h_4093_);
lean_dec(v_a_3971_);
v_a_4224_ = lean_ctor_get(v___x_4149_, 0);
v_isSharedCheck_4231_ = !lean_is_exclusive(v___x_4149_);
if (v_isSharedCheck_4231_ == 0)
{
v___x_4226_ = v___x_4149_;
v_isShared_4227_ = v_isSharedCheck_4231_;
goto v_resetjp_4225_;
}
else
{
lean_inc(v_a_4224_);
lean_dec(v___x_4149_);
v___x_4226_ = lean_box(0);
v_isShared_4227_ = v_isSharedCheck_4231_;
goto v_resetjp_4225_;
}
v_resetjp_4225_:
{
lean_object* v___x_4229_; 
if (v_isShared_4227_ == 0)
{
v___x_4229_ = v___x_4226_;
goto v_reusejp_4228_;
}
else
{
lean_object* v_reuseFailAlloc_4230_; 
v_reuseFailAlloc_4230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4230_, 0, v_a_4224_);
v___x_4229_ = v_reuseFailAlloc_4230_;
goto v_reusejp_4228_;
}
v_reusejp_4228_:
{
return v___x_4229_;
}
}
}
}
}
else
{
uint8_t v_kind_4232_; 
lean_dec(v_a_4106_);
v_kind_4232_ = lean_ctor_get_uint8(v_c_3848_, sizeof(void*)*5);
if (v_kind_4232_ == 1)
{
lean_object* v_u_4233_; lean_object* v_v_4234_; lean_object* v_k_4235_; lean_object* v___x_4236_; 
v_u_4233_ = lean_ctor_get(v_c_3848_, 0);
lean_inc(v_u_4233_);
v_v_4234_ = lean_ctor_get(v_c_3848_, 1);
lean_inc(v_v_4234_);
v_k_4235_ = lean_ctor_get(v_c_3848_, 2);
lean_inc(v_k_4235_);
lean_dec_ref(v_c_3848_);
v___x_4236_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__24));
v___y_4034_ = v___y_4095_;
v___y_4035_ = v_k_4235_;
v___y_4036_ = v___y_4100_;
v___y_4037_ = v___y_4104_;
v___y_4038_ = v___y_4098_;
v___y_4039_ = v___y_4101_;
v___y_4040_ = v_u_4233_;
v___y_4041_ = v_h_4093_;
v___y_4042_ = v_v_4234_;
v___y_4043_ = v___y_4102_;
v___y_4044_ = v___y_4097_;
v___y_4045_ = v___y_4094_;
v___y_4046_ = v___y_4103_;
v___y_4047_ = v_kind_4232_;
v___y_4048_ = v___y_4096_;
v___y_4049_ = v___y_4099_;
v___y_4050_ = v___x_4236_;
goto v___jp_4033_;
}
else
{
lean_object* v_u_4237_; lean_object* v_v_4238_; lean_object* v_k_4239_; lean_object* v___x_4240_; 
v_u_4237_ = lean_ctor_get(v_c_3848_, 0);
lean_inc(v_u_4237_);
v_v_4238_ = lean_ctor_get(v_c_3848_, 1);
lean_inc(v_v_4238_);
v_k_4239_ = lean_ctor_get(v_c_3848_, 2);
lean_inc(v_k_4239_);
lean_dec_ref(v_c_3848_);
v___x_4240_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__26));
v___y_4034_ = v___y_4095_;
v___y_4035_ = v_k_4239_;
v___y_4036_ = v___y_4100_;
v___y_4037_ = v___y_4104_;
v___y_4038_ = v___y_4098_;
v___y_4039_ = v___y_4101_;
v___y_4040_ = v_u_4237_;
v___y_4041_ = v_h_4093_;
v___y_4042_ = v_v_4238_;
v___y_4043_ = v___y_4102_;
v___y_4044_ = v___y_4097_;
v___y_4045_ = v___y_4094_;
v___y_4046_ = v___y_4103_;
v___y_4047_ = v_kind_4232_;
v___y_4048_ = v___y_4096_;
v___y_4049_ = v___y_4099_;
v___y_4050_ = v___x_4240_;
goto v___jp_4033_;
}
}
}
else
{
lean_object* v_a_4241_; lean_object* v___x_4243_; uint8_t v_isShared_4244_; uint8_t v_isSharedCheck_4248_; 
lean_dec_ref(v_h_4093_);
lean_dec(v_a_3971_);
lean_dec_ref(v_c_3848_);
v_a_4241_ = lean_ctor_get(v___x_4105_, 0);
v_isSharedCheck_4248_ = !lean_is_exclusive(v___x_4105_);
if (v_isSharedCheck_4248_ == 0)
{
v___x_4243_ = v___x_4105_;
v_isShared_4244_ = v_isSharedCheck_4248_;
goto v_resetjp_4242_;
}
else
{
lean_inc(v_a_4241_);
lean_dec(v___x_4105_);
v___x_4243_ = lean_box(0);
v_isShared_4244_ = v_isSharedCheck_4248_;
goto v_resetjp_4242_;
}
v_resetjp_4242_:
{
lean_object* v___x_4246_; 
if (v_isShared_4244_ == 0)
{
v___x_4246_ = v___x_4243_;
goto v_reusejp_4245_;
}
else
{
lean_object* v_reuseFailAlloc_4247_; 
v_reuseFailAlloc_4247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4247_, 0, v_a_4241_);
v___x_4246_ = v_reuseFailAlloc_4247_;
goto v_reusejp_4245_;
}
v_reusejp_4245_:
{
return v___x_4246_;
}
}
}
}
v___jp_4249_:
{
lean_object* v_h_x3f_4261_; 
v_h_x3f_4261_ = lean_ctor_get(v_c_3848_, 4);
if (lean_obj_tag(v_h_x3f_4261_) == 1)
{
lean_object* v_e_4262_; lean_object* v_val_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; 
v_e_4262_ = lean_ctor_get(v_c_3848_, 3);
v_val_4263_ = lean_ctor_get(v_h_x3f_4261_, 0);
v___x_4264_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__29, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__29_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__29);
lean_inc_ref(v_e_3849_);
v___x_4265_ = l_Lean_Meta_mkOfEqFalseCore(v_e_3849_, v_he_3850_);
lean_inc(v_val_4263_);
lean_inc_ref(v_e_4262_);
v___x_4266_ = l_Lean_mkApp4(v___x_4264_, v_e_3849_, v_e_4262_, v_val_4263_, v___x_4265_);
v_h_4093_ = v___x_4266_;
v___y_4094_ = v___y_4250_;
v___y_4095_ = v___y_4251_;
v___y_4096_ = v___y_4252_;
v___y_4097_ = v___y_4253_;
v___y_4098_ = v___y_4254_;
v___y_4099_ = v___y_4255_;
v___y_4100_ = v___y_4256_;
v___y_4101_ = v___y_4257_;
v___y_4102_ = v___y_4258_;
v___y_4103_ = v___y_4259_;
v___y_4104_ = v___y_4260_;
goto v___jp_4092_;
}
else
{
lean_object* v___x_4267_; 
v___x_4267_ = l_Lean_Meta_mkOfEqFalseCore(v_e_3849_, v_he_3850_);
v_h_4093_ = v___x_4267_;
v___y_4094_ = v___y_4250_;
v___y_4095_ = v___y_4251_;
v___y_4096_ = v___y_4252_;
v___y_4097_ = v___y_4253_;
v___y_4098_ = v___y_4254_;
v___y_4099_ = v___y_4255_;
v___y_4100_ = v___y_4256_;
v___y_4101_ = v___y_4257_;
v___y_4102_ = v___y_4258_;
v___y_4103_ = v___y_4259_;
v___y_4104_ = v___y_4260_;
goto v___jp_4092_;
}
}
}
}
else
{
lean_object* v_a_4293_; lean_object* v___x_4295_; uint8_t v_isShared_4296_; uint8_t v_isSharedCheck_4300_; 
lean_dec_ref(v_he_3850_);
lean_dec_ref(v_e_3849_);
lean_dec_ref(v_c_3848_);
v_a_4293_ = lean_ctor_get(v___x_3970_, 0);
v_isSharedCheck_4300_ = !lean_is_exclusive(v___x_3970_);
if (v_isSharedCheck_4300_ == 0)
{
v___x_4295_ = v___x_3970_;
v_isShared_4296_ = v_isSharedCheck_4300_;
goto v_resetjp_4294_;
}
else
{
lean_inc(v_a_4293_);
lean_dec(v___x_3970_);
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
v___jp_3863_:
{
lean_object* v___x_3880_; lean_object* v___x_3881_; 
v___x_3880_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3880_, 0, v_k_x27_3866_);
lean_ctor_set_uint8(v___x_3880_, sizeof(void*)*1, v_strict_3868_);
v___x_3881_ = l_Lean_Meta_Grind_Order_addEdge(v___y_3865_, v___y_3864_, v___x_3880_, v_h_3867_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_, v___y_3875_, v___y_3876_, v___y_3877_, v___y_3878_, v___y_3879_);
return v___x_3881_;
}
v___jp_3882_:
{
lean_object* v___x_3904_; uint8_t v___x_3905_; 
lean_inc_ref(v___y_3895_);
v___x_3904_ = l_Lean_mkApp6(v___y_3895_, v___y_3899_, v___y_3900_, v___y_3896_, v___y_3903_, v___y_3883_, v___y_3890_);
v___x_3905_ = 0;
v___y_3864_ = v___y_3889_;
v___y_3865_ = v___y_3891_;
v_k_x27_3866_ = v___y_3893_;
v_h_3867_ = v___x_3904_;
v_strict_3868_ = v___x_3905_;
v___y_3869_ = v___y_3897_;
v___y_3870_ = v___y_3884_;
v___y_3871_ = v___y_3901_;
v___y_3872_ = v___y_3894_;
v___y_3873_ = v___y_3888_;
v___y_3874_ = v___y_3902_;
v___y_3875_ = v___y_3886_;
v___y_3876_ = v___y_3887_;
v___y_3877_ = v___y_3892_;
v___y_3878_ = v___y_3898_;
v___y_3879_ = v___y_3885_;
goto v___jp_3863_;
}
v___jp_3906_:
{
lean_object* v___x_3925_; 
v___x_3925_ = l_Lean_Meta_Grind_Order_isInt(v___y_3920_, v___y_3909_, v___y_3922_, v___y_3918_, v___y_3912_, v___y_3923_, v___y_3910_, v___y_3913_, v___y_3917_, v___y_3921_, v___y_3911_);
if (lean_obj_tag(v___x_3925_) == 0)
{
lean_object* v_a_3926_; uint8_t v___x_3927_; 
v_a_3926_ = lean_ctor_get(v___x_3925_, 0);
lean_inc(v_a_3926_);
lean_dec_ref(v___x_3925_);
v___x_3927_ = lean_unbox(v_a_3926_);
lean_dec(v_a_3926_);
if (v___x_3927_ == 0)
{
lean_dec_ref(v___y_3919_);
lean_dec_ref(v___y_3908_);
v___y_3864_ = v___y_3914_;
v___y_3865_ = v___y_3916_;
v_k_x27_3866_ = v___y_3907_;
v_h_3867_ = v___y_3915_;
v_strict_3868_ = v___y_3924_;
v___y_3869_ = v___y_3920_;
v___y_3870_ = v___y_3909_;
v___y_3871_ = v___y_3922_;
v___y_3872_ = v___y_3918_;
v___y_3873_ = v___y_3912_;
v___y_3874_ = v___y_3923_;
v___y_3875_ = v___y_3910_;
v___y_3876_ = v___y_3913_;
v___y_3877_ = v___y_3917_;
v___y_3878_ = v___y_3921_;
v___y_3879_ = v___y_3911_;
goto v___jp_3863_;
}
else
{
if (v___y_3924_ == 0)
{
lean_dec_ref(v___y_3919_);
lean_dec_ref(v___y_3908_);
v___y_3864_ = v___y_3914_;
v___y_3865_ = v___y_3916_;
v_k_x27_3866_ = v___y_3907_;
v_h_3867_ = v___y_3915_;
v_strict_3868_ = v___y_3924_;
v___y_3869_ = v___y_3920_;
v___y_3870_ = v___y_3909_;
v___y_3871_ = v___y_3922_;
v___y_3872_ = v___y_3918_;
v___y_3873_ = v___y_3912_;
v___y_3874_ = v___y_3923_;
v___y_3875_ = v___y_3910_;
v___y_3876_ = v___y_3913_;
v___y_3877_ = v___y_3917_;
v___y_3878_ = v___y_3921_;
v___y_3879_ = v___y_3911_;
goto v___jp_3863_;
}
else
{
lean_object* v___x_3928_; 
v___x_3928_ = l_Lean_Meta_Grind_Order_getExpr(v___y_3916_, v___y_3920_, v___y_3909_, v___y_3922_, v___y_3918_, v___y_3912_, v___y_3923_, v___y_3910_, v___y_3913_, v___y_3917_, v___y_3921_, v___y_3911_);
if (lean_obj_tag(v___x_3928_) == 0)
{
lean_object* v_a_3929_; lean_object* v___x_3930_; 
v_a_3929_ = lean_ctor_get(v___x_3928_, 0);
lean_inc(v_a_3929_);
lean_dec_ref(v___x_3928_);
v___x_3930_ = l_Lean_Meta_Grind_Order_getExpr(v___y_3914_, v___y_3920_, v___y_3909_, v___y_3922_, v___y_3918_, v___y_3912_, v___y_3923_, v___y_3910_, v___y_3913_, v___y_3917_, v___y_3921_, v___y_3911_);
if (lean_obj_tag(v___x_3930_) == 0)
{
lean_object* v_a_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; uint8_t v___x_3936_; 
v_a_3931_ = lean_ctor_get(v___x_3930_, 0);
lean_inc(v_a_3931_);
lean_dec_ref(v___x_3930_);
v___x_3932_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__2, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__2);
v___x_3933_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__3);
v___x_3934_ = lean_int_sub(v___y_3907_, v___x_3933_);
lean_dec(v___y_3907_);
v___x_3935_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4);
v___x_3936_ = lean_int_dec_le(v___x_3935_, v___x_3934_);
if (v___x_3936_ == 0)
{
lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; 
v___x_3937_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10);
v___x_3938_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13);
v___x_3939_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16);
v___x_3940_ = lean_int_neg(v___x_3934_);
v___x_3941_ = l_Int_toNat(v___x_3940_);
lean_dec(v___x_3940_);
v___x_3942_ = l_Lean_instToExprInt_mkNat(v___x_3941_);
v___x_3943_ = l_Lean_mkApp3(v___x_3937_, v___x_3938_, v___x_3939_, v___x_3942_);
v___y_3883_ = v___y_3908_;
v___y_3884_ = v___y_3909_;
v___y_3885_ = v___y_3911_;
v___y_3886_ = v___y_3910_;
v___y_3887_ = v___y_3913_;
v___y_3888_ = v___y_3912_;
v___y_3889_ = v___y_3914_;
v___y_3890_ = v___y_3915_;
v___y_3891_ = v___y_3916_;
v___y_3892_ = v___y_3917_;
v___y_3893_ = v___x_3934_;
v___y_3894_ = v___y_3918_;
v___y_3895_ = v___x_3932_;
v___y_3896_ = v___y_3919_;
v___y_3897_ = v___y_3920_;
v___y_3898_ = v___y_3921_;
v___y_3899_ = v_a_3929_;
v___y_3900_ = v_a_3931_;
v___y_3901_ = v___y_3922_;
v___y_3902_ = v___y_3923_;
v___y_3903_ = v___x_3943_;
goto v___jp_3882_;
}
else
{
lean_object* v___x_3944_; lean_object* v___x_3945_; 
v___x_3944_ = l_Int_toNat(v___x_3934_);
v___x_3945_ = l_Lean_instToExprInt_mkNat(v___x_3944_);
v___y_3883_ = v___y_3908_;
v___y_3884_ = v___y_3909_;
v___y_3885_ = v___y_3911_;
v___y_3886_ = v___y_3910_;
v___y_3887_ = v___y_3913_;
v___y_3888_ = v___y_3912_;
v___y_3889_ = v___y_3914_;
v___y_3890_ = v___y_3915_;
v___y_3891_ = v___y_3916_;
v___y_3892_ = v___y_3917_;
v___y_3893_ = v___x_3934_;
v___y_3894_ = v___y_3918_;
v___y_3895_ = v___x_3932_;
v___y_3896_ = v___y_3919_;
v___y_3897_ = v___y_3920_;
v___y_3898_ = v___y_3921_;
v___y_3899_ = v_a_3929_;
v___y_3900_ = v_a_3931_;
v___y_3901_ = v___y_3922_;
v___y_3902_ = v___y_3923_;
v___y_3903_ = v___x_3945_;
goto v___jp_3882_;
}
}
else
{
lean_object* v_a_3946_; lean_object* v___x_3948_; uint8_t v_isShared_3949_; uint8_t v_isSharedCheck_3953_; 
lean_dec(v_a_3929_);
lean_dec_ref(v___y_3919_);
lean_dec(v___y_3916_);
lean_dec_ref(v___y_3915_);
lean_dec(v___y_3914_);
lean_dec_ref(v___y_3908_);
lean_dec(v___y_3907_);
v_a_3946_ = lean_ctor_get(v___x_3930_, 0);
v_isSharedCheck_3953_ = !lean_is_exclusive(v___x_3930_);
if (v_isSharedCheck_3953_ == 0)
{
v___x_3948_ = v___x_3930_;
v_isShared_3949_ = v_isSharedCheck_3953_;
goto v_resetjp_3947_;
}
else
{
lean_inc(v_a_3946_);
lean_dec(v___x_3930_);
v___x_3948_ = lean_box(0);
v_isShared_3949_ = v_isSharedCheck_3953_;
goto v_resetjp_3947_;
}
v_resetjp_3947_:
{
lean_object* v___x_3951_; 
if (v_isShared_3949_ == 0)
{
v___x_3951_ = v___x_3948_;
goto v_reusejp_3950_;
}
else
{
lean_object* v_reuseFailAlloc_3952_; 
v_reuseFailAlloc_3952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3952_, 0, v_a_3946_);
v___x_3951_ = v_reuseFailAlloc_3952_;
goto v_reusejp_3950_;
}
v_reusejp_3950_:
{
return v___x_3951_;
}
}
}
}
else
{
lean_object* v_a_3954_; lean_object* v___x_3956_; uint8_t v_isShared_3957_; uint8_t v_isSharedCheck_3961_; 
lean_dec_ref(v___y_3919_);
lean_dec(v___y_3916_);
lean_dec_ref(v___y_3915_);
lean_dec(v___y_3914_);
lean_dec_ref(v___y_3908_);
lean_dec(v___y_3907_);
v_a_3954_ = lean_ctor_get(v___x_3928_, 0);
v_isSharedCheck_3961_ = !lean_is_exclusive(v___x_3928_);
if (v_isSharedCheck_3961_ == 0)
{
v___x_3956_ = v___x_3928_;
v_isShared_3957_ = v_isSharedCheck_3961_;
goto v_resetjp_3955_;
}
else
{
lean_inc(v_a_3954_);
lean_dec(v___x_3928_);
v___x_3956_ = lean_box(0);
v_isShared_3957_ = v_isSharedCheck_3961_;
goto v_resetjp_3955_;
}
v_resetjp_3955_:
{
lean_object* v___x_3959_; 
if (v_isShared_3957_ == 0)
{
v___x_3959_ = v___x_3956_;
goto v_reusejp_3958_;
}
else
{
lean_object* v_reuseFailAlloc_3960_; 
v_reuseFailAlloc_3960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3960_, 0, v_a_3954_);
v___x_3959_ = v_reuseFailAlloc_3960_;
goto v_reusejp_3958_;
}
v_reusejp_3958_:
{
return v___x_3959_;
}
}
}
}
}
}
else
{
lean_object* v_a_3962_; lean_object* v___x_3964_; uint8_t v_isShared_3965_; uint8_t v_isSharedCheck_3969_; 
lean_dec_ref(v___y_3919_);
lean_dec(v___y_3916_);
lean_dec_ref(v___y_3915_);
lean_dec(v___y_3914_);
lean_dec_ref(v___y_3908_);
lean_dec(v___y_3907_);
v_a_3962_ = lean_ctor_get(v___x_3925_, 0);
v_isSharedCheck_3969_ = !lean_is_exclusive(v___x_3925_);
if (v_isSharedCheck_3969_ == 0)
{
v___x_3964_ = v___x_3925_;
v_isShared_3965_ = v_isSharedCheck_3969_;
goto v_resetjp_3963_;
}
else
{
lean_inc(v_a_3962_);
lean_dec(v___x_3925_);
v___x_3964_ = lean_box(0);
v_isShared_3965_ = v_isSharedCheck_3969_;
goto v_resetjp_3963_;
}
v_resetjp_3963_:
{
lean_object* v___x_3967_; 
if (v_isShared_3965_ == 0)
{
v___x_3967_ = v___x_3964_;
goto v_reusejp_3966_;
}
else
{
lean_object* v_reuseFailAlloc_3968_; 
v_reuseFailAlloc_3968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3968_, 0, v_a_3962_);
v___x_3967_ = v_reuseFailAlloc_3968_;
goto v_reusejp_3966_;
}
v_reusejp_3966_:
{
return v___x_3967_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___boxed(lean_object* v_c_4301_, lean_object* v_e_4302_, lean_object* v_he_4303_, lean_object* v_a_4304_, lean_object* v_a_4305_, lean_object* v_a_4306_, lean_object* v_a_4307_, lean_object* v_a_4308_, lean_object* v_a_4309_, lean_object* v_a_4310_, lean_object* v_a_4311_, lean_object* v_a_4312_, lean_object* v_a_4313_, lean_object* v_a_4314_, lean_object* v_a_4315_){
_start:
{
lean_object* v_res_4316_; 
v_res_4316_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse(v_c_4301_, v_e_4302_, v_he_4303_, v_a_4304_, v_a_4305_, v_a_4306_, v_a_4307_, v_a_4308_, v_a_4309_, v_a_4310_, v_a_4311_, v_a_4312_, v_a_4313_, v_a_4314_);
lean_dec(v_a_4314_);
lean_dec_ref(v_a_4313_);
lean_dec(v_a_4312_);
lean_dec_ref(v_a_4311_);
lean_dec(v_a_4310_);
lean_dec_ref(v_a_4309_);
lean_dec(v_a_4308_);
lean_dec_ref(v_a_4307_);
lean_dec(v_a_4306_);
lean_dec(v_a_4305_);
lean_dec(v_a_4304_);
return v_res_4316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___redArg(lean_object* v_e_4317_, lean_object* v_a_4318_, lean_object* v_a_4319_){
_start:
{
lean_object* v___x_4321_; 
v___x_4321_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_4318_, v_a_4319_);
if (lean_obj_tag(v___x_4321_) == 0)
{
lean_object* v_a_4322_; lean_object* v___x_4324_; uint8_t v_isShared_4325_; uint8_t v_isSharedCheck_4331_; 
v_a_4322_ = lean_ctor_get(v___x_4321_, 0);
v_isSharedCheck_4331_ = !lean_is_exclusive(v___x_4321_);
if (v_isSharedCheck_4331_ == 0)
{
v___x_4324_ = v___x_4321_;
v_isShared_4325_ = v_isSharedCheck_4331_;
goto v_resetjp_4323_;
}
else
{
lean_inc(v_a_4322_);
lean_dec(v___x_4321_);
v___x_4324_ = lean_box(0);
v_isShared_4325_ = v_isSharedCheck_4331_;
goto v_resetjp_4323_;
}
v_resetjp_4323_:
{
lean_object* v_exprToStructId_4326_; lean_object* v___x_4327_; lean_object* v___x_4329_; 
v_exprToStructId_4326_ = lean_ctor_get(v_a_4322_, 2);
lean_inc_ref(v_exprToStructId_4326_);
lean_dec(v_a_4322_);
v___x_4327_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_exprToStructId_4326_, v_e_4317_);
lean_dec_ref(v_exprToStructId_4326_);
if (v_isShared_4325_ == 0)
{
lean_ctor_set(v___x_4324_, 0, v___x_4327_);
v___x_4329_ = v___x_4324_;
goto v_reusejp_4328_;
}
else
{
lean_object* v_reuseFailAlloc_4330_; 
v_reuseFailAlloc_4330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4330_, 0, v___x_4327_);
v___x_4329_ = v_reuseFailAlloc_4330_;
goto v_reusejp_4328_;
}
v_reusejp_4328_:
{
return v___x_4329_;
}
}
}
else
{
lean_object* v_a_4332_; lean_object* v___x_4334_; uint8_t v_isShared_4335_; uint8_t v_isSharedCheck_4339_; 
v_a_4332_ = lean_ctor_get(v___x_4321_, 0);
v_isSharedCheck_4339_ = !lean_is_exclusive(v___x_4321_);
if (v_isSharedCheck_4339_ == 0)
{
v___x_4334_ = v___x_4321_;
v_isShared_4335_ = v_isSharedCheck_4339_;
goto v_resetjp_4333_;
}
else
{
lean_inc(v_a_4332_);
lean_dec(v___x_4321_);
v___x_4334_ = lean_box(0);
v_isShared_4335_ = v_isSharedCheck_4339_;
goto v_resetjp_4333_;
}
v_resetjp_4333_:
{
lean_object* v___x_4337_; 
if (v_isShared_4335_ == 0)
{
v___x_4337_ = v___x_4334_;
goto v_reusejp_4336_;
}
else
{
lean_object* v_reuseFailAlloc_4338_; 
v_reuseFailAlloc_4338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4338_, 0, v_a_4332_);
v___x_4337_ = v_reuseFailAlloc_4338_;
goto v_reusejp_4336_;
}
v_reusejp_4336_:
{
return v___x_4337_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___redArg___boxed(lean_object* v_e_4340_, lean_object* v_a_4341_, lean_object* v_a_4342_, lean_object* v_a_4343_){
_start:
{
lean_object* v_res_4344_; 
v_res_4344_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___redArg(v_e_4340_, v_a_4341_, v_a_4342_);
lean_dec_ref(v_a_4342_);
lean_dec(v_a_4341_);
lean_dec_ref(v_e_4340_);
return v_res_4344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f(lean_object* v_e_4345_, lean_object* v_a_4346_, lean_object* v_a_4347_, lean_object* v_a_4348_, lean_object* v_a_4349_, lean_object* v_a_4350_, lean_object* v_a_4351_, lean_object* v_a_4352_, lean_object* v_a_4353_, lean_object* v_a_4354_, lean_object* v_a_4355_){
_start:
{
lean_object* v___x_4357_; 
v___x_4357_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___redArg(v_e_4345_, v_a_4346_, v_a_4354_);
return v___x_4357_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___boxed(lean_object* v_e_4358_, lean_object* v_a_4359_, lean_object* v_a_4360_, lean_object* v_a_4361_, lean_object* v_a_4362_, lean_object* v_a_4363_, lean_object* v_a_4364_, lean_object* v_a_4365_, lean_object* v_a_4366_, lean_object* v_a_4367_, lean_object* v_a_4368_, lean_object* v_a_4369_){
_start:
{
lean_object* v_res_4370_; 
v_res_4370_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f(v_e_4358_, v_a_4359_, v_a_4360_, v_a_4361_, v_a_4362_, v_a_4363_, v_a_4364_, v_a_4365_, v_a_4366_, v_a_4367_, v_a_4368_);
lean_dec(v_a_4368_);
lean_dec_ref(v_a_4367_);
lean_dec(v_a_4366_);
lean_dec_ref(v_a_4365_);
lean_dec(v_a_4364_);
lean_dec_ref(v_a_4363_);
lean_dec(v_a_4362_);
lean_dec_ref(v_a_4361_);
lean_dec(v_a_4360_);
lean_dec(v_a_4359_);
lean_dec_ref(v_e_4358_);
return v_res_4370_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__2(void){
_start:
{
lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; 
v___x_4377_ = lean_box(0);
v___x_4378_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__1));
v___x_4379_ = l_Lean_mkConst(v___x_4378_, v___x_4377_);
return v___x_4379_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__5(void){
_start:
{
lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; 
v___x_4386_ = lean_box(0);
v___x_4387_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__4));
v___x_4388_ = l_Lean_mkConst(v___x_4387_, v___x_4386_);
return v___x_4388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go(lean_object* v_e_4389_, lean_object* v_e_x27_4390_, lean_object* v_he_x3f_4391_, lean_object* v_a_4392_, lean_object* v_a_4393_, lean_object* v_a_4394_, lean_object* v_a_4395_, lean_object* v_a_4396_, lean_object* v_a_4397_, lean_object* v_a_4398_, lean_object* v_a_4399_, lean_object* v_a_4400_, lean_object* v_a_4401_){
_start:
{
lean_object* v___x_4403_; 
v___x_4403_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___redArg(v_e_x27_4390_, v_a_4392_, v_a_4400_);
if (lean_obj_tag(v___x_4403_) == 0)
{
lean_object* v_a_4404_; lean_object* v___x_4406_; uint8_t v_isShared_4407_; uint8_t v_isSharedCheck_4494_; 
v_a_4404_ = lean_ctor_get(v___x_4403_, 0);
v_isSharedCheck_4494_ = !lean_is_exclusive(v___x_4403_);
if (v_isSharedCheck_4494_ == 0)
{
v___x_4406_ = v___x_4403_;
v_isShared_4407_ = v_isSharedCheck_4494_;
goto v_resetjp_4405_;
}
else
{
lean_inc(v_a_4404_);
lean_dec(v___x_4403_);
v___x_4406_ = lean_box(0);
v_isShared_4407_ = v_isSharedCheck_4494_;
goto v_resetjp_4405_;
}
v_resetjp_4405_:
{
if (lean_obj_tag(v_a_4404_) == 1)
{
lean_object* v_val_4408_; lean_object* v___x_4409_; 
lean_del_object(v___x_4406_);
v_val_4408_ = lean_ctor_get(v_a_4404_, 0);
lean_inc(v_val_4408_);
lean_dec_ref(v_a_4404_);
v___x_4409_ = l_Lean_Meta_Grind_Order_getCnstr_x3f(v_e_x27_4390_, v_val_4408_, v_a_4392_, v_a_4393_, v_a_4394_, v_a_4395_, v_a_4396_, v_a_4397_, v_a_4398_, v_a_4399_, v_a_4400_, v_a_4401_);
if (lean_obj_tag(v___x_4409_) == 0)
{
lean_object* v_a_4410_; lean_object* v___x_4412_; uint8_t v_isShared_4413_; uint8_t v_isSharedCheck_4481_; 
v_a_4410_ = lean_ctor_get(v___x_4409_, 0);
v_isSharedCheck_4481_ = !lean_is_exclusive(v___x_4409_);
if (v_isSharedCheck_4481_ == 0)
{
v___x_4412_ = v___x_4409_;
v_isShared_4413_ = v_isSharedCheck_4481_;
goto v_resetjp_4411_;
}
else
{
lean_inc(v_a_4410_);
lean_dec(v___x_4409_);
v___x_4412_ = lean_box(0);
v_isShared_4413_ = v_isSharedCheck_4481_;
goto v_resetjp_4411_;
}
v_resetjp_4411_:
{
if (lean_obj_tag(v_a_4410_) == 1)
{
lean_object* v_val_4414_; lean_object* v___x_4415_; 
lean_del_object(v___x_4412_);
v_val_4414_ = lean_ctor_get(v_a_4410_, 0);
lean_inc(v_val_4414_);
lean_dec_ref(v_a_4410_);
lean_inc_ref(v_e_4389_);
v___x_4415_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_4389_, v_a_4392_, v_a_4396_, v_a_4398_, v_a_4399_, v_a_4400_, v_a_4401_);
if (lean_obj_tag(v___x_4415_) == 0)
{
lean_object* v_a_4416_; uint8_t v___x_4417_; 
v_a_4416_ = lean_ctor_get(v___x_4415_, 0);
lean_inc(v_a_4416_);
lean_dec_ref(v___x_4415_);
v___x_4417_ = lean_unbox(v_a_4416_);
lean_dec(v_a_4416_);
if (v___x_4417_ == 0)
{
lean_object* v___x_4418_; 
lean_inc_ref(v_e_4389_);
v___x_4418_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_4389_, v_a_4392_, v_a_4396_, v_a_4398_, v_a_4399_, v_a_4400_, v_a_4401_);
if (lean_obj_tag(v___x_4418_) == 0)
{
lean_object* v_a_4419_; lean_object* v___x_4421_; uint8_t v_isShared_4422_; uint8_t v_isSharedCheck_4444_; 
v_a_4419_ = lean_ctor_get(v___x_4418_, 0);
v_isSharedCheck_4444_ = !lean_is_exclusive(v___x_4418_);
if (v_isSharedCheck_4444_ == 0)
{
v___x_4421_ = v___x_4418_;
v_isShared_4422_ = v_isSharedCheck_4444_;
goto v_resetjp_4420_;
}
else
{
lean_inc(v_a_4419_);
lean_dec(v___x_4418_);
v___x_4421_ = lean_box(0);
v_isShared_4422_ = v_isSharedCheck_4444_;
goto v_resetjp_4420_;
}
v_resetjp_4420_:
{
uint8_t v___x_4423_; 
v___x_4423_ = lean_unbox(v_a_4419_);
lean_dec(v_a_4419_);
if (v___x_4423_ == 0)
{
lean_object* v___x_4424_; lean_object* v___x_4426_; 
lean_dec(v_val_4414_);
lean_dec(v_val_4408_);
lean_dec(v_he_x3f_4391_);
lean_dec_ref(v_e_x27_4390_);
lean_dec_ref(v_e_4389_);
v___x_4424_ = lean_box(0);
if (v_isShared_4422_ == 0)
{
lean_ctor_set(v___x_4421_, 0, v___x_4424_);
v___x_4426_ = v___x_4421_;
goto v_reusejp_4425_;
}
else
{
lean_object* v_reuseFailAlloc_4427_; 
v_reuseFailAlloc_4427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4427_, 0, v___x_4424_);
v___x_4426_ = v_reuseFailAlloc_4427_;
goto v_reusejp_4425_;
}
v_reusejp_4425_:
{
return v___x_4426_;
}
}
else
{
lean_object* v___x_4428_; 
lean_del_object(v___x_4421_);
lean_inc_ref(v_e_4389_);
v___x_4428_ = l_Lean_Meta_Grind_mkEqFalseProof(v_e_4389_, v_a_4392_, v_a_4393_, v_a_4394_, v_a_4395_, v_a_4396_, v_a_4397_, v_a_4398_, v_a_4399_, v_a_4400_, v_a_4401_);
if (lean_obj_tag(v___x_4428_) == 0)
{
if (lean_obj_tag(v_he_x3f_4391_) == 1)
{
lean_object* v_a_4429_; lean_object* v_val_4430_; lean_object* v___x_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; 
v_a_4429_ = lean_ctor_get(v___x_4428_, 0);
lean_inc(v_a_4429_);
lean_dec_ref(v___x_4428_);
v_val_4430_ = lean_ctor_get(v_he_x3f_4391_, 0);
lean_inc(v_val_4430_);
lean_dec_ref(v_he_x3f_4391_);
v___x_4431_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__2, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__2);
lean_inc_ref(v_e_x27_4390_);
v___x_4432_ = l_Lean_mkApp4(v___x_4431_, v_e_4389_, v_e_x27_4390_, v_val_4430_, v_a_4429_);
v___x_4433_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse(v_val_4414_, v_e_x27_4390_, v___x_4432_, v_val_4408_, v_a_4392_, v_a_4393_, v_a_4394_, v_a_4395_, v_a_4396_, v_a_4397_, v_a_4398_, v_a_4399_, v_a_4400_, v_a_4401_);
lean_dec(v_val_4408_);
return v___x_4433_;
}
else
{
lean_object* v_a_4434_; lean_object* v___x_4435_; 
lean_dec(v_he_x3f_4391_);
lean_dec_ref(v_e_4389_);
v_a_4434_ = lean_ctor_get(v___x_4428_, 0);
lean_inc(v_a_4434_);
lean_dec_ref(v___x_4428_);
v___x_4435_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse(v_val_4414_, v_e_x27_4390_, v_a_4434_, v_val_4408_, v_a_4392_, v_a_4393_, v_a_4394_, v_a_4395_, v_a_4396_, v_a_4397_, v_a_4398_, v_a_4399_, v_a_4400_, v_a_4401_);
lean_dec(v_val_4408_);
return v___x_4435_;
}
}
else
{
lean_object* v_a_4436_; lean_object* v___x_4438_; uint8_t v_isShared_4439_; uint8_t v_isSharedCheck_4443_; 
lean_dec(v_val_4414_);
lean_dec(v_val_4408_);
lean_dec(v_he_x3f_4391_);
lean_dec_ref(v_e_x27_4390_);
lean_dec_ref(v_e_4389_);
v_a_4436_ = lean_ctor_get(v___x_4428_, 0);
v_isSharedCheck_4443_ = !lean_is_exclusive(v___x_4428_);
if (v_isSharedCheck_4443_ == 0)
{
v___x_4438_ = v___x_4428_;
v_isShared_4439_ = v_isSharedCheck_4443_;
goto v_resetjp_4437_;
}
else
{
lean_inc(v_a_4436_);
lean_dec(v___x_4428_);
v___x_4438_ = lean_box(0);
v_isShared_4439_ = v_isSharedCheck_4443_;
goto v_resetjp_4437_;
}
v_resetjp_4437_:
{
lean_object* v___x_4441_; 
if (v_isShared_4439_ == 0)
{
v___x_4441_ = v___x_4438_;
goto v_reusejp_4440_;
}
else
{
lean_object* v_reuseFailAlloc_4442_; 
v_reuseFailAlloc_4442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4442_, 0, v_a_4436_);
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
}
}
else
{
lean_object* v_a_4445_; lean_object* v___x_4447_; uint8_t v_isShared_4448_; uint8_t v_isSharedCheck_4452_; 
lean_dec(v_val_4414_);
lean_dec(v_val_4408_);
lean_dec(v_he_x3f_4391_);
lean_dec_ref(v_e_x27_4390_);
lean_dec_ref(v_e_4389_);
v_a_4445_ = lean_ctor_get(v___x_4418_, 0);
v_isSharedCheck_4452_ = !lean_is_exclusive(v___x_4418_);
if (v_isSharedCheck_4452_ == 0)
{
v___x_4447_ = v___x_4418_;
v_isShared_4448_ = v_isSharedCheck_4452_;
goto v_resetjp_4446_;
}
else
{
lean_inc(v_a_4445_);
lean_dec(v___x_4418_);
v___x_4447_ = lean_box(0);
v_isShared_4448_ = v_isSharedCheck_4452_;
goto v_resetjp_4446_;
}
v_resetjp_4446_:
{
lean_object* v___x_4450_; 
if (v_isShared_4448_ == 0)
{
v___x_4450_ = v___x_4447_;
goto v_reusejp_4449_;
}
else
{
lean_object* v_reuseFailAlloc_4451_; 
v_reuseFailAlloc_4451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4451_, 0, v_a_4445_);
v___x_4450_ = v_reuseFailAlloc_4451_;
goto v_reusejp_4449_;
}
v_reusejp_4449_:
{
return v___x_4450_;
}
}
}
}
else
{
lean_object* v___x_4453_; 
lean_inc_ref(v_e_4389_);
v___x_4453_ = l_Lean_Meta_Grind_mkEqTrueProof(v_e_4389_, v_a_4392_, v_a_4393_, v_a_4394_, v_a_4395_, v_a_4396_, v_a_4397_, v_a_4398_, v_a_4399_, v_a_4400_, v_a_4401_);
if (lean_obj_tag(v___x_4453_) == 0)
{
if (lean_obj_tag(v_he_x3f_4391_) == 1)
{
lean_object* v_a_4454_; lean_object* v_val_4455_; lean_object* v___x_4456_; lean_object* v___x_4457_; lean_object* v___x_4458_; 
v_a_4454_ = lean_ctor_get(v___x_4453_, 0);
lean_inc(v_a_4454_);
lean_dec_ref(v___x_4453_);
v_val_4455_ = lean_ctor_get(v_he_x3f_4391_, 0);
lean_inc(v_val_4455_);
lean_dec_ref(v_he_x3f_4391_);
v___x_4456_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__5);
lean_inc_ref(v_e_x27_4390_);
v___x_4457_ = l_Lean_mkApp4(v___x_4456_, v_e_4389_, v_e_x27_4390_, v_val_4455_, v_a_4454_);
v___x_4458_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue(v_val_4414_, v_e_x27_4390_, v___x_4457_, v_val_4408_, v_a_4392_, v_a_4393_, v_a_4394_, v_a_4395_, v_a_4396_, v_a_4397_, v_a_4398_, v_a_4399_, v_a_4400_, v_a_4401_);
lean_dec(v_val_4408_);
return v___x_4458_;
}
else
{
lean_object* v_a_4459_; lean_object* v___x_4460_; 
lean_dec(v_he_x3f_4391_);
lean_dec_ref(v_e_4389_);
v_a_4459_ = lean_ctor_get(v___x_4453_, 0);
lean_inc(v_a_4459_);
lean_dec_ref(v___x_4453_);
v___x_4460_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue(v_val_4414_, v_e_x27_4390_, v_a_4459_, v_val_4408_, v_a_4392_, v_a_4393_, v_a_4394_, v_a_4395_, v_a_4396_, v_a_4397_, v_a_4398_, v_a_4399_, v_a_4400_, v_a_4401_);
lean_dec(v_val_4408_);
return v___x_4460_;
}
}
else
{
lean_object* v_a_4461_; lean_object* v___x_4463_; uint8_t v_isShared_4464_; uint8_t v_isSharedCheck_4468_; 
lean_dec(v_val_4414_);
lean_dec(v_val_4408_);
lean_dec(v_he_x3f_4391_);
lean_dec_ref(v_e_x27_4390_);
lean_dec_ref(v_e_4389_);
v_a_4461_ = lean_ctor_get(v___x_4453_, 0);
v_isSharedCheck_4468_ = !lean_is_exclusive(v___x_4453_);
if (v_isSharedCheck_4468_ == 0)
{
v___x_4463_ = v___x_4453_;
v_isShared_4464_ = v_isSharedCheck_4468_;
goto v_resetjp_4462_;
}
else
{
lean_inc(v_a_4461_);
lean_dec(v___x_4453_);
v___x_4463_ = lean_box(0);
v_isShared_4464_ = v_isSharedCheck_4468_;
goto v_resetjp_4462_;
}
v_resetjp_4462_:
{
lean_object* v___x_4466_; 
if (v_isShared_4464_ == 0)
{
v___x_4466_ = v___x_4463_;
goto v_reusejp_4465_;
}
else
{
lean_object* v_reuseFailAlloc_4467_; 
v_reuseFailAlloc_4467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4467_, 0, v_a_4461_);
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
}
else
{
lean_object* v_a_4469_; lean_object* v___x_4471_; uint8_t v_isShared_4472_; uint8_t v_isSharedCheck_4476_; 
lean_dec(v_val_4414_);
lean_dec(v_val_4408_);
lean_dec(v_he_x3f_4391_);
lean_dec_ref(v_e_x27_4390_);
lean_dec_ref(v_e_4389_);
v_a_4469_ = lean_ctor_get(v___x_4415_, 0);
v_isSharedCheck_4476_ = !lean_is_exclusive(v___x_4415_);
if (v_isSharedCheck_4476_ == 0)
{
v___x_4471_ = v___x_4415_;
v_isShared_4472_ = v_isSharedCheck_4476_;
goto v_resetjp_4470_;
}
else
{
lean_inc(v_a_4469_);
lean_dec(v___x_4415_);
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
lean_dec(v_a_4410_);
lean_dec(v_val_4408_);
lean_dec(v_he_x3f_4391_);
lean_dec_ref(v_e_x27_4390_);
lean_dec_ref(v_e_4389_);
v___x_4477_ = lean_box(0);
if (v_isShared_4413_ == 0)
{
lean_ctor_set(v___x_4412_, 0, v___x_4477_);
v___x_4479_ = v___x_4412_;
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
lean_dec(v_val_4408_);
lean_dec(v_he_x3f_4391_);
lean_dec_ref(v_e_x27_4390_);
lean_dec_ref(v_e_4389_);
v_a_4482_ = lean_ctor_get(v___x_4409_, 0);
v_isSharedCheck_4489_ = !lean_is_exclusive(v___x_4409_);
if (v_isSharedCheck_4489_ == 0)
{
v___x_4484_ = v___x_4409_;
v_isShared_4485_ = v_isSharedCheck_4489_;
goto v_resetjp_4483_;
}
else
{
lean_inc(v_a_4482_);
lean_dec(v___x_4409_);
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
else
{
lean_object* v___x_4490_; lean_object* v___x_4492_; 
lean_dec(v_a_4404_);
lean_dec(v_he_x3f_4391_);
lean_dec_ref(v_e_x27_4390_);
lean_dec_ref(v_e_4389_);
v___x_4490_ = lean_box(0);
if (v_isShared_4407_ == 0)
{
lean_ctor_set(v___x_4406_, 0, v___x_4490_);
v___x_4492_ = v___x_4406_;
goto v_reusejp_4491_;
}
else
{
lean_object* v_reuseFailAlloc_4493_; 
v_reuseFailAlloc_4493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4493_, 0, v___x_4490_);
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
lean_object* v_a_4495_; lean_object* v___x_4497_; uint8_t v_isShared_4498_; uint8_t v_isSharedCheck_4502_; 
lean_dec(v_he_x3f_4391_);
lean_dec_ref(v_e_x27_4390_);
lean_dec_ref(v_e_4389_);
v_a_4495_ = lean_ctor_get(v___x_4403_, 0);
v_isSharedCheck_4502_ = !lean_is_exclusive(v___x_4403_);
if (v_isSharedCheck_4502_ == 0)
{
v___x_4497_ = v___x_4403_;
v_isShared_4498_ = v_isSharedCheck_4502_;
goto v_resetjp_4496_;
}
else
{
lean_inc(v_a_4495_);
lean_dec(v___x_4403_);
v___x_4497_ = lean_box(0);
v_isShared_4498_ = v_isSharedCheck_4502_;
goto v_resetjp_4496_;
}
v_resetjp_4496_:
{
lean_object* v___x_4500_; 
if (v_isShared_4498_ == 0)
{
v___x_4500_ = v___x_4497_;
goto v_reusejp_4499_;
}
else
{
lean_object* v_reuseFailAlloc_4501_; 
v_reuseFailAlloc_4501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4501_, 0, v_a_4495_);
v___x_4500_ = v_reuseFailAlloc_4501_;
goto v_reusejp_4499_;
}
v_reusejp_4499_:
{
return v___x_4500_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___boxed(lean_object* v_e_4503_, lean_object* v_e_x27_4504_, lean_object* v_he_x3f_4505_, lean_object* v_a_4506_, lean_object* v_a_4507_, lean_object* v_a_4508_, lean_object* v_a_4509_, lean_object* v_a_4510_, lean_object* v_a_4511_, lean_object* v_a_4512_, lean_object* v_a_4513_, lean_object* v_a_4514_, lean_object* v_a_4515_, lean_object* v_a_4516_){
_start:
{
lean_object* v_res_4517_; 
v_res_4517_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go(v_e_4503_, v_e_x27_4504_, v_he_x3f_4505_, v_a_4506_, v_a_4507_, v_a_4508_, v_a_4509_, v_a_4510_, v_a_4511_, v_a_4512_, v_a_4513_, v_a_4514_, v_a_4515_);
lean_dec(v_a_4515_);
lean_dec_ref(v_a_4514_);
lean_dec(v_a_4513_);
lean_dec_ref(v_a_4512_);
lean_dec(v_a_4511_);
lean_dec_ref(v_a_4510_);
lean_dec(v_a_4509_);
lean_dec_ref(v_a_4508_);
lean_dec(v_a_4507_);
lean_dec(v_a_4506_);
return v_res_4517_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq(lean_object* v_e_4518_, lean_object* v_a_4519_, lean_object* v_a_4520_, lean_object* v_a_4521_, lean_object* v_a_4522_, lean_object* v_a_4523_, lean_object* v_a_4524_, lean_object* v_a_4525_, lean_object* v_a_4526_, lean_object* v_a_4527_, lean_object* v_a_4528_){
_start:
{
lean_object* v___x_4530_; 
v___x_4530_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_4519_, v_a_4527_);
if (lean_obj_tag(v___x_4530_) == 0)
{
lean_object* v_a_4531_; lean_object* v_termMap_4532_; lean_object* v___x_4533_; 
v_a_4531_ = lean_ctor_get(v___x_4530_, 0);
lean_inc(v_a_4531_);
lean_dec_ref(v___x_4530_);
v_termMap_4532_ = lean_ctor_get(v_a_4531_, 3);
lean_inc_ref(v_termMap_4532_);
lean_dec(v_a_4531_);
v___x_4533_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMap_4532_, v_e_4518_);
lean_dec_ref(v_termMap_4532_);
if (lean_obj_tag(v___x_4533_) == 1)
{
lean_object* v_val_4534_; lean_object* v___x_4536_; uint8_t v_isShared_4537_; uint8_t v_isSharedCheck_4544_; 
v_val_4534_ = lean_ctor_get(v___x_4533_, 0);
v_isSharedCheck_4544_ = !lean_is_exclusive(v___x_4533_);
if (v_isSharedCheck_4544_ == 0)
{
v___x_4536_ = v___x_4533_;
v_isShared_4537_ = v_isSharedCheck_4544_;
goto v_resetjp_4535_;
}
else
{
lean_inc(v_val_4534_);
lean_dec(v___x_4533_);
v___x_4536_ = lean_box(0);
v_isShared_4537_ = v_isSharedCheck_4544_;
goto v_resetjp_4535_;
}
v_resetjp_4535_:
{
lean_object* v_e_4538_; lean_object* v_h_4539_; lean_object* v___x_4541_; 
v_e_4538_ = lean_ctor_get(v_val_4534_, 0);
lean_inc_ref(v_e_4538_);
v_h_4539_ = lean_ctor_get(v_val_4534_, 1);
lean_inc_ref(v_h_4539_);
lean_dec(v_val_4534_);
if (v_isShared_4537_ == 0)
{
lean_ctor_set(v___x_4536_, 0, v_h_4539_);
v___x_4541_ = v___x_4536_;
goto v_reusejp_4540_;
}
else
{
lean_object* v_reuseFailAlloc_4543_; 
v_reuseFailAlloc_4543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4543_, 0, v_h_4539_);
v___x_4541_ = v_reuseFailAlloc_4543_;
goto v_reusejp_4540_;
}
v_reusejp_4540_:
{
lean_object* v___x_4542_; 
v___x_4542_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go(v_e_4518_, v_e_4538_, v___x_4541_, v_a_4519_, v_a_4520_, v_a_4521_, v_a_4522_, v_a_4523_, v_a_4524_, v_a_4525_, v_a_4526_, v_a_4527_, v_a_4528_);
return v___x_4542_;
}
}
}
else
{
lean_object* v___x_4545_; lean_object* v___x_4546_; 
lean_dec(v___x_4533_);
v___x_4545_ = lean_box(0);
lean_inc_ref(v_e_4518_);
v___x_4546_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go(v_e_4518_, v_e_4518_, v___x_4545_, v_a_4519_, v_a_4520_, v_a_4521_, v_a_4522_, v_a_4523_, v_a_4524_, v_a_4525_, v_a_4526_, v_a_4527_, v_a_4528_);
return v___x_4546_;
}
}
else
{
lean_object* v_a_4547_; lean_object* v___x_4549_; uint8_t v_isShared_4550_; uint8_t v_isSharedCheck_4554_; 
lean_dec_ref(v_e_4518_);
v_a_4547_ = lean_ctor_get(v___x_4530_, 0);
v_isSharedCheck_4554_ = !lean_is_exclusive(v___x_4530_);
if (v_isSharedCheck_4554_ == 0)
{
v___x_4549_ = v___x_4530_;
v_isShared_4550_ = v_isSharedCheck_4554_;
goto v_resetjp_4548_;
}
else
{
lean_inc(v_a_4547_);
lean_dec(v___x_4530_);
v___x_4549_ = lean_box(0);
v_isShared_4550_ = v_isSharedCheck_4554_;
goto v_resetjp_4548_;
}
v_resetjp_4548_:
{
lean_object* v___x_4552_; 
if (v_isShared_4550_ == 0)
{
v___x_4552_ = v___x_4549_;
goto v_reusejp_4551_;
}
else
{
lean_object* v_reuseFailAlloc_4553_; 
v_reuseFailAlloc_4553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4553_, 0, v_a_4547_);
v___x_4552_ = v_reuseFailAlloc_4553_;
goto v_reusejp_4551_;
}
v_reusejp_4551_:
{
return v___x_4552_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq___boxed(lean_object* v_e_4555_, lean_object* v_a_4556_, lean_object* v_a_4557_, lean_object* v_a_4558_, lean_object* v_a_4559_, lean_object* v_a_4560_, lean_object* v_a_4561_, lean_object* v_a_4562_, lean_object* v_a_4563_, lean_object* v_a_4564_, lean_object* v_a_4565_, lean_object* v_a_4566_){
_start:
{
lean_object* v_res_4567_; 
v_res_4567_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq(v_e_4555_, v_a_4556_, v_a_4557_, v_a_4558_, v_a_4559_, v_a_4560_, v_a_4561_, v_a_4562_, v_a_4563_, v_a_4564_, v_a_4565_);
lean_dec(v_a_4565_);
lean_dec_ref(v_a_4564_);
lean_dec(v_a_4563_);
lean_dec_ref(v_a_4562_);
lean_dec(v_a_4561_);
lean_dec_ref(v_a_4560_);
lean_dec(v_a_4559_);
lean_dec_ref(v_a_4558_);
lean_dec(v_a_4557_);
lean_dec(v_a_4556_);
return v_res_4567_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE(lean_object* v_e_4568_, lean_object* v_a_4569_, lean_object* v_a_4570_, lean_object* v_a_4571_, lean_object* v_a_4572_, lean_object* v_a_4573_, lean_object* v_a_4574_, lean_object* v_a_4575_, lean_object* v_a_4576_, lean_object* v_a_4577_, lean_object* v_a_4578_){
_start:
{
lean_object* v___x_4580_; 
v___x_4580_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq(v_e_4568_, v_a_4569_, v_a_4570_, v_a_4571_, v_a_4572_, v_a_4573_, v_a_4574_, v_a_4575_, v_a_4576_, v_a_4577_, v_a_4578_);
return v___x_4580_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___boxed(lean_object* v_e_4581_, lean_object* v_a_4582_, lean_object* v_a_4583_, lean_object* v_a_4584_, lean_object* v_a_4585_, lean_object* v_a_4586_, lean_object* v_a_4587_, lean_object* v_a_4588_, lean_object* v_a_4589_, lean_object* v_a_4590_, lean_object* v_a_4591_, lean_object* v_a_4592_){
_start:
{
lean_object* v_res_4593_; 
v_res_4593_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE(v_e_4581_, v_a_4582_, v_a_4583_, v_a_4584_, v_a_4585_, v_a_4586_, v_a_4587_, v_a_4588_, v_a_4589_, v_a_4590_, v_a_4591_);
lean_dec(v_a_4591_);
lean_dec_ref(v_a_4590_);
lean_dec(v_a_4589_);
lean_dec_ref(v_a_4588_);
lean_dec(v_a_4587_);
lean_dec_ref(v_a_4586_);
lean_dec(v_a_4585_);
lean_dec_ref(v_a_4584_);
lean_dec(v_a_4583_);
lean_dec(v_a_4582_);
return v_res_4593_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_8_(){
_start:
{
lean_object* v___f_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; 
v___f_4601_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_8_));
v___x_4602_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_8_));
v___x_4603_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_4602_, v___f_4601_);
return v___x_4603_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_8____boxed(lean_object* v_a_4604_){
_start:
{
lean_object* v_res_4605_; 
v_res_4605_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_8_();
return v_res_4605_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT(lean_object* v_e_4606_, lean_object* v_a_4607_, lean_object* v_a_4608_, lean_object* v_a_4609_, lean_object* v_a_4610_, lean_object* v_a_4611_, lean_object* v_a_4612_, lean_object* v_a_4613_, lean_object* v_a_4614_, lean_object* v_a_4615_, lean_object* v_a_4616_){
_start:
{
lean_object* v___x_4618_; 
v___x_4618_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq(v_e_4606_, v_a_4607_, v_a_4608_, v_a_4609_, v_a_4610_, v_a_4611_, v_a_4612_, v_a_4613_, v_a_4614_, v_a_4615_, v_a_4616_);
return v___x_4618_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___boxed(lean_object* v_e_4619_, lean_object* v_a_4620_, lean_object* v_a_4621_, lean_object* v_a_4622_, lean_object* v_a_4623_, lean_object* v_a_4624_, lean_object* v_a_4625_, lean_object* v_a_4626_, lean_object* v_a_4627_, lean_object* v_a_4628_, lean_object* v_a_4629_, lean_object* v_a_4630_){
_start:
{
lean_object* v_res_4631_; 
v_res_4631_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT(v_e_4619_, v_a_4620_, v_a_4621_, v_a_4622_, v_a_4623_, v_a_4624_, v_a_4625_, v_a_4626_, v_a_4627_, v_a_4628_, v_a_4629_);
lean_dec(v_a_4629_);
lean_dec_ref(v_a_4628_);
lean_dec(v_a_4627_);
lean_dec_ref(v_a_4626_);
lean_dec(v_a_4625_);
lean_dec_ref(v_a_4624_);
lean_dec(v_a_4623_);
lean_dec_ref(v_a_4622_);
lean_dec(v_a_4621_);
lean_dec(v_a_4620_);
return v_res_4631_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_1204040634____hygCtx___hyg_8_(){
_start:
{
lean_object* v___f_4638_; lean_object* v___x_4639_; lean_object* v___x_4640_; 
v___f_4638_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_8_));
v___x_4639_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_1204040634____hygCtx___hyg_8_));
v___x_4640_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_4639_, v___f_4638_);
return v___x_4640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_1204040634____hygCtx___hyg_8____boxed(lean_object* v_a_4641_){
_start:
{
lean_object* v_res_4642_; 
v_res_4642_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_1204040634____hygCtx___hyg_8_();
return v_res_4642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f___redArg(lean_object* v_e_4643_, lean_object* v_a_4644_, lean_object* v_a_4645_){
_start:
{
lean_object* v___x_4647_; 
v___x_4647_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_4644_, v_a_4645_);
if (lean_obj_tag(v___x_4647_) == 0)
{
lean_object* v_a_4648_; lean_object* v___x_4650_; uint8_t v_isShared_4651_; uint8_t v_isSharedCheck_4657_; 
v_a_4648_ = lean_ctor_get(v___x_4647_, 0);
v_isSharedCheck_4657_ = !lean_is_exclusive(v___x_4647_);
if (v_isSharedCheck_4657_ == 0)
{
v___x_4650_ = v___x_4647_;
v_isShared_4651_ = v_isSharedCheck_4657_;
goto v_resetjp_4649_;
}
else
{
lean_inc(v_a_4648_);
lean_dec(v___x_4647_);
v___x_4650_ = lean_box(0);
v_isShared_4651_ = v_isSharedCheck_4657_;
goto v_resetjp_4649_;
}
v_resetjp_4649_:
{
lean_object* v_termMap_4652_; lean_object* v___x_4653_; lean_object* v___x_4655_; 
v_termMap_4652_ = lean_ctor_get(v_a_4648_, 3);
lean_inc_ref(v_termMap_4652_);
lean_dec(v_a_4648_);
v___x_4653_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMap_4652_, v_e_4643_);
lean_dec_ref(v_termMap_4652_);
if (v_isShared_4651_ == 0)
{
lean_ctor_set(v___x_4650_, 0, v___x_4653_);
v___x_4655_ = v___x_4650_;
goto v_reusejp_4654_;
}
else
{
lean_object* v_reuseFailAlloc_4656_; 
v_reuseFailAlloc_4656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4656_, 0, v___x_4653_);
v___x_4655_ = v_reuseFailAlloc_4656_;
goto v_reusejp_4654_;
}
v_reusejp_4654_:
{
return v___x_4655_;
}
}
}
else
{
lean_object* v_a_4658_; lean_object* v___x_4660_; uint8_t v_isShared_4661_; uint8_t v_isSharedCheck_4665_; 
v_a_4658_ = lean_ctor_get(v___x_4647_, 0);
v_isSharedCheck_4665_ = !lean_is_exclusive(v___x_4647_);
if (v_isSharedCheck_4665_ == 0)
{
v___x_4660_ = v___x_4647_;
v_isShared_4661_ = v_isSharedCheck_4665_;
goto v_resetjp_4659_;
}
else
{
lean_inc(v_a_4658_);
lean_dec(v___x_4647_);
v___x_4660_ = lean_box(0);
v_isShared_4661_ = v_isSharedCheck_4665_;
goto v_resetjp_4659_;
}
v_resetjp_4659_:
{
lean_object* v___x_4663_; 
if (v_isShared_4661_ == 0)
{
v___x_4663_ = v___x_4660_;
goto v_reusejp_4662_;
}
else
{
lean_object* v_reuseFailAlloc_4664_; 
v_reuseFailAlloc_4664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4664_, 0, v_a_4658_);
v___x_4663_ = v_reuseFailAlloc_4664_;
goto v_reusejp_4662_;
}
v_reusejp_4662_:
{
return v___x_4663_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f___redArg___boxed(lean_object* v_e_4666_, lean_object* v_a_4667_, lean_object* v_a_4668_, lean_object* v_a_4669_){
_start:
{
lean_object* v_res_4670_; 
v_res_4670_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f___redArg(v_e_4666_, v_a_4667_, v_a_4668_);
lean_dec_ref(v_a_4668_);
lean_dec(v_a_4667_);
lean_dec_ref(v_e_4666_);
return v_res_4670_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f(lean_object* v_e_4671_, lean_object* v_a_4672_, lean_object* v_a_4673_, lean_object* v_a_4674_, lean_object* v_a_4675_, lean_object* v_a_4676_, lean_object* v_a_4677_, lean_object* v_a_4678_, lean_object* v_a_4679_, lean_object* v_a_4680_, lean_object* v_a_4681_){
_start:
{
lean_object* v___x_4683_; 
v___x_4683_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f___redArg(v_e_4671_, v_a_4672_, v_a_4680_);
return v___x_4683_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f___boxed(lean_object* v_e_4684_, lean_object* v_a_4685_, lean_object* v_a_4686_, lean_object* v_a_4687_, lean_object* v_a_4688_, lean_object* v_a_4689_, lean_object* v_a_4690_, lean_object* v_a_4691_, lean_object* v_a_4692_, lean_object* v_a_4693_, lean_object* v_a_4694_, lean_object* v_a_4695_){
_start:
{
lean_object* v_res_4696_; 
v_res_4696_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f(v_e_4684_, v_a_4685_, v_a_4686_, v_a_4687_, v_a_4688_, v_a_4689_, v_a_4690_, v_a_4691_, v_a_4692_, v_a_4693_, v_a_4694_);
lean_dec(v_a_4694_);
lean_dec_ref(v_a_4693_);
lean_dec(v_a_4692_);
lean_dec_ref(v_a_4691_);
lean_dec(v_a_4690_);
lean_dec_ref(v_a_4689_);
lean_dec(v_a_4688_);
lean_dec_ref(v_a_4687_);
lean_dec(v_a_4686_);
lean_dec(v_a_4685_);
lean_dec_ref(v_e_4684_);
return v_res_4696_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__8(void){
_start:
{
uint8_t v___x_4721_; lean_object* v___x_4722_; lean_object* v___x_4723_; 
v___x_4721_ = 0;
v___x_4722_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4);
v___x_4723_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4723_, 0, v___x_4722_);
lean_ctor_set_uint8(v___x_4723_, sizeof(void*)*1, v___x_4721_);
return v___x_4723_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__10(void){
_start:
{
lean_object* v___x_4725_; lean_object* v___x_4726_; 
v___x_4725_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__9));
v___x_4726_ = l_Lean_stringToMessageData(v___x_4725_);
return v___x_4726_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go(lean_object* v_a_4727_, lean_object* v_b_4728_, lean_object* v_h_4729_, lean_object* v_a_4730_, lean_object* v_a_4731_, lean_object* v_a_4732_, lean_object* v_a_4733_, lean_object* v_a_4734_, lean_object* v_a_4735_, lean_object* v_a_4736_, lean_object* v_a_4737_, lean_object* v_a_4738_, lean_object* v_a_4739_){
_start:
{
lean_object* v___y_4742_; lean_object* v___y_4743_; lean_object* v___y_4744_; lean_object* v___y_4745_; lean_object* v___y_4746_; lean_object* v___y_4747_; lean_object* v___y_4748_; lean_object* v___y_4749_; lean_object* v___y_4750_; lean_object* v___y_4751_; lean_object* v___y_4752_; lean_object* v___x_4840_; 
v___x_4840_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___redArg(v_a_4727_, v_a_4730_, v_a_4738_);
if (lean_obj_tag(v___x_4840_) == 0)
{
lean_object* v_a_4841_; lean_object* v___x_4843_; uint8_t v_isShared_4844_; uint8_t v_isSharedCheck_4886_; 
v_a_4841_ = lean_ctor_get(v___x_4840_, 0);
v_isSharedCheck_4886_ = !lean_is_exclusive(v___x_4840_);
if (v_isSharedCheck_4886_ == 0)
{
v___x_4843_ = v___x_4840_;
v_isShared_4844_ = v_isSharedCheck_4886_;
goto v_resetjp_4842_;
}
else
{
lean_inc(v_a_4841_);
lean_dec(v___x_4840_);
v___x_4843_ = lean_box(0);
v_isShared_4844_ = v_isSharedCheck_4886_;
goto v_resetjp_4842_;
}
v_resetjp_4842_:
{
if (lean_obj_tag(v_a_4841_) == 1)
{
lean_object* v_val_4845_; lean_object* v___x_4846_; 
lean_del_object(v___x_4843_);
v_val_4845_ = lean_ctor_get(v_a_4841_, 0);
lean_inc(v_val_4845_);
lean_dec_ref(v_a_4841_);
v___x_4846_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___redArg(v_b_4728_, v_a_4730_, v_a_4738_);
if (lean_obj_tag(v___x_4846_) == 0)
{
lean_object* v_a_4847_; lean_object* v___x_4849_; uint8_t v_isShared_4850_; uint8_t v_isSharedCheck_4873_; 
v_a_4847_ = lean_ctor_get(v___x_4846_, 0);
v_isSharedCheck_4873_ = !lean_is_exclusive(v___x_4846_);
if (v_isSharedCheck_4873_ == 0)
{
v___x_4849_ = v___x_4846_;
v_isShared_4850_ = v_isSharedCheck_4873_;
goto v_resetjp_4848_;
}
else
{
lean_inc(v_a_4847_);
lean_dec(v___x_4846_);
v___x_4849_ = lean_box(0);
v_isShared_4850_ = v_isSharedCheck_4873_;
goto v_resetjp_4848_;
}
v_resetjp_4848_:
{
if (lean_obj_tag(v_a_4847_) == 1)
{
lean_object* v_val_4851_; uint8_t v___x_4852_; 
v_val_4851_ = lean_ctor_get(v_a_4847_, 0);
lean_inc(v_val_4851_);
lean_dec_ref(v_a_4847_);
v___x_4852_ = lean_nat_dec_eq(v_val_4845_, v_val_4851_);
lean_dec(v_val_4851_);
if (v___x_4852_ == 0)
{
lean_object* v___x_4853_; lean_object* v___x_4855_; 
lean_dec(v_val_4845_);
lean_dec_ref(v_h_4729_);
lean_dec_ref(v_b_4728_);
lean_dec_ref(v_a_4727_);
v___x_4853_ = lean_box(0);
if (v_isShared_4850_ == 0)
{
lean_ctor_set(v___x_4849_, 0, v___x_4853_);
v___x_4855_ = v___x_4849_;
goto v_reusejp_4854_;
}
else
{
lean_object* v_reuseFailAlloc_4856_; 
v_reuseFailAlloc_4856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4856_, 0, v___x_4853_);
v___x_4855_ = v_reuseFailAlloc_4856_;
goto v_reusejp_4854_;
}
v_reusejp_4854_:
{
return v___x_4855_;
}
}
else
{
lean_object* v_options_4857_; uint8_t v_hasTrace_4858_; 
lean_del_object(v___x_4849_);
v_options_4857_ = lean_ctor_get(v_a_4738_, 2);
v_hasTrace_4858_ = lean_ctor_get_uint8(v_options_4857_, sizeof(void*)*1);
if (v_hasTrace_4858_ == 0)
{
v___y_4742_ = v_val_4845_;
v___y_4743_ = v_a_4730_;
v___y_4744_ = v_a_4731_;
v___y_4745_ = v_a_4732_;
v___y_4746_ = v_a_4733_;
v___y_4747_ = v_a_4734_;
v___y_4748_ = v_a_4735_;
v___y_4749_ = v_a_4736_;
v___y_4750_ = v_a_4737_;
v___y_4751_ = v_a_4738_;
v___y_4752_ = v_a_4739_;
goto v___jp_4741_;
}
else
{
lean_object* v_inheritedTraceOptions_4859_; lean_object* v___x_4860_; lean_object* v___x_4861_; uint8_t v___x_4862_; 
v_inheritedTraceOptions_4859_ = lean_ctor_get(v_a_4738_, 13);
v___x_4860_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__4));
v___x_4861_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5);
v___x_4862_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4859_, v_options_4857_, v___x_4861_);
if (v___x_4862_ == 0)
{
v___y_4742_ = v_val_4845_;
v___y_4743_ = v_a_4730_;
v___y_4744_ = v_a_4731_;
v___y_4745_ = v_a_4732_;
v___y_4746_ = v_a_4733_;
v___y_4747_ = v_a_4734_;
v___y_4748_ = v_a_4735_;
v___y_4749_ = v_a_4736_;
v___y_4750_ = v_a_4737_;
v___y_4751_ = v_a_4738_;
v___y_4752_ = v_a_4739_;
goto v___jp_4741_;
}
else
{
lean_object* v___x_4863_; lean_object* v___x_4864_; lean_object* v___x_4865_; lean_object* v___x_4866_; lean_object* v___x_4867_; lean_object* v___x_4868_; 
lean_inc_ref(v_a_4727_);
v___x_4863_ = l_Lean_MessageData_ofExpr(v_a_4727_);
v___x_4864_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__10, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__10);
v___x_4865_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4865_, 0, v___x_4863_);
lean_ctor_set(v___x_4865_, 1, v___x_4864_);
lean_inc_ref(v_b_4728_);
v___x_4866_ = l_Lean_MessageData_ofExpr(v_b_4728_);
v___x_4867_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4867_, 0, v___x_4865_);
lean_ctor_set(v___x_4867_, 1, v___x_4866_);
v___x_4868_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(v___x_4860_, v___x_4867_, v_a_4736_, v_a_4737_, v_a_4738_, v_a_4739_);
if (lean_obj_tag(v___x_4868_) == 0)
{
lean_dec_ref(v___x_4868_);
v___y_4742_ = v_val_4845_;
v___y_4743_ = v_a_4730_;
v___y_4744_ = v_a_4731_;
v___y_4745_ = v_a_4732_;
v___y_4746_ = v_a_4733_;
v___y_4747_ = v_a_4734_;
v___y_4748_ = v_a_4735_;
v___y_4749_ = v_a_4736_;
v___y_4750_ = v_a_4737_;
v___y_4751_ = v_a_4738_;
v___y_4752_ = v_a_4739_;
goto v___jp_4741_;
}
else
{
lean_dec(v_val_4845_);
lean_dec_ref(v_h_4729_);
lean_dec_ref(v_b_4728_);
lean_dec_ref(v_a_4727_);
return v___x_4868_;
}
}
}
}
}
else
{
lean_object* v___x_4869_; lean_object* v___x_4871_; 
lean_dec(v_a_4847_);
lean_dec(v_val_4845_);
lean_dec_ref(v_h_4729_);
lean_dec_ref(v_b_4728_);
lean_dec_ref(v_a_4727_);
v___x_4869_ = lean_box(0);
if (v_isShared_4850_ == 0)
{
lean_ctor_set(v___x_4849_, 0, v___x_4869_);
v___x_4871_ = v___x_4849_;
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
lean_dec(v_val_4845_);
lean_dec_ref(v_h_4729_);
lean_dec_ref(v_b_4728_);
lean_dec_ref(v_a_4727_);
v_a_4874_ = lean_ctor_get(v___x_4846_, 0);
v_isSharedCheck_4881_ = !lean_is_exclusive(v___x_4846_);
if (v_isSharedCheck_4881_ == 0)
{
v___x_4876_ = v___x_4846_;
v_isShared_4877_ = v_isSharedCheck_4881_;
goto v_resetjp_4875_;
}
else
{
lean_inc(v_a_4874_);
lean_dec(v___x_4846_);
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
}
else
{
lean_object* v___x_4882_; lean_object* v___x_4884_; 
lean_dec(v_a_4841_);
lean_dec_ref(v_h_4729_);
lean_dec_ref(v_b_4728_);
lean_dec_ref(v_a_4727_);
v___x_4882_ = lean_box(0);
if (v_isShared_4844_ == 0)
{
lean_ctor_set(v___x_4843_, 0, v___x_4882_);
v___x_4884_ = v___x_4843_;
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
lean_dec_ref(v_h_4729_);
lean_dec_ref(v_b_4728_);
lean_dec_ref(v_a_4727_);
v_a_4887_ = lean_ctor_get(v___x_4840_, 0);
v_isSharedCheck_4894_ = !lean_is_exclusive(v___x_4840_);
if (v_isSharedCheck_4894_ == 0)
{
v___x_4889_ = v___x_4840_;
v_isShared_4890_ = v_isSharedCheck_4894_;
goto v_resetjp_4888_;
}
else
{
lean_inc(v_a_4887_);
lean_dec(v___x_4840_);
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
v___jp_4741_:
{
lean_object* v___x_4753_; 
lean_inc_ref(v_a_4727_);
v___x_4753_ = l_Lean_Meta_Grind_Order_getNodeId(v_a_4727_, v___y_4742_, v___y_4743_, v___y_4744_, v___y_4745_, v___y_4746_, v___y_4747_, v___y_4748_, v___y_4749_, v___y_4750_, v___y_4751_, v___y_4752_);
if (lean_obj_tag(v___x_4753_) == 0)
{
lean_object* v_a_4754_; lean_object* v___x_4755_; 
v_a_4754_ = lean_ctor_get(v___x_4753_, 0);
lean_inc(v_a_4754_);
lean_dec_ref(v___x_4753_);
lean_inc_ref(v_b_4728_);
v___x_4755_ = l_Lean_Meta_Grind_Order_getNodeId(v_b_4728_, v___y_4742_, v___y_4743_, v___y_4744_, v___y_4745_, v___y_4746_, v___y_4747_, v___y_4748_, v___y_4749_, v___y_4750_, v___y_4751_, v___y_4752_);
if (lean_obj_tag(v___x_4755_) == 0)
{
lean_object* v_a_4756_; lean_object* v___x_4757_; 
v_a_4756_ = lean_ctor_get(v___x_4755_, 0);
lean_inc(v_a_4756_);
lean_dec_ref(v___x_4755_);
v___x_4757_ = l_Lean_Meta_Grind_Order_isRing(v___y_4742_, v___y_4743_, v___y_4744_, v___y_4745_, v___y_4746_, v___y_4747_, v___y_4748_, v___y_4749_, v___y_4750_, v___y_4751_, v___y_4752_);
if (lean_obj_tag(v___x_4757_) == 0)
{
lean_object* v_a_4758_; uint8_t v___x_4759_; 
v_a_4758_ = lean_ctor_get(v___x_4757_, 0);
lean_inc(v_a_4758_);
lean_dec_ref(v___x_4757_);
v___x_4759_ = lean_unbox(v_a_4758_);
if (v___x_4759_ == 0)
{
lean_object* v___x_4760_; lean_object* v___x_4761_; 
v___x_4760_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__1));
v___x_4761_ = l_Lean_Meta_Grind_Order_mkLePreorderPrefix(v___x_4760_, v___y_4742_, v___y_4743_, v___y_4744_, v___y_4745_, v___y_4746_, v___y_4747_, v___y_4748_, v___y_4749_, v___y_4750_, v___y_4751_, v___y_4752_);
if (lean_obj_tag(v___x_4761_) == 0)
{
lean_object* v_a_4762_; lean_object* v___x_4763_; lean_object* v___x_4764_; 
v_a_4762_ = lean_ctor_get(v___x_4761_, 0);
lean_inc(v_a_4762_);
lean_dec_ref(v___x_4761_);
v___x_4763_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__3));
v___x_4764_ = l_Lean_Meta_Grind_Order_mkLePreorderPrefix(v___x_4763_, v___y_4742_, v___y_4743_, v___y_4744_, v___y_4745_, v___y_4746_, v___y_4747_, v___y_4748_, v___y_4749_, v___y_4750_, v___y_4751_, v___y_4752_);
if (lean_obj_tag(v___x_4764_) == 0)
{
lean_object* v_a_4765_; lean_object* v___x_4766_; lean_object* v___x_4767_; lean_object* v___x_4768_; uint8_t v___x_4769_; lean_object* v___x_4770_; 
v_a_4765_ = lean_ctor_get(v___x_4764_, 0);
lean_inc(v_a_4765_);
lean_dec_ref(v___x_4764_);
lean_inc_ref(v_h_4729_);
lean_inc_ref(v_b_4728_);
lean_inc_ref(v_a_4727_);
v___x_4766_ = l_Lean_mkApp3(v_a_4762_, v_a_4727_, v_b_4728_, v_h_4729_);
v___x_4767_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4);
v___x_4768_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4768_, 0, v___x_4767_);
v___x_4769_ = lean_unbox(v_a_4758_);
lean_dec(v_a_4758_);
lean_ctor_set_uint8(v___x_4768_, sizeof(void*)*1, v___x_4769_);
lean_inc_ref(v___x_4768_);
lean_inc(v_a_4756_);
lean_inc(v_a_4754_);
v___x_4770_ = l_Lean_Meta_Grind_Order_addEdge(v_a_4754_, v_a_4756_, v___x_4768_, v___x_4766_, v___y_4742_, v___y_4743_, v___y_4744_, v___y_4745_, v___y_4746_, v___y_4747_, v___y_4748_, v___y_4749_, v___y_4750_, v___y_4751_, v___y_4752_);
if (lean_obj_tag(v___x_4770_) == 0)
{
lean_object* v___x_4771_; lean_object* v___x_4772_; 
lean_dec_ref(v___x_4770_);
v___x_4771_ = l_Lean_mkApp3(v_a_4765_, v_a_4727_, v_b_4728_, v_h_4729_);
v___x_4772_ = l_Lean_Meta_Grind_Order_addEdge(v_a_4756_, v_a_4754_, v___x_4768_, v___x_4771_, v___y_4742_, v___y_4743_, v___y_4744_, v___y_4745_, v___y_4746_, v___y_4747_, v___y_4748_, v___y_4749_, v___y_4750_, v___y_4751_, v___y_4752_);
lean_dec(v___y_4742_);
return v___x_4772_;
}
else
{
lean_dec_ref(v___x_4768_);
lean_dec(v_a_4765_);
lean_dec(v_a_4756_);
lean_dec(v_a_4754_);
lean_dec(v___y_4742_);
lean_dec_ref(v_h_4729_);
lean_dec_ref(v_b_4728_);
lean_dec_ref(v_a_4727_);
return v___x_4770_;
}
}
else
{
lean_object* v_a_4773_; lean_object* v___x_4775_; uint8_t v_isShared_4776_; uint8_t v_isSharedCheck_4780_; 
lean_dec(v_a_4762_);
lean_dec(v_a_4758_);
lean_dec(v_a_4756_);
lean_dec(v_a_4754_);
lean_dec(v___y_4742_);
lean_dec_ref(v_h_4729_);
lean_dec_ref(v_b_4728_);
lean_dec_ref(v_a_4727_);
v_a_4773_ = lean_ctor_get(v___x_4764_, 0);
v_isSharedCheck_4780_ = !lean_is_exclusive(v___x_4764_);
if (v_isSharedCheck_4780_ == 0)
{
v___x_4775_ = v___x_4764_;
v_isShared_4776_ = v_isSharedCheck_4780_;
goto v_resetjp_4774_;
}
else
{
lean_inc(v_a_4773_);
lean_dec(v___x_4764_);
v___x_4775_ = lean_box(0);
v_isShared_4776_ = v_isSharedCheck_4780_;
goto v_resetjp_4774_;
}
v_resetjp_4774_:
{
lean_object* v___x_4778_; 
if (v_isShared_4776_ == 0)
{
v___x_4778_ = v___x_4775_;
goto v_reusejp_4777_;
}
else
{
lean_object* v_reuseFailAlloc_4779_; 
v_reuseFailAlloc_4779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4779_, 0, v_a_4773_);
v___x_4778_ = v_reuseFailAlloc_4779_;
goto v_reusejp_4777_;
}
v_reusejp_4777_:
{
return v___x_4778_;
}
}
}
}
else
{
lean_object* v_a_4781_; lean_object* v___x_4783_; uint8_t v_isShared_4784_; uint8_t v_isSharedCheck_4788_; 
lean_dec(v_a_4758_);
lean_dec(v_a_4756_);
lean_dec(v_a_4754_);
lean_dec(v___y_4742_);
lean_dec_ref(v_h_4729_);
lean_dec_ref(v_b_4728_);
lean_dec_ref(v_a_4727_);
v_a_4781_ = lean_ctor_get(v___x_4761_, 0);
v_isSharedCheck_4788_ = !lean_is_exclusive(v___x_4761_);
if (v_isSharedCheck_4788_ == 0)
{
v___x_4783_ = v___x_4761_;
v_isShared_4784_ = v_isSharedCheck_4788_;
goto v_resetjp_4782_;
}
else
{
lean_inc(v_a_4781_);
lean_dec(v___x_4761_);
v___x_4783_ = lean_box(0);
v_isShared_4784_ = v_isSharedCheck_4788_;
goto v_resetjp_4782_;
}
v_resetjp_4782_:
{
lean_object* v___x_4786_; 
if (v_isShared_4784_ == 0)
{
v___x_4786_ = v___x_4783_;
goto v_reusejp_4785_;
}
else
{
lean_object* v_reuseFailAlloc_4787_; 
v_reuseFailAlloc_4787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4787_, 0, v_a_4781_);
v___x_4786_ = v_reuseFailAlloc_4787_;
goto v_reusejp_4785_;
}
v_reusejp_4785_:
{
return v___x_4786_;
}
}
}
}
else
{
lean_object* v___x_4789_; lean_object* v___x_4790_; 
lean_dec(v_a_4758_);
v___x_4789_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__5));
v___x_4790_ = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(v___x_4789_, v___y_4742_, v___y_4743_, v___y_4744_, v___y_4745_, v___y_4746_, v___y_4747_, v___y_4748_, v___y_4749_, v___y_4750_, v___y_4751_, v___y_4752_);
if (lean_obj_tag(v___x_4790_) == 0)
{
lean_object* v_a_4791_; lean_object* v___x_4792_; lean_object* v___x_4793_; 
v_a_4791_ = lean_ctor_get(v___x_4790_, 0);
lean_inc(v_a_4791_);
lean_dec_ref(v___x_4790_);
v___x_4792_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__7));
v___x_4793_ = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(v___x_4792_, v___y_4742_, v___y_4743_, v___y_4744_, v___y_4745_, v___y_4746_, v___y_4747_, v___y_4748_, v___y_4749_, v___y_4750_, v___y_4751_, v___y_4752_);
if (lean_obj_tag(v___x_4793_) == 0)
{
lean_object* v_a_4794_; lean_object* v___x_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; 
v_a_4794_ = lean_ctor_get(v___x_4793_, 0);
lean_inc(v_a_4794_);
lean_dec_ref(v___x_4793_);
lean_inc_ref(v_h_4729_);
lean_inc_ref(v_b_4728_);
lean_inc_ref(v_a_4727_);
v___x_4795_ = l_Lean_mkApp3(v_a_4791_, v_a_4727_, v_b_4728_, v_h_4729_);
v___x_4796_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__8, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__8);
lean_inc(v_a_4756_);
lean_inc(v_a_4754_);
v___x_4797_ = l_Lean_Meta_Grind_Order_addEdge(v_a_4754_, v_a_4756_, v___x_4796_, v___x_4795_, v___y_4742_, v___y_4743_, v___y_4744_, v___y_4745_, v___y_4746_, v___y_4747_, v___y_4748_, v___y_4749_, v___y_4750_, v___y_4751_, v___y_4752_);
if (lean_obj_tag(v___x_4797_) == 0)
{
lean_object* v___x_4798_; lean_object* v___x_4799_; 
lean_dec_ref(v___x_4797_);
v___x_4798_ = l_Lean_mkApp3(v_a_4794_, v_a_4727_, v_b_4728_, v_h_4729_);
v___x_4799_ = l_Lean_Meta_Grind_Order_addEdge(v_a_4756_, v_a_4754_, v___x_4796_, v___x_4798_, v___y_4742_, v___y_4743_, v___y_4744_, v___y_4745_, v___y_4746_, v___y_4747_, v___y_4748_, v___y_4749_, v___y_4750_, v___y_4751_, v___y_4752_);
lean_dec(v___y_4742_);
return v___x_4799_;
}
else
{
lean_dec(v_a_4794_);
lean_dec(v_a_4756_);
lean_dec(v_a_4754_);
lean_dec(v___y_4742_);
lean_dec_ref(v_h_4729_);
lean_dec_ref(v_b_4728_);
lean_dec_ref(v_a_4727_);
return v___x_4797_;
}
}
else
{
lean_object* v_a_4800_; lean_object* v___x_4802_; uint8_t v_isShared_4803_; uint8_t v_isSharedCheck_4807_; 
lean_dec(v_a_4791_);
lean_dec(v_a_4756_);
lean_dec(v_a_4754_);
lean_dec(v___y_4742_);
lean_dec_ref(v_h_4729_);
lean_dec_ref(v_b_4728_);
lean_dec_ref(v_a_4727_);
v_a_4800_ = lean_ctor_get(v___x_4793_, 0);
v_isSharedCheck_4807_ = !lean_is_exclusive(v___x_4793_);
if (v_isSharedCheck_4807_ == 0)
{
v___x_4802_ = v___x_4793_;
v_isShared_4803_ = v_isSharedCheck_4807_;
goto v_resetjp_4801_;
}
else
{
lean_inc(v_a_4800_);
lean_dec(v___x_4793_);
v___x_4802_ = lean_box(0);
v_isShared_4803_ = v_isSharedCheck_4807_;
goto v_resetjp_4801_;
}
v_resetjp_4801_:
{
lean_object* v___x_4805_; 
if (v_isShared_4803_ == 0)
{
v___x_4805_ = v___x_4802_;
goto v_reusejp_4804_;
}
else
{
lean_object* v_reuseFailAlloc_4806_; 
v_reuseFailAlloc_4806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4806_, 0, v_a_4800_);
v___x_4805_ = v_reuseFailAlloc_4806_;
goto v_reusejp_4804_;
}
v_reusejp_4804_:
{
return v___x_4805_;
}
}
}
}
else
{
lean_object* v_a_4808_; lean_object* v___x_4810_; uint8_t v_isShared_4811_; uint8_t v_isSharedCheck_4815_; 
lean_dec(v_a_4756_);
lean_dec(v_a_4754_);
lean_dec(v___y_4742_);
lean_dec_ref(v_h_4729_);
lean_dec_ref(v_b_4728_);
lean_dec_ref(v_a_4727_);
v_a_4808_ = lean_ctor_get(v___x_4790_, 0);
v_isSharedCheck_4815_ = !lean_is_exclusive(v___x_4790_);
if (v_isSharedCheck_4815_ == 0)
{
v___x_4810_ = v___x_4790_;
v_isShared_4811_ = v_isSharedCheck_4815_;
goto v_resetjp_4809_;
}
else
{
lean_inc(v_a_4808_);
lean_dec(v___x_4790_);
v___x_4810_ = lean_box(0);
v_isShared_4811_ = v_isSharedCheck_4815_;
goto v_resetjp_4809_;
}
v_resetjp_4809_:
{
lean_object* v___x_4813_; 
if (v_isShared_4811_ == 0)
{
v___x_4813_ = v___x_4810_;
goto v_reusejp_4812_;
}
else
{
lean_object* v_reuseFailAlloc_4814_; 
v_reuseFailAlloc_4814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4814_, 0, v_a_4808_);
v___x_4813_ = v_reuseFailAlloc_4814_;
goto v_reusejp_4812_;
}
v_reusejp_4812_:
{
return v___x_4813_;
}
}
}
}
}
else
{
lean_object* v_a_4816_; lean_object* v___x_4818_; uint8_t v_isShared_4819_; uint8_t v_isSharedCheck_4823_; 
lean_dec(v_a_4756_);
lean_dec(v_a_4754_);
lean_dec(v___y_4742_);
lean_dec_ref(v_h_4729_);
lean_dec_ref(v_b_4728_);
lean_dec_ref(v_a_4727_);
v_a_4816_ = lean_ctor_get(v___x_4757_, 0);
v_isSharedCheck_4823_ = !lean_is_exclusive(v___x_4757_);
if (v_isSharedCheck_4823_ == 0)
{
v___x_4818_ = v___x_4757_;
v_isShared_4819_ = v_isSharedCheck_4823_;
goto v_resetjp_4817_;
}
else
{
lean_inc(v_a_4816_);
lean_dec(v___x_4757_);
v___x_4818_ = lean_box(0);
v_isShared_4819_ = v_isSharedCheck_4823_;
goto v_resetjp_4817_;
}
v_resetjp_4817_:
{
lean_object* v___x_4821_; 
if (v_isShared_4819_ == 0)
{
v___x_4821_ = v___x_4818_;
goto v_reusejp_4820_;
}
else
{
lean_object* v_reuseFailAlloc_4822_; 
v_reuseFailAlloc_4822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4822_, 0, v_a_4816_);
v___x_4821_ = v_reuseFailAlloc_4822_;
goto v_reusejp_4820_;
}
v_reusejp_4820_:
{
return v___x_4821_;
}
}
}
}
else
{
lean_object* v_a_4824_; lean_object* v___x_4826_; uint8_t v_isShared_4827_; uint8_t v_isSharedCheck_4831_; 
lean_dec(v_a_4754_);
lean_dec(v___y_4742_);
lean_dec_ref(v_h_4729_);
lean_dec_ref(v_b_4728_);
lean_dec_ref(v_a_4727_);
v_a_4824_ = lean_ctor_get(v___x_4755_, 0);
v_isSharedCheck_4831_ = !lean_is_exclusive(v___x_4755_);
if (v_isSharedCheck_4831_ == 0)
{
v___x_4826_ = v___x_4755_;
v_isShared_4827_ = v_isSharedCheck_4831_;
goto v_resetjp_4825_;
}
else
{
lean_inc(v_a_4824_);
lean_dec(v___x_4755_);
v___x_4826_ = lean_box(0);
v_isShared_4827_ = v_isSharedCheck_4831_;
goto v_resetjp_4825_;
}
v_resetjp_4825_:
{
lean_object* v___x_4829_; 
if (v_isShared_4827_ == 0)
{
v___x_4829_ = v___x_4826_;
goto v_reusejp_4828_;
}
else
{
lean_object* v_reuseFailAlloc_4830_; 
v_reuseFailAlloc_4830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4830_, 0, v_a_4824_);
v___x_4829_ = v_reuseFailAlloc_4830_;
goto v_reusejp_4828_;
}
v_reusejp_4828_:
{
return v___x_4829_;
}
}
}
}
else
{
lean_object* v_a_4832_; lean_object* v___x_4834_; uint8_t v_isShared_4835_; uint8_t v_isSharedCheck_4839_; 
lean_dec(v___y_4742_);
lean_dec_ref(v_h_4729_);
lean_dec_ref(v_b_4728_);
lean_dec_ref(v_a_4727_);
v_a_4832_ = lean_ctor_get(v___x_4753_, 0);
v_isSharedCheck_4839_ = !lean_is_exclusive(v___x_4753_);
if (v_isSharedCheck_4839_ == 0)
{
v___x_4834_ = v___x_4753_;
v_isShared_4835_ = v_isSharedCheck_4839_;
goto v_resetjp_4833_;
}
else
{
lean_inc(v_a_4832_);
lean_dec(v___x_4753_);
v___x_4834_ = lean_box(0);
v_isShared_4835_ = v_isSharedCheck_4839_;
goto v_resetjp_4833_;
}
v_resetjp_4833_:
{
lean_object* v___x_4837_; 
if (v_isShared_4835_ == 0)
{
v___x_4837_ = v___x_4834_;
goto v_reusejp_4836_;
}
else
{
lean_object* v_reuseFailAlloc_4838_; 
v_reuseFailAlloc_4838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4838_, 0, v_a_4832_);
v___x_4837_ = v_reuseFailAlloc_4838_;
goto v_reusejp_4836_;
}
v_reusejp_4836_:
{
return v___x_4837_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___boxed(lean_object* v_a_4895_, lean_object* v_b_4896_, lean_object* v_h_4897_, lean_object* v_a_4898_, lean_object* v_a_4899_, lean_object* v_a_4900_, lean_object* v_a_4901_, lean_object* v_a_4902_, lean_object* v_a_4903_, lean_object* v_a_4904_, lean_object* v_a_4905_, lean_object* v_a_4906_, lean_object* v_a_4907_, lean_object* v_a_4908_){
_start:
{
lean_object* v_res_4909_; 
v_res_4909_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go(v_a_4895_, v_b_4896_, v_h_4897_, v_a_4898_, v_a_4899_, v_a_4900_, v_a_4901_, v_a_4902_, v_a_4903_, v_a_4904_, v_a_4905_, v_a_4906_, v_a_4907_);
lean_dec(v_a_4907_);
lean_dec_ref(v_a_4906_);
lean_dec(v_a_4905_);
lean_dec_ref(v_a_4904_);
lean_dec(v_a_4903_);
lean_dec_ref(v_a_4902_);
lean_dec(v_a_4901_);
lean_dec_ref(v_a_4900_);
lean_dec(v_a_4899_);
lean_dec(v_a_4898_);
return v_res_4909_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_processNewEq___closed__6(void){
_start:
{
lean_object* v___x_4925_; lean_object* v___x_4926_; lean_object* v___x_4927_; 
v___x_4925_ = lean_box(0);
v___x_4926_ = ((lean_object*)(l_Lean_Meta_Grind_Order_processNewEq___closed__5));
v___x_4927_ = l_Lean_mkConst(v___x_4926_, v___x_4925_);
return v___x_4927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_processNewEq(lean_object* v_a_4928_, lean_object* v_b_4929_, lean_object* v_a_4930_, lean_object* v_a_4931_, lean_object* v_a_4932_, lean_object* v_a_4933_, lean_object* v_a_4934_, lean_object* v_a_4935_, lean_object* v_a_4936_, lean_object* v_a_4937_, lean_object* v_a_4938_, lean_object* v_a_4939_){
_start:
{
uint8_t v___x_4941_; 
v___x_4941_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_a_4928_, v_b_4929_);
if (v___x_4941_ == 0)
{
lean_object* v___x_4942_; 
lean_inc(v_a_4939_);
lean_inc_ref(v_a_4938_);
lean_inc(v_a_4937_);
lean_inc_ref(v_a_4936_);
lean_inc(v_a_4935_);
lean_inc_ref(v_a_4934_);
lean_inc(v_a_4933_);
lean_inc_ref(v_a_4932_);
lean_inc(v_a_4931_);
lean_inc(v_a_4930_);
lean_inc_ref(v_b_4929_);
lean_inc_ref(v_a_4928_);
v___x_4942_ = lean_grind_mk_eq_proof(v_a_4928_, v_b_4929_, v_a_4930_, v_a_4931_, v_a_4932_, v_a_4933_, v_a_4934_, v_a_4935_, v_a_4936_, v_a_4937_, v_a_4938_, v_a_4939_);
if (lean_obj_tag(v___x_4942_) == 0)
{
lean_object* v_a_4943_; lean_object* v___x_4944_; 
v_a_4943_ = lean_ctor_get(v___x_4942_, 0);
lean_inc(v_a_4943_);
lean_dec_ref(v___x_4942_);
v___x_4944_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f___redArg(v_a_4928_, v_a_4930_, v_a_4938_);
if (lean_obj_tag(v___x_4944_) == 0)
{
lean_object* v_a_4945_; 
v_a_4945_ = lean_ctor_get(v___x_4944_, 0);
lean_inc(v_a_4945_);
lean_dec_ref(v___x_4944_);
if (lean_obj_tag(v_a_4945_) == 1)
{
lean_object* v_val_4946_; lean_object* v_e_4947_; lean_object* v_h_4948_; lean_object* v_00_u03b1_4949_; lean_object* v___x_4950_; 
v_val_4946_ = lean_ctor_get(v_a_4945_, 0);
lean_inc(v_val_4946_);
lean_dec_ref(v_a_4945_);
v_e_4947_ = lean_ctor_get(v_val_4946_, 0);
lean_inc_ref(v_e_4947_);
v_h_4948_ = lean_ctor_get(v_val_4946_, 1);
lean_inc_ref(v_h_4948_);
v_00_u03b1_4949_ = lean_ctor_get(v_val_4946_, 2);
lean_inc_ref(v_00_u03b1_4949_);
lean_dec(v_val_4946_);
v___x_4950_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f___redArg(v_b_4929_, v_a_4930_, v_a_4938_);
if (lean_obj_tag(v___x_4950_) == 0)
{
lean_object* v_a_4951_; lean_object* v___x_4953_; uint8_t v_isShared_4954_; uint8_t v_isSharedCheck_4996_; 
v_a_4951_ = lean_ctor_get(v___x_4950_, 0);
v_isSharedCheck_4996_ = !lean_is_exclusive(v___x_4950_);
if (v_isSharedCheck_4996_ == 0)
{
v___x_4953_ = v___x_4950_;
v_isShared_4954_ = v_isSharedCheck_4996_;
goto v_resetjp_4952_;
}
else
{
lean_inc(v_a_4951_);
lean_dec(v___x_4950_);
v___x_4953_ = lean_box(0);
v_isShared_4954_ = v_isSharedCheck_4996_;
goto v_resetjp_4952_;
}
v_resetjp_4952_:
{
if (lean_obj_tag(v_a_4951_) == 1)
{
lean_object* v_val_4955_; lean_object* v_e_4956_; lean_object* v_h_4957_; lean_object* v___x_4958_; uint8_t v___x_4959_; 
lean_del_object(v___x_4953_);
v_val_4955_ = lean_ctor_get(v_a_4951_, 0);
lean_inc(v_val_4955_);
lean_dec_ref(v_a_4951_);
v_e_4956_ = lean_ctor_get(v_val_4955_, 0);
lean_inc_ref(v_e_4956_);
v_h_4957_ = lean_ctor_get(v_val_4955_, 1);
lean_inc_ref(v_h_4957_);
lean_dec(v_val_4955_);
v___x_4958_ = l_Lean_Int_mkType;
v___x_4959_ = lean_expr_eqv(v_00_u03b1_4949_, v___x_4958_);
if (v___x_4959_ == 0)
{
lean_object* v___x_4960_; 
lean_inc_ref(v_00_u03b1_4949_);
v___x_4960_ = l_Lean_Meta_getDecLevel(v_00_u03b1_4949_, v_a_4936_, v_a_4937_, v_a_4938_, v_a_4939_);
if (lean_obj_tag(v___x_4960_) == 0)
{
lean_object* v_a_4961_; lean_object* v___x_4962_; lean_object* v___x_4963_; lean_object* v___x_4964_; lean_object* v___x_4965_; lean_object* v___x_4966_; lean_object* v___x_4967_; 
v_a_4961_ = lean_ctor_get(v___x_4960_, 0);
lean_inc(v_a_4961_);
lean_dec_ref(v___x_4960_);
v___x_4962_ = ((lean_object*)(l_Lean_Meta_Grind_Order_processNewEq___closed__1));
v___x_4963_ = lean_box(0);
v___x_4964_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4964_, 0, v_a_4961_);
lean_ctor_set(v___x_4964_, 1, v___x_4963_);
lean_inc_ref(v___x_4964_);
v___x_4965_ = l_Lean_mkConst(v___x_4962_, v___x_4964_);
lean_inc_ref(v_00_u03b1_4949_);
v___x_4966_ = l_Lean_Expr_app___override(v___x_4965_, v_00_u03b1_4949_);
v___x_4967_ = l_Lean_Meta_Sym_synthInstance(v___x_4966_, v_a_4934_, v_a_4935_, v_a_4936_, v_a_4937_, v_a_4938_, v_a_4939_);
if (lean_obj_tag(v___x_4967_) == 0)
{
lean_object* v_a_4968_; lean_object* v___x_4969_; lean_object* v___x_4970_; lean_object* v___x_4971_; lean_object* v___x_4972_; 
v_a_4968_ = lean_ctor_get(v___x_4967_, 0);
lean_inc(v_a_4968_);
lean_dec_ref(v___x_4967_);
v___x_4969_ = ((lean_object*)(l_Lean_Meta_Grind_Order_processNewEq___closed__3));
v___x_4970_ = l_Lean_mkConst(v___x_4969_, v___x_4964_);
lean_inc_ref(v_e_4956_);
lean_inc_ref(v_e_4947_);
v___x_4971_ = l_Lean_mkApp9(v___x_4970_, v_00_u03b1_4949_, v_a_4968_, v_a_4928_, v_b_4929_, v_e_4947_, v_e_4956_, v_h_4948_, v_h_4957_, v_a_4943_);
v___x_4972_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go(v_e_4947_, v_e_4956_, v___x_4971_, v_a_4930_, v_a_4931_, v_a_4932_, v_a_4933_, v_a_4934_, v_a_4935_, v_a_4936_, v_a_4937_, v_a_4938_, v_a_4939_);
return v___x_4972_;
}
else
{
lean_object* v_a_4973_; lean_object* v___x_4975_; uint8_t v_isShared_4976_; uint8_t v_isSharedCheck_4980_; 
lean_dec_ref(v___x_4964_);
lean_dec_ref(v_h_4957_);
lean_dec_ref(v_e_4956_);
lean_dec_ref(v_00_u03b1_4949_);
lean_dec_ref(v_h_4948_);
lean_dec_ref(v_e_4947_);
lean_dec(v_a_4943_);
lean_dec_ref(v_b_4929_);
lean_dec_ref(v_a_4928_);
v_a_4973_ = lean_ctor_get(v___x_4967_, 0);
v_isSharedCheck_4980_ = !lean_is_exclusive(v___x_4967_);
if (v_isSharedCheck_4980_ == 0)
{
v___x_4975_ = v___x_4967_;
v_isShared_4976_ = v_isSharedCheck_4980_;
goto v_resetjp_4974_;
}
else
{
lean_inc(v_a_4973_);
lean_dec(v___x_4967_);
v___x_4975_ = lean_box(0);
v_isShared_4976_ = v_isSharedCheck_4980_;
goto v_resetjp_4974_;
}
v_resetjp_4974_:
{
lean_object* v___x_4978_; 
if (v_isShared_4976_ == 0)
{
v___x_4978_ = v___x_4975_;
goto v_reusejp_4977_;
}
else
{
lean_object* v_reuseFailAlloc_4979_; 
v_reuseFailAlloc_4979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4979_, 0, v_a_4973_);
v___x_4978_ = v_reuseFailAlloc_4979_;
goto v_reusejp_4977_;
}
v_reusejp_4977_:
{
return v___x_4978_;
}
}
}
}
else
{
lean_object* v_a_4981_; lean_object* v___x_4983_; uint8_t v_isShared_4984_; uint8_t v_isSharedCheck_4988_; 
lean_dec_ref(v_h_4957_);
lean_dec_ref(v_e_4956_);
lean_dec_ref(v_00_u03b1_4949_);
lean_dec_ref(v_h_4948_);
lean_dec_ref(v_e_4947_);
lean_dec(v_a_4943_);
lean_dec_ref(v_b_4929_);
lean_dec_ref(v_a_4928_);
v_a_4981_ = lean_ctor_get(v___x_4960_, 0);
v_isSharedCheck_4988_ = !lean_is_exclusive(v___x_4960_);
if (v_isSharedCheck_4988_ == 0)
{
v___x_4983_ = v___x_4960_;
v_isShared_4984_ = v_isSharedCheck_4988_;
goto v_resetjp_4982_;
}
else
{
lean_inc(v_a_4981_);
lean_dec(v___x_4960_);
v___x_4983_ = lean_box(0);
v_isShared_4984_ = v_isSharedCheck_4988_;
goto v_resetjp_4982_;
}
v_resetjp_4982_:
{
lean_object* v___x_4986_; 
if (v_isShared_4984_ == 0)
{
v___x_4986_ = v___x_4983_;
goto v_reusejp_4985_;
}
else
{
lean_object* v_reuseFailAlloc_4987_; 
v_reuseFailAlloc_4987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4987_, 0, v_a_4981_);
v___x_4986_ = v_reuseFailAlloc_4987_;
goto v_reusejp_4985_;
}
v_reusejp_4985_:
{
return v___x_4986_;
}
}
}
}
else
{
lean_object* v___x_4989_; lean_object* v___x_4990_; lean_object* v___x_4991_; 
lean_dec_ref(v_00_u03b1_4949_);
v___x_4989_ = lean_obj_once(&l_Lean_Meta_Grind_Order_processNewEq___closed__6, &l_Lean_Meta_Grind_Order_processNewEq___closed__6_once, _init_l_Lean_Meta_Grind_Order_processNewEq___closed__6);
lean_inc_ref(v_e_4956_);
lean_inc_ref(v_e_4947_);
v___x_4990_ = l_Lean_mkApp7(v___x_4989_, v_a_4928_, v_b_4929_, v_e_4947_, v_e_4956_, v_h_4948_, v_h_4957_, v_a_4943_);
v___x_4991_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go(v_e_4947_, v_e_4956_, v___x_4990_, v_a_4930_, v_a_4931_, v_a_4932_, v_a_4933_, v_a_4934_, v_a_4935_, v_a_4936_, v_a_4937_, v_a_4938_, v_a_4939_);
return v___x_4991_;
}
}
else
{
lean_object* v___x_4992_; lean_object* v___x_4994_; 
lean_dec(v_a_4951_);
lean_dec_ref(v_00_u03b1_4949_);
lean_dec_ref(v_h_4948_);
lean_dec_ref(v_e_4947_);
lean_dec(v_a_4943_);
lean_dec_ref(v_b_4929_);
lean_dec_ref(v_a_4928_);
v___x_4992_ = lean_box(0);
if (v_isShared_4954_ == 0)
{
lean_ctor_set(v___x_4953_, 0, v___x_4992_);
v___x_4994_ = v___x_4953_;
goto v_reusejp_4993_;
}
else
{
lean_object* v_reuseFailAlloc_4995_; 
v_reuseFailAlloc_4995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4995_, 0, v___x_4992_);
v___x_4994_ = v_reuseFailAlloc_4995_;
goto v_reusejp_4993_;
}
v_reusejp_4993_:
{
return v___x_4994_;
}
}
}
}
else
{
lean_object* v_a_4997_; lean_object* v___x_4999_; uint8_t v_isShared_5000_; uint8_t v_isSharedCheck_5004_; 
lean_dec_ref(v_00_u03b1_4949_);
lean_dec_ref(v_h_4948_);
lean_dec_ref(v_e_4947_);
lean_dec(v_a_4943_);
lean_dec_ref(v_b_4929_);
lean_dec_ref(v_a_4928_);
v_a_4997_ = lean_ctor_get(v___x_4950_, 0);
v_isSharedCheck_5004_ = !lean_is_exclusive(v___x_4950_);
if (v_isSharedCheck_5004_ == 0)
{
v___x_4999_ = v___x_4950_;
v_isShared_5000_ = v_isSharedCheck_5004_;
goto v_resetjp_4998_;
}
else
{
lean_inc(v_a_4997_);
lean_dec(v___x_4950_);
v___x_4999_ = lean_box(0);
v_isShared_5000_ = v_isSharedCheck_5004_;
goto v_resetjp_4998_;
}
v_resetjp_4998_:
{
lean_object* v___x_5002_; 
if (v_isShared_5000_ == 0)
{
v___x_5002_ = v___x_4999_;
goto v_reusejp_5001_;
}
else
{
lean_object* v_reuseFailAlloc_5003_; 
v_reuseFailAlloc_5003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5003_, 0, v_a_4997_);
v___x_5002_ = v_reuseFailAlloc_5003_;
goto v_reusejp_5001_;
}
v_reusejp_5001_:
{
return v___x_5002_;
}
}
}
}
else
{
lean_object* v___x_5005_; 
lean_dec(v_a_4945_);
v___x_5005_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go(v_a_4928_, v_b_4929_, v_a_4943_, v_a_4930_, v_a_4931_, v_a_4932_, v_a_4933_, v_a_4934_, v_a_4935_, v_a_4936_, v_a_4937_, v_a_4938_, v_a_4939_);
return v___x_5005_;
}
}
else
{
lean_object* v_a_5006_; lean_object* v___x_5008_; uint8_t v_isShared_5009_; uint8_t v_isSharedCheck_5013_; 
lean_dec(v_a_4943_);
lean_dec_ref(v_b_4929_);
lean_dec_ref(v_a_4928_);
v_a_5006_ = lean_ctor_get(v___x_4944_, 0);
v_isSharedCheck_5013_ = !lean_is_exclusive(v___x_4944_);
if (v_isSharedCheck_5013_ == 0)
{
v___x_5008_ = v___x_4944_;
v_isShared_5009_ = v_isSharedCheck_5013_;
goto v_resetjp_5007_;
}
else
{
lean_inc(v_a_5006_);
lean_dec(v___x_4944_);
v___x_5008_ = lean_box(0);
v_isShared_5009_ = v_isSharedCheck_5013_;
goto v_resetjp_5007_;
}
v_resetjp_5007_:
{
lean_object* v___x_5011_; 
if (v_isShared_5009_ == 0)
{
v___x_5011_ = v___x_5008_;
goto v_reusejp_5010_;
}
else
{
lean_object* v_reuseFailAlloc_5012_; 
v_reuseFailAlloc_5012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5012_, 0, v_a_5006_);
v___x_5011_ = v_reuseFailAlloc_5012_;
goto v_reusejp_5010_;
}
v_reusejp_5010_:
{
return v___x_5011_;
}
}
}
}
else
{
lean_object* v_a_5014_; lean_object* v___x_5016_; uint8_t v_isShared_5017_; uint8_t v_isSharedCheck_5021_; 
lean_dec_ref(v_b_4929_);
lean_dec_ref(v_a_4928_);
v_a_5014_ = lean_ctor_get(v___x_4942_, 0);
v_isSharedCheck_5021_ = !lean_is_exclusive(v___x_4942_);
if (v_isSharedCheck_5021_ == 0)
{
v___x_5016_ = v___x_4942_;
v_isShared_5017_ = v_isSharedCheck_5021_;
goto v_resetjp_5015_;
}
else
{
lean_inc(v_a_5014_);
lean_dec(v___x_4942_);
v___x_5016_ = lean_box(0);
v_isShared_5017_ = v_isSharedCheck_5021_;
goto v_resetjp_5015_;
}
v_resetjp_5015_:
{
lean_object* v___x_5019_; 
if (v_isShared_5017_ == 0)
{
v___x_5019_ = v___x_5016_;
goto v_reusejp_5018_;
}
else
{
lean_object* v_reuseFailAlloc_5020_; 
v_reuseFailAlloc_5020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5020_, 0, v_a_5014_);
v___x_5019_ = v_reuseFailAlloc_5020_;
goto v_reusejp_5018_;
}
v_reusejp_5018_:
{
return v___x_5019_;
}
}
}
}
else
{
lean_object* v___x_5022_; lean_object* v___x_5023_; 
lean_dec_ref(v_b_4929_);
lean_dec_ref(v_a_4928_);
v___x_5022_ = lean_box(0);
v___x_5023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5023_, 0, v___x_5022_);
return v___x_5023_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_processNewEq___boxed(lean_object* v_a_5024_, lean_object* v_b_5025_, lean_object* v_a_5026_, lean_object* v_a_5027_, lean_object* v_a_5028_, lean_object* v_a_5029_, lean_object* v_a_5030_, lean_object* v_a_5031_, lean_object* v_a_5032_, lean_object* v_a_5033_, lean_object* v_a_5034_, lean_object* v_a_5035_, lean_object* v_a_5036_){
_start:
{
lean_object* v_res_5037_; 
v_res_5037_ = l_Lean_Meta_Grind_Order_processNewEq(v_a_5024_, v_b_5025_, v_a_5026_, v_a_5027_, v_a_5028_, v_a_5029_, v_a_5030_, v_a_5031_, v_a_5032_, v_a_5033_, v_a_5034_, v_a_5035_);
lean_dec(v_a_5035_);
lean_dec_ref(v_a_5034_);
lean_dec(v_a_5033_);
lean_dec_ref(v_a_5032_);
lean_dec(v_a_5031_);
lean_dec_ref(v_a_5030_);
lean_dec(v_a_5029_);
lean_dec_ref(v_a_5028_);
lean_dec(v_a_5027_);
lean_dec(v_a_5026_);
return v_res_5037_;
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
