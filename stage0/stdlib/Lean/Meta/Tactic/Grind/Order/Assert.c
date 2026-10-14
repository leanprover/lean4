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
lean_object* l_Lean_Meta_Grind_Order_getProof___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_mkTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_getExpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_getCnstr_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqTrue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqFalse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqFalseProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_getDist_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_Order_Weight_compare(lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_modifyStruct___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_getStruct___redArg(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_Order_Weight_add(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_Order_Weight_isNeg(lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_Cnstr_pp___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_instMonadEIO___redArg();
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
lean_object* l_Lean_Meta_Grind_instInhabitedGoalM___redArg();
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instDecidableEqNat___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instBEqProd___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_getNodeId___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isShorter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isShorter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_19_ = l_Lean_Meta_Grind_Order_getProof___redArg(v_u_1_, v_w_16_, v_a_4_, v_a_5_, v_a_11_, v_a_12_, v_a_13_, v_a_14_);
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
v___x_71_ = l_Lean_Meta_Grind_Order_getProof___redArg(v_u_57_, v_v_58_, v_a_59_, v_a_60_, v_a_66_, v_a_67_, v_a_68_, v_a_69_);
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
v___x_116_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_u_97_, v_a_102_, v_a_103_, v_a_111_);
if (lean_obj_tag(v___x_116_) == 0)
{
lean_object* v_a_117_; lean_object* v___x_118_; 
v_a_117_ = lean_ctor_get(v___x_116_, 0);
lean_inc(v_a_117_);
lean_dec_ref_known(v___x_116_, 1);
v___x_118_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_v_98_, v_a_102_, v_a_103_, v_a_111_);
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
size_t v_x_281__boxed_259_; size_t v_x_282__boxed_260_; lean_object* v_res_261_; 
v_x_281__boxed_259_ = lean_unbox_usize(v_x_257_);
lean_dec(v_x_257_);
v_x_282__boxed_260_ = lean_unbox_usize(v_x_258_);
lean_dec(v_x_258_);
v_res_261_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1_spec__3(v_u_254_, v_k_255_, v_x_256_, v_x_281__boxed_259_, v_x_282__boxed_260_);
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
lean_object* v_id_304_; lean_object* v_nodes_305_; lean_object* v_nodeMap_306_; lean_object* v_cnstrs_307_; lean_object* v_cnstrsOf_308_; lean_object* v_sources_309_; lean_object* v_targets_310_; lean_object* v_proofs_311_; lean_object* v_propagate_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_321_; 
v_id_304_ = lean_ctor_get(v_s_303_, 0);
v_nodes_305_ = lean_ctor_get(v_s_303_, 1);
v_nodeMap_306_ = lean_ctor_get(v_s_303_, 2);
v_cnstrs_307_ = lean_ctor_get(v_s_303_, 3);
v_cnstrsOf_308_ = lean_ctor_get(v_s_303_, 4);
v_sources_309_ = lean_ctor_get(v_s_303_, 5);
v_targets_310_ = lean_ctor_get(v_s_303_, 6);
v_proofs_311_ = lean_ctor_get(v_s_303_, 7);
v_propagate_312_ = lean_ctor_get(v_s_303_, 8);
v_isSharedCheck_321_ = !lean_is_exclusive(v_s_303_);
if (v_isSharedCheck_321_ == 0)
{
v___x_314_ = v_s_303_;
v_isShared_315_ = v_isSharedCheck_321_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_propagate_312_);
lean_inc(v_proofs_311_);
lean_inc(v_targets_310_);
lean_inc(v_sources_309_);
lean_inc(v_cnstrsOf_308_);
lean_inc(v_cnstrs_307_);
lean_inc(v_nodeMap_306_);
lean_inc(v_nodes_305_);
lean_inc(v_id_304_);
lean_dec(v_s_303_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_321_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_319_; 
lean_inc_ref(v_k_301_);
lean_inc(v_u_300_);
v___x_316_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1(v_u_300_, v_k_301_, v_sources_309_, v_v_302_);
v___x_317_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1(v_v_302_, v_k_301_, v_targets_310_, v_u_300_);
lean_dec(v_u_300_);
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 6, v___x_317_);
lean_ctor_set(v___x_314_, 5, v___x_316_);
v___x_319_ = v___x_314_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v_id_304_);
lean_ctor_set(v_reuseFailAlloc_320_, 1, v_nodes_305_);
lean_ctor_set(v_reuseFailAlloc_320_, 2, v_nodeMap_306_);
lean_ctor_set(v_reuseFailAlloc_320_, 3, v_cnstrs_307_);
lean_ctor_set(v_reuseFailAlloc_320_, 4, v_cnstrsOf_308_);
lean_ctor_set(v_reuseFailAlloc_320_, 5, v___x_316_);
lean_ctor_set(v_reuseFailAlloc_320_, 6, v___x_317_);
lean_ctor_set(v_reuseFailAlloc_320_, 7, v_proofs_311_);
lean_ctor_set(v_reuseFailAlloc_320_, 8, v_propagate_312_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist___redArg(lean_object* v_u_322_, lean_object* v_v_323_, lean_object* v_k_324_, lean_object* v_a_325_, lean_object* v_a_326_){
_start:
{
lean_object* v___f_328_; lean_object* v___x_329_; 
v___f_328_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist___redArg___lam__0), 4, 3);
lean_closure_set(v___f_328_, 0, v_u_322_);
lean_closure_set(v___f_328_, 1, v_k_324_);
lean_closure_set(v___f_328_, 2, v_v_323_);
v___x_329_ = l_Lean_Meta_Grind_Order_modifyStruct___redArg(v___f_328_, v_a_325_, v_a_326_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist___redArg___boxed(lean_object* v_u_330_, lean_object* v_v_331_, lean_object* v_k_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist___redArg(v_u_330_, v_v_331_, v_k_332_, v_a_333_, v_a_334_);
lean_dec(v_a_334_);
lean_dec(v_a_333_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist(lean_object* v_u_337_, lean_object* v_v_338_, lean_object* v_k_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist___redArg(v_u_337_, v_v_338_, v_k_339_, v_a_340_, v_a_341_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist___boxed(lean_object* v_u_353_, lean_object* v_v_354_, lean_object* v_k_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist(v_u_353_, v_v_354_, v_k_355_, v_a_356_, v_a_357_, v_a_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_);
lean_dec(v_a_366_);
lean_dec_ref(v_a_365_);
lean_dec(v_a_364_);
lean_dec_ref(v_a_363_);
lean_dec(v_a_362_);
lean_dec_ref(v_a_361_);
lean_dec(v_a_360_);
lean_dec_ref(v_a_359_);
lean_dec(v_a_358_);
lean_dec(v_a_357_);
lean_dec(v_a_356_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0(lean_object* v_00_u03b2_369_, lean_object* v_m_370_, lean_object* v_k_371_, lean_object* v_v_372_){
_start:
{
lean_object* v___x_373_; 
v___x_373_ = l_Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0___redArg(v_m_370_, v_k_371_, v_v_372_);
return v___x_373_;
}
}
LEAN_EXPORT uint8_t l_Lean_AssocList_contains___at___00Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0_spec__0(lean_object* v_00_u03b2_374_, lean_object* v_a_375_, lean_object* v_x_376_){
_start:
{
uint8_t v___x_377_; 
v___x_377_ = l_Lean_AssocList_contains___at___00Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0_spec__0___redArg(v_a_375_, v_x_376_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_contains___at___00Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0_spec__0___boxed(lean_object* v_00_u03b2_378_, lean_object* v_a_379_, lean_object* v_x_380_){
_start:
{
uint8_t v_res_381_; lean_object* v_r_382_; 
v_res_381_ = l_Lean_AssocList_contains___at___00Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0_spec__0(v_00_u03b2_378_, v_a_379_, v_x_380_);
lean_dec(v_x_380_);
lean_dec(v_a_379_);
v_r_382_ = lean_box(v_res_381_);
return v_r_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_replace___at___00Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0_spec__1(lean_object* v_00_u03b2_383_, lean_object* v_a_384_, lean_object* v_b_385_, lean_object* v_x_386_){
_start:
{
lean_object* v___x_387_; 
v___x_387_ = l_Lean_AssocList_replace___at___00Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0_spec__1___redArg(v_a_384_, v_b_385_, v_x_386_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof_spec__0_spec__0(lean_object* v_v_388_, lean_object* v_p_389_, lean_object* v_x_390_, size_t v_x_391_, size_t v_x_392_){
_start:
{
if (lean_obj_tag(v_x_390_) == 0)
{
lean_object* v_cs_393_; size_t v_j_394_; lean_object* v___x_395_; lean_object* v___x_396_; uint8_t v___x_397_; 
v_cs_393_ = lean_ctor_get(v_x_390_, 0);
v_j_394_ = lean_usize_shift_right(v_x_391_, v_x_392_);
v___x_395_ = lean_usize_to_nat(v_j_394_);
v___x_396_ = lean_array_get_size(v_cs_393_);
v___x_397_ = lean_nat_dec_lt(v___x_395_, v___x_396_);
if (v___x_397_ == 0)
{
lean_dec(v___x_395_);
lean_dec_ref(v_p_389_);
lean_dec(v_v_388_);
return v_x_390_;
}
else
{
lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_415_; 
lean_inc_ref(v_cs_393_);
v_isSharedCheck_415_ = !lean_is_exclusive(v_x_390_);
if (v_isSharedCheck_415_ == 0)
{
lean_object* v_unused_416_; 
v_unused_416_ = lean_ctor_get(v_x_390_, 0);
lean_dec(v_unused_416_);
v___x_399_ = v_x_390_;
v_isShared_400_ = v_isSharedCheck_415_;
goto v_resetjp_398_;
}
else
{
lean_dec(v_x_390_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_415_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
size_t v___x_401_; size_t v___x_402_; size_t v___x_403_; size_t v_i_404_; size_t v___x_405_; size_t v_shift_406_; lean_object* v_v_407_; lean_object* v___x_408_; lean_object* v_xs_x27_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_413_; 
v___x_401_ = ((size_t)1ULL);
v___x_402_ = lean_usize_shift_left(v___x_401_, v_x_392_);
v___x_403_ = lean_usize_sub(v___x_402_, v___x_401_);
v_i_404_ = lean_usize_land(v_x_391_, v___x_403_);
v___x_405_ = ((size_t)5ULL);
v_shift_406_ = lean_usize_sub(v_x_392_, v___x_405_);
v_v_407_ = lean_array_fget(v_cs_393_, v___x_395_);
v___x_408_ = lean_box(0);
v_xs_x27_409_ = lean_array_fset(v_cs_393_, v___x_395_, v___x_408_);
v___x_410_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof_spec__0_spec__0(v_v_388_, v_p_389_, v_v_407_, v_i_404_, v_shift_406_);
v___x_411_ = lean_array_fset(v_xs_x27_409_, v___x_395_, v___x_410_);
lean_dec(v___x_395_);
if (v_isShared_400_ == 0)
{
lean_ctor_set(v___x_399_, 0, v___x_411_);
v___x_413_ = v___x_399_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v___x_411_);
v___x_413_ = v_reuseFailAlloc_414_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
return v___x_413_;
}
}
}
}
else
{
lean_object* v_vs_417_; lean_object* v___x_418_; lean_object* v___x_419_; uint8_t v___x_420_; 
v_vs_417_ = lean_ctor_get(v_x_390_, 0);
v___x_418_ = lean_usize_to_nat(v_x_391_);
v___x_419_ = lean_array_get_size(v_vs_417_);
v___x_420_ = lean_nat_dec_lt(v___x_418_, v___x_419_);
if (v___x_420_ == 0)
{
lean_dec(v___x_418_);
lean_dec_ref(v_p_389_);
lean_dec(v_v_388_);
return v_x_390_;
}
else
{
lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_432_; 
lean_inc_ref(v_vs_417_);
v_isSharedCheck_432_ = !lean_is_exclusive(v_x_390_);
if (v_isSharedCheck_432_ == 0)
{
lean_object* v_unused_433_; 
v_unused_433_ = lean_ctor_get(v_x_390_, 0);
lean_dec(v_unused_433_);
v___x_422_ = v_x_390_;
v_isShared_423_ = v_isSharedCheck_432_;
goto v_resetjp_421_;
}
else
{
lean_dec(v_x_390_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_432_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v_v_424_; lean_object* v___x_425_; lean_object* v_xs_x27_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_430_; 
v_v_424_ = lean_array_fget(v_vs_417_, v___x_418_);
v___x_425_ = lean_box(0);
v_xs_x27_426_ = lean_array_fset(v_vs_417_, v___x_418_, v___x_425_);
v___x_427_ = l_Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0___redArg(v_v_424_, v_v_388_, v_p_389_);
v___x_428_ = lean_array_fset(v_xs_x27_426_, v___x_418_, v___x_427_);
lean_dec(v___x_418_);
if (v_isShared_423_ == 0)
{
lean_ctor_set(v___x_422_, 0, v___x_428_);
v___x_430_ = v___x_422_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v___x_428_);
v___x_430_ = v_reuseFailAlloc_431_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
return v___x_430_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof_spec__0_spec__0___boxed(lean_object* v_v_434_, lean_object* v_p_435_, lean_object* v_x_436_, lean_object* v_x_437_, lean_object* v_x_438_){
_start:
{
size_t v_x_141__boxed_439_; size_t v_x_142__boxed_440_; lean_object* v_res_441_; 
v_x_141__boxed_439_ = lean_unbox_usize(v_x_437_);
lean_dec(v_x_437_);
v_x_142__boxed_440_ = lean_unbox_usize(v_x_438_);
lean_dec(v_x_438_);
v_res_441_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof_spec__0_spec__0(v_v_434_, v_p_435_, v_x_436_, v_x_141__boxed_439_, v_x_142__boxed_440_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof_spec__0(lean_object* v_v_442_, lean_object* v_p_443_, lean_object* v_t_444_, lean_object* v_i_445_){
_start:
{
lean_object* v_root_446_; lean_object* v_tail_447_; lean_object* v_size_448_; size_t v_shift_449_; lean_object* v_tailOff_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_474_; 
v_root_446_ = lean_ctor_get(v_t_444_, 0);
v_tail_447_ = lean_ctor_get(v_t_444_, 1);
v_size_448_ = lean_ctor_get(v_t_444_, 2);
v_shift_449_ = lean_ctor_get_usize(v_t_444_, 4);
v_tailOff_450_ = lean_ctor_get(v_t_444_, 3);
v_isSharedCheck_474_ = !lean_is_exclusive(v_t_444_);
if (v_isSharedCheck_474_ == 0)
{
v___x_452_ = v_t_444_;
v_isShared_453_ = v_isSharedCheck_474_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_tailOff_450_);
lean_inc(v_size_448_);
lean_inc(v_tail_447_);
lean_inc(v_root_446_);
lean_dec(v_t_444_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_474_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
uint8_t v___x_454_; 
v___x_454_ = lean_nat_dec_le(v_tailOff_450_, v_i_445_);
if (v___x_454_ == 0)
{
size_t v___x_455_; lean_object* v___x_456_; lean_object* v___x_458_; 
v___x_455_ = lean_usize_of_nat(v_i_445_);
v___x_456_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof_spec__0_spec__0(v_v_442_, v_p_443_, v_root_446_, v___x_455_, v_shift_449_);
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 0, v___x_456_);
v___x_458_ = v___x_452_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v___x_456_);
lean_ctor_set(v_reuseFailAlloc_459_, 1, v_tail_447_);
lean_ctor_set(v_reuseFailAlloc_459_, 2, v_size_448_);
lean_ctor_set(v_reuseFailAlloc_459_, 3, v_tailOff_450_);
lean_ctor_set_usize(v_reuseFailAlloc_459_, 4, v_shift_449_);
v___x_458_ = v_reuseFailAlloc_459_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
return v___x_458_;
}
}
else
{
lean_object* v___x_460_; lean_object* v___x_461_; uint8_t v___x_462_; 
v___x_460_ = lean_nat_sub(v_i_445_, v_tailOff_450_);
v___x_461_ = lean_array_get_size(v_tail_447_);
v___x_462_ = lean_nat_dec_lt(v___x_460_, v___x_461_);
if (v___x_462_ == 0)
{
lean_object* v___x_464_; 
lean_dec(v___x_460_);
lean_dec_ref(v_p_443_);
lean_dec(v_v_442_);
if (v_isShared_453_ == 0)
{
v___x_464_ = v___x_452_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v_root_446_);
lean_ctor_set(v_reuseFailAlloc_465_, 1, v_tail_447_);
lean_ctor_set(v_reuseFailAlloc_465_, 2, v_size_448_);
lean_ctor_set(v_reuseFailAlloc_465_, 3, v_tailOff_450_);
lean_ctor_set_usize(v_reuseFailAlloc_465_, 4, v_shift_449_);
v___x_464_ = v_reuseFailAlloc_465_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
return v___x_464_;
}
}
else
{
lean_object* v_v_466_; lean_object* v___x_467_; lean_object* v_xs_x27_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_472_; 
v_v_466_ = lean_array_fget(v_tail_447_, v___x_460_);
v___x_467_ = lean_box(0);
v_xs_x27_468_ = lean_array_fset(v_tail_447_, v___x_460_, v___x_467_);
v___x_469_ = l_Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0___redArg(v_v_466_, v_v_442_, v_p_443_);
v___x_470_ = lean_array_fset(v_xs_x27_468_, v___x_460_, v___x_469_);
lean_dec(v___x_460_);
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 1, v___x_470_);
v___x_472_ = v___x_452_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v_root_446_);
lean_ctor_set(v_reuseFailAlloc_473_, 1, v___x_470_);
lean_ctor_set(v_reuseFailAlloc_473_, 2, v_size_448_);
lean_ctor_set(v_reuseFailAlloc_473_, 3, v_tailOff_450_);
lean_ctor_set_usize(v_reuseFailAlloc_473_, 4, v_shift_449_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
return v___x_472_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof_spec__0___boxed(lean_object* v_v_475_, lean_object* v_p_476_, lean_object* v_t_477_, lean_object* v_i_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof_spec__0(v_v_475_, v_p_476_, v_t_477_, v_i_478_);
lean_dec(v_i_478_);
return v_res_479_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___redArg___lam__0(lean_object* v_v_480_, lean_object* v_p_481_, lean_object* v_u_482_, lean_object* v_s_483_){
_start:
{
lean_object* v_id_484_; lean_object* v_nodes_485_; lean_object* v_nodeMap_486_; lean_object* v_cnstrs_487_; lean_object* v_cnstrsOf_488_; lean_object* v_sources_489_; lean_object* v_targets_490_; lean_object* v_proofs_491_; lean_object* v_propagate_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_500_; 
v_id_484_ = lean_ctor_get(v_s_483_, 0);
v_nodes_485_ = lean_ctor_get(v_s_483_, 1);
v_nodeMap_486_ = lean_ctor_get(v_s_483_, 2);
v_cnstrs_487_ = lean_ctor_get(v_s_483_, 3);
v_cnstrsOf_488_ = lean_ctor_get(v_s_483_, 4);
v_sources_489_ = lean_ctor_get(v_s_483_, 5);
v_targets_490_ = lean_ctor_get(v_s_483_, 6);
v_proofs_491_ = lean_ctor_get(v_s_483_, 7);
v_propagate_492_ = lean_ctor_get(v_s_483_, 8);
v_isSharedCheck_500_ = !lean_is_exclusive(v_s_483_);
if (v_isSharedCheck_500_ == 0)
{
v___x_494_ = v_s_483_;
v_isShared_495_ = v_isSharedCheck_500_;
goto v_resetjp_493_;
}
else
{
lean_inc(v_propagate_492_);
lean_inc(v_proofs_491_);
lean_inc(v_targets_490_);
lean_inc(v_sources_489_);
lean_inc(v_cnstrsOf_488_);
lean_inc(v_cnstrs_487_);
lean_inc(v_nodeMap_486_);
lean_inc(v_nodes_485_);
lean_inc(v_id_484_);
lean_dec(v_s_483_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_500_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
lean_object* v___x_496_; lean_object* v___x_498_; 
v___x_496_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof_spec__0(v_v_480_, v_p_481_, v_proofs_491_, v_u_482_);
if (v_isShared_495_ == 0)
{
lean_ctor_set(v___x_494_, 7, v___x_496_);
v___x_498_ = v___x_494_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v_id_484_);
lean_ctor_set(v_reuseFailAlloc_499_, 1, v_nodes_485_);
lean_ctor_set(v_reuseFailAlloc_499_, 2, v_nodeMap_486_);
lean_ctor_set(v_reuseFailAlloc_499_, 3, v_cnstrs_487_);
lean_ctor_set(v_reuseFailAlloc_499_, 4, v_cnstrsOf_488_);
lean_ctor_set(v_reuseFailAlloc_499_, 5, v_sources_489_);
lean_ctor_set(v_reuseFailAlloc_499_, 6, v_targets_490_);
lean_ctor_set(v_reuseFailAlloc_499_, 7, v___x_496_);
lean_ctor_set(v_reuseFailAlloc_499_, 8, v_propagate_492_);
v___x_498_ = v_reuseFailAlloc_499_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
return v___x_498_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___redArg___lam__0___boxed(lean_object* v_v_501_, lean_object* v_p_502_, lean_object* v_u_503_, lean_object* v_s_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___redArg___lam__0(v_v_501_, v_p_502_, v_u_503_, v_s_504_);
lean_dec(v_u_503_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___redArg(lean_object* v_u_506_, lean_object* v_v_507_, lean_object* v_p_508_, lean_object* v_a_509_, lean_object* v_a_510_){
_start:
{
lean_object* v___f_512_; lean_object* v___x_513_; 
v___f_512_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_512_, 0, v_v_507_);
lean_closure_set(v___f_512_, 1, v_p_508_);
lean_closure_set(v___f_512_, 2, v_u_506_);
v___x_513_ = l_Lean_Meta_Grind_Order_modifyStruct___redArg(v___f_512_, v_a_509_, v_a_510_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___redArg___boxed(lean_object* v_u_514_, lean_object* v_v_515_, lean_object* v_p_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___redArg(v_u_514_, v_v_515_, v_p_516_, v_a_517_, v_a_518_);
lean_dec(v_a_518_);
lean_dec(v_a_517_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof(lean_object* v_u_521_, lean_object* v_v_522_, lean_object* v_p_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_){
_start:
{
lean_object* v___x_536_; 
v___x_536_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___redArg(v_u_521_, v_v_522_, v_p_523_, v_a_524_, v_a_525_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___boxed(lean_object* v_u_537_, lean_object* v_v_538_, lean_object* v_p_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof(v_u_537_, v_v_538_, v_p_539_, v_a_540_, v_a_541_, v_a_542_, v_a_543_, v_a_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_, v_a_550_);
lean_dec(v_a_550_);
lean_dec_ref(v_a_549_);
lean_dec(v_a_548_);
lean_dec_ref(v_a_547_);
lean_dec(v_a_546_);
lean_dec_ref(v_a_545_);
lean_dec(v_a_544_);
lean_dec_ref(v_a_543_);
lean_dec(v_a_542_);
lean_dec(v_a_541_);
lean_dec(v_a_540_);
return v_res_552_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__0(void){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = l_instMonadEIO___redArg();
return v___x_553_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__1(void){
_start:
{
lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_554_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__0, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__0);
v___x_555_ = l_StateRefT_x27_instMonad___redArg(v___x_554_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf(lean_object* v_u_560_, lean_object* v_f_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_){
_start:
{
lean_object* v___x_574_; lean_object* v_toApplicative_575_; lean_object* v_toFunctor_576_; lean_object* v_toSeq_577_; lean_object* v_toSeqLeft_578_; lean_object* v_toSeqRight_579_; lean_object* v___f_580_; lean_object* v___f_581_; lean_object* v___f_582_; lean_object* v___f_583_; lean_object* v___x_584_; lean_object* v___f_585_; lean_object* v___f_586_; lean_object* v___f_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v_toApplicative_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_645_; 
v___x_574_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__1, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__1);
v_toApplicative_575_ = lean_ctor_get(v___x_574_, 0);
v_toFunctor_576_ = lean_ctor_get(v_toApplicative_575_, 0);
v_toSeq_577_ = lean_ctor_get(v_toApplicative_575_, 2);
v_toSeqLeft_578_ = lean_ctor_get(v_toApplicative_575_, 3);
v_toSeqRight_579_ = lean_ctor_get(v_toApplicative_575_, 4);
v___f_580_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__2));
v___f_581_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__3));
lean_inc_ref_n(v_toFunctor_576_, 2);
v___f_582_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_582_, 0, v_toFunctor_576_);
v___f_583_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_583_, 0, v_toFunctor_576_);
v___x_584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_584_, 0, v___f_582_);
lean_ctor_set(v___x_584_, 1, v___f_583_);
lean_inc(v_toSeqRight_579_);
v___f_585_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_585_, 0, v_toSeqRight_579_);
lean_inc(v_toSeqLeft_578_);
v___f_586_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_586_, 0, v_toSeqLeft_578_);
lean_inc(v_toSeq_577_);
v___f_587_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_587_, 0, v_toSeq_577_);
v___x_588_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_588_, 0, v___x_584_);
lean_ctor_set(v___x_588_, 1, v___f_580_);
lean_ctor_set(v___x_588_, 2, v___f_587_);
lean_ctor_set(v___x_588_, 3, v___f_586_);
lean_ctor_set(v___x_588_, 4, v___f_585_);
v___x_589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_589_, 0, v___x_588_);
lean_ctor_set(v___x_589_, 1, v___f_581_);
v___x_590_ = l_StateRefT_x27_instMonad___redArg(v___x_589_);
v_toApplicative_591_ = lean_ctor_get(v___x_590_, 0);
v_isSharedCheck_645_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_645_ == 0)
{
lean_object* v_unused_646_; 
v_unused_646_ = lean_ctor_get(v___x_590_, 1);
lean_dec(v_unused_646_);
v___x_593_ = v___x_590_;
v_isShared_594_ = v_isSharedCheck_645_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_toApplicative_591_);
lean_dec(v___x_590_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_645_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v_toFunctor_595_; lean_object* v_toSeq_596_; lean_object* v_toSeqLeft_597_; lean_object* v_toSeqRight_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_643_; 
v_toFunctor_595_ = lean_ctor_get(v_toApplicative_591_, 0);
v_toSeq_596_ = lean_ctor_get(v_toApplicative_591_, 2);
v_toSeqLeft_597_ = lean_ctor_get(v_toApplicative_591_, 3);
v_toSeqRight_598_ = lean_ctor_get(v_toApplicative_591_, 4);
v_isSharedCheck_643_ = !lean_is_exclusive(v_toApplicative_591_);
if (v_isSharedCheck_643_ == 0)
{
lean_object* v_unused_644_; 
v_unused_644_ = lean_ctor_get(v_toApplicative_591_, 1);
lean_dec(v_unused_644_);
v___x_600_ = v_toApplicative_591_;
v_isShared_601_ = v_isSharedCheck_643_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_toSeqRight_598_);
lean_inc(v_toSeqLeft_597_);
lean_inc(v_toSeq_596_);
lean_inc(v_toFunctor_595_);
lean_dec(v_toApplicative_591_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_643_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___f_602_; lean_object* v___f_603_; lean_object* v___f_604_; lean_object* v___f_605_; lean_object* v___x_606_; lean_object* v___f_607_; lean_object* v___f_608_; lean_object* v___f_609_; lean_object* v___x_611_; 
v___f_602_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__4));
v___f_603_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__5));
lean_inc_ref(v_toFunctor_595_);
v___f_604_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_604_, 0, v_toFunctor_595_);
v___f_605_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_605_, 0, v_toFunctor_595_);
v___x_606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_606_, 0, v___f_604_);
lean_ctor_set(v___x_606_, 1, v___f_605_);
v___f_607_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_607_, 0, v_toSeqRight_598_);
v___f_608_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_608_, 0, v_toSeqLeft_597_);
v___f_609_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_609_, 0, v_toSeq_596_);
if (v_isShared_601_ == 0)
{
lean_ctor_set(v___x_600_, 4, v___f_607_);
lean_ctor_set(v___x_600_, 3, v___f_608_);
lean_ctor_set(v___x_600_, 2, v___f_609_);
lean_ctor_set(v___x_600_, 1, v___f_602_);
lean_ctor_set(v___x_600_, 0, v___x_606_);
v___x_611_ = v___x_600_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v___x_606_);
lean_ctor_set(v_reuseFailAlloc_642_, 1, v___f_602_);
lean_ctor_set(v_reuseFailAlloc_642_, 2, v___f_609_);
lean_ctor_set(v_reuseFailAlloc_642_, 3, v___f_608_);
lean_ctor_set(v_reuseFailAlloc_642_, 4, v___f_607_);
v___x_611_ = v_reuseFailAlloc_642_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
lean_object* v___x_613_; 
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 1, v___f_603_);
lean_ctor_set(v___x_593_, 0, v___x_611_);
v___x_613_ = v___x_593_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v___x_611_);
lean_ctor_set(v_reuseFailAlloc_641_, 1, v___f_603_);
v___x_613_ = v_reuseFailAlloc_641_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_614_ = l_StateRefT_x27_instMonad___redArg(v___x_613_);
v___x_615_ = l_ReaderT_instMonad___redArg(v___x_614_);
v___x_616_ = l_StateRefT_x27_instMonad___redArg(v___x_615_);
v___x_617_ = l_ReaderT_instMonad___redArg(v___x_616_);
v___x_618_ = l_ReaderT_instMonad___redArg(v___x_617_);
v___x_619_ = l_StateRefT_x27_instMonad___redArg(v___x_618_);
v___x_620_ = l_ReaderT_instMonad___redArg(v___x_619_);
v___x_621_ = lean_box(0);
v___x_622_ = l_Lean_Meta_Grind_Order_getStruct___redArg(v_a_562_, v_a_563_, v_a_571_);
if (lean_obj_tag(v___x_622_) == 0)
{
lean_object* v_a_623_; lean_object* v_sources_624_; lean_object* v_size_625_; uint8_t v___x_626_; 
v_a_623_ = lean_ctor_get(v___x_622_, 0);
lean_inc(v_a_623_);
lean_dec_ref_known(v___x_622_, 1);
v_sources_624_ = lean_ctor_get(v_a_623_, 5);
lean_inc_ref(v_sources_624_);
lean_dec(v_a_623_);
v_size_625_ = lean_ctor_get(v_sources_624_, 2);
v___x_626_ = lean_nat_dec_lt(v_u_560_, v_size_625_);
if (v___x_626_ == 0)
{
lean_object* v___x_627_; lean_object* v___x_839__overap_628_; lean_object* v___x_629_; 
lean_dec_ref(v_sources_624_);
v___x_627_ = l_outOfBounds___redArg(v___x_621_);
v___x_839__overap_628_ = l_Lean_AssocList_forM___redArg(v___x_620_, v_f_561_, v___x_627_);
lean_inc(v_a_572_);
lean_inc_ref(v_a_571_);
lean_inc(v_a_570_);
lean_inc_ref(v_a_569_);
lean_inc(v_a_568_);
lean_inc_ref(v_a_567_);
lean_inc(v_a_566_);
lean_inc_ref(v_a_565_);
lean_inc(v_a_564_);
lean_inc(v_a_563_);
lean_inc(v_a_562_);
v___x_629_ = lean_apply_12(v___x_839__overap_628_, v_a_562_, v_a_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_, v_a_570_, v_a_571_, v_a_572_, lean_box(0));
return v___x_629_;
}
else
{
lean_object* v___x_630_; lean_object* v___x_842__overap_631_; lean_object* v___x_632_; 
v___x_630_ = l_Lean_PersistentArray_get_x21___redArg(v___x_621_, v_sources_624_, v_u_560_);
lean_dec_ref(v_sources_624_);
v___x_842__overap_631_ = l_Lean_AssocList_forM___redArg(v___x_620_, v_f_561_, v___x_630_);
lean_inc(v_a_572_);
lean_inc_ref(v_a_571_);
lean_inc(v_a_570_);
lean_inc_ref(v_a_569_);
lean_inc(v_a_568_);
lean_inc_ref(v_a_567_);
lean_inc(v_a_566_);
lean_inc_ref(v_a_565_);
lean_inc(v_a_564_);
lean_inc(v_a_563_);
lean_inc(v_a_562_);
v___x_632_ = lean_apply_12(v___x_842__overap_631_, v_a_562_, v_a_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_, v_a_570_, v_a_571_, v_a_572_, lean_box(0));
return v___x_632_;
}
}
else
{
lean_object* v_a_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_640_; 
lean_dec_ref(v___x_620_);
lean_dec_ref(v_f_561_);
v_a_633_ = lean_ctor_get(v___x_622_, 0);
v_isSharedCheck_640_ = !lean_is_exclusive(v___x_622_);
if (v_isSharedCheck_640_ == 0)
{
v___x_635_ = v___x_622_;
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_a_633_);
lean_dec(v___x_622_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v___x_638_; 
if (v_isShared_636_ == 0)
{
v___x_638_ = v___x_635_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_a_633_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___boxed(lean_object* v_u_647_, lean_object* v_f_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf(v_u_647_, v_f_648_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_, v_a_656_, v_a_657_, v_a_658_, v_a_659_);
lean_dec(v_a_659_);
lean_dec_ref(v_a_658_);
lean_dec(v_a_657_);
lean_dec_ref(v_a_656_);
lean_dec(v_a_655_);
lean_dec_ref(v_a_654_);
lean_dec(v_a_653_);
lean_dec_ref(v_a_652_);
lean_dec(v_a_651_);
lean_dec(v_a_650_);
lean_dec(v_a_649_);
lean_dec(v_u_647_);
return v_res_661_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachTargetOf(lean_object* v_u_662_, lean_object* v_f_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_){
_start:
{
lean_object* v___x_676_; lean_object* v_toApplicative_677_; lean_object* v_toFunctor_678_; lean_object* v_toSeq_679_; lean_object* v_toSeqLeft_680_; lean_object* v_toSeqRight_681_; lean_object* v___f_682_; lean_object* v___f_683_; lean_object* v___f_684_; lean_object* v___f_685_; lean_object* v___x_686_; lean_object* v___f_687_; lean_object* v___f_688_; lean_object* v___f_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v_toApplicative_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_747_; 
v___x_676_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__1, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__1);
v_toApplicative_677_ = lean_ctor_get(v___x_676_, 0);
v_toFunctor_678_ = lean_ctor_get(v_toApplicative_677_, 0);
v_toSeq_679_ = lean_ctor_get(v_toApplicative_677_, 2);
v_toSeqLeft_680_ = lean_ctor_get(v_toApplicative_677_, 3);
v_toSeqRight_681_ = lean_ctor_get(v_toApplicative_677_, 4);
v___f_682_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__2));
v___f_683_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__3));
lean_inc_ref_n(v_toFunctor_678_, 2);
v___f_684_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_684_, 0, v_toFunctor_678_);
v___f_685_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_685_, 0, v_toFunctor_678_);
v___x_686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_686_, 0, v___f_684_);
lean_ctor_set(v___x_686_, 1, v___f_685_);
lean_inc(v_toSeqRight_681_);
v___f_687_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_687_, 0, v_toSeqRight_681_);
lean_inc(v_toSeqLeft_680_);
v___f_688_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_688_, 0, v_toSeqLeft_680_);
lean_inc(v_toSeq_679_);
v___f_689_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_689_, 0, v_toSeq_679_);
v___x_690_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_690_, 0, v___x_686_);
lean_ctor_set(v___x_690_, 1, v___f_682_);
lean_ctor_set(v___x_690_, 2, v___f_689_);
lean_ctor_set(v___x_690_, 3, v___f_688_);
lean_ctor_set(v___x_690_, 4, v___f_687_);
v___x_691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_691_, 0, v___x_690_);
lean_ctor_set(v___x_691_, 1, v___f_683_);
v___x_692_ = l_StateRefT_x27_instMonad___redArg(v___x_691_);
v_toApplicative_693_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_747_ == 0)
{
lean_object* v_unused_748_; 
v_unused_748_ = lean_ctor_get(v___x_692_, 1);
lean_dec(v_unused_748_);
v___x_695_ = v___x_692_;
v_isShared_696_ = v_isSharedCheck_747_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_toApplicative_693_);
lean_dec(v___x_692_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_747_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v_toFunctor_697_; lean_object* v_toSeq_698_; lean_object* v_toSeqLeft_699_; lean_object* v_toSeqRight_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_745_; 
v_toFunctor_697_ = lean_ctor_get(v_toApplicative_693_, 0);
v_toSeq_698_ = lean_ctor_get(v_toApplicative_693_, 2);
v_toSeqLeft_699_ = lean_ctor_get(v_toApplicative_693_, 3);
v_toSeqRight_700_ = lean_ctor_get(v_toApplicative_693_, 4);
v_isSharedCheck_745_ = !lean_is_exclusive(v_toApplicative_693_);
if (v_isSharedCheck_745_ == 0)
{
lean_object* v_unused_746_; 
v_unused_746_ = lean_ctor_get(v_toApplicative_693_, 1);
lean_dec(v_unused_746_);
v___x_702_ = v_toApplicative_693_;
v_isShared_703_ = v_isSharedCheck_745_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_toSeqRight_700_);
lean_inc(v_toSeqLeft_699_);
lean_inc(v_toSeq_698_);
lean_inc(v_toFunctor_697_);
lean_dec(v_toApplicative_693_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_745_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___f_704_; lean_object* v___f_705_; lean_object* v___f_706_; lean_object* v___f_707_; lean_object* v___x_708_; lean_object* v___f_709_; lean_object* v___f_710_; lean_object* v___f_711_; lean_object* v___x_713_; 
v___f_704_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__4));
v___f_705_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__5));
lean_inc_ref(v_toFunctor_697_);
v___f_706_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_706_, 0, v_toFunctor_697_);
v___f_707_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_707_, 0, v_toFunctor_697_);
v___x_708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_708_, 0, v___f_706_);
lean_ctor_set(v___x_708_, 1, v___f_707_);
v___f_709_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_709_, 0, v_toSeqRight_700_);
v___f_710_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_710_, 0, v_toSeqLeft_699_);
v___f_711_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_711_, 0, v_toSeq_698_);
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 4, v___f_709_);
lean_ctor_set(v___x_702_, 3, v___f_710_);
lean_ctor_set(v___x_702_, 2, v___f_711_);
lean_ctor_set(v___x_702_, 1, v___f_704_);
lean_ctor_set(v___x_702_, 0, v___x_708_);
v___x_713_ = v___x_702_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v___x_708_);
lean_ctor_set(v_reuseFailAlloc_744_, 1, v___f_704_);
lean_ctor_set(v_reuseFailAlloc_744_, 2, v___f_711_);
lean_ctor_set(v_reuseFailAlloc_744_, 3, v___f_710_);
lean_ctor_set(v_reuseFailAlloc_744_, 4, v___f_709_);
v___x_713_ = v_reuseFailAlloc_744_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
lean_object* v___x_715_; 
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 1, v___f_705_);
lean_ctor_set(v___x_695_, 0, v___x_713_);
v___x_715_ = v___x_695_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v___x_713_);
lean_ctor_set(v_reuseFailAlloc_743_, 1, v___f_705_);
v___x_715_ = v_reuseFailAlloc_743_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_716_ = l_StateRefT_x27_instMonad___redArg(v___x_715_);
v___x_717_ = l_ReaderT_instMonad___redArg(v___x_716_);
v___x_718_ = l_StateRefT_x27_instMonad___redArg(v___x_717_);
v___x_719_ = l_ReaderT_instMonad___redArg(v___x_718_);
v___x_720_ = l_ReaderT_instMonad___redArg(v___x_719_);
v___x_721_ = l_StateRefT_x27_instMonad___redArg(v___x_720_);
v___x_722_ = l_ReaderT_instMonad___redArg(v___x_721_);
v___x_723_ = lean_box(0);
v___x_724_ = l_Lean_Meta_Grind_Order_getStruct___redArg(v_a_664_, v_a_665_, v_a_673_);
if (lean_obj_tag(v___x_724_) == 0)
{
lean_object* v_a_725_; lean_object* v_targets_726_; lean_object* v_size_727_; uint8_t v___x_728_; 
v_a_725_ = lean_ctor_get(v___x_724_, 0);
lean_inc(v_a_725_);
lean_dec_ref_known(v___x_724_, 1);
v_targets_726_ = lean_ctor_get(v_a_725_, 6);
lean_inc_ref(v_targets_726_);
lean_dec(v_a_725_);
v_size_727_ = lean_ctor_get(v_targets_726_, 2);
v___x_728_ = lean_nat_dec_lt(v_u_662_, v_size_727_);
if (v___x_728_ == 0)
{
lean_object* v___x_729_; lean_object* v___x_839__overap_730_; lean_object* v___x_731_; 
lean_dec_ref(v_targets_726_);
v___x_729_ = l_outOfBounds___redArg(v___x_723_);
v___x_839__overap_730_ = l_Lean_AssocList_forM___redArg(v___x_722_, v_f_663_, v___x_729_);
lean_inc(v_a_674_);
lean_inc_ref(v_a_673_);
lean_inc(v_a_672_);
lean_inc_ref(v_a_671_);
lean_inc(v_a_670_);
lean_inc_ref(v_a_669_);
lean_inc(v_a_668_);
lean_inc_ref(v_a_667_);
lean_inc(v_a_666_);
lean_inc(v_a_665_);
lean_inc(v_a_664_);
v___x_731_ = lean_apply_12(v___x_839__overap_730_, v_a_664_, v_a_665_, v_a_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_, lean_box(0));
return v___x_731_;
}
else
{
lean_object* v___x_732_; lean_object* v___x_842__overap_733_; lean_object* v___x_734_; 
v___x_732_ = l_Lean_PersistentArray_get_x21___redArg(v___x_723_, v_targets_726_, v_u_662_);
lean_dec_ref(v_targets_726_);
v___x_842__overap_733_ = l_Lean_AssocList_forM___redArg(v___x_722_, v_f_663_, v___x_732_);
lean_inc(v_a_674_);
lean_inc_ref(v_a_673_);
lean_inc(v_a_672_);
lean_inc_ref(v_a_671_);
lean_inc(v_a_670_);
lean_inc_ref(v_a_669_);
lean_inc(v_a_668_);
lean_inc_ref(v_a_667_);
lean_inc(v_a_666_);
lean_inc(v_a_665_);
lean_inc(v_a_664_);
v___x_734_ = lean_apply_12(v___x_842__overap_733_, v_a_664_, v_a_665_, v_a_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_, lean_box(0));
return v___x_734_;
}
}
else
{
lean_object* v_a_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_742_; 
lean_dec_ref(v___x_722_);
lean_dec_ref(v_f_663_);
v_a_735_ = lean_ctor_get(v___x_724_, 0);
v_isSharedCheck_742_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_742_ == 0)
{
v___x_737_ = v___x_724_;
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_a_735_);
lean_dec(v___x_724_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_740_; 
if (v_isShared_738_ == 0)
{
v___x_740_ = v___x_737_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v_a_735_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachTargetOf___boxed(lean_object* v_u_749_, lean_object* v_f_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachTargetOf(v_u_749_, v_f_750_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_, v_a_759_, v_a_760_, v_a_761_);
lean_dec(v_a_761_);
lean_dec_ref(v_a_760_);
lean_dec(v_a_759_);
lean_dec_ref(v_a_758_);
lean_dec(v_a_757_);
lean_dec_ref(v_a_756_);
lean_dec(v_a_755_);
lean_dec_ref(v_a_754_);
lean_dec(v_a_753_);
lean_dec(v_a_752_);
lean_dec(v_a_751_);
lean_dec(v_u_749_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isShorter___redArg(lean_object* v_u_764_, lean_object* v_v_765_, lean_object* v_k_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_){
_start:
{
lean_object* v___x_771_; 
v___x_771_ = l_Lean_Meta_Grind_Order_getDist_x3f___redArg(v_u_764_, v_v_765_, v_a_767_, v_a_768_, v_a_769_);
if (lean_obj_tag(v___x_771_) == 0)
{
lean_object* v_a_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_791_; 
v_a_772_ = lean_ctor_get(v___x_771_, 0);
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_771_);
if (v_isSharedCheck_791_ == 0)
{
v___x_774_ = v___x_771_;
v_isShared_775_ = v_isSharedCheck_791_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_a_772_);
lean_dec(v___x_771_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_791_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
if (lean_obj_tag(v_a_772_) == 1)
{
lean_object* v_val_776_; uint8_t v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; uint8_t v___x_781_; lean_object* v___x_782_; lean_object* v___x_784_; 
v_val_776_ = lean_ctor_get(v_a_772_, 0);
lean_inc(v_val_776_);
lean_dec_ref_known(v_a_772_, 1);
v___x_777_ = l_Lean_Meta_Grind_Order_Weight_compare(v_k_766_, v_val_776_);
lean_dec(v_val_776_);
v___x_778_ = lean_box(v___x_777_);
v___x_779_ = lean_obj_tag_nat(v___x_778_);
lean_dec(v___x_778_);
v___x_780_ = lean_unsigned_to_nat(0u);
v___x_781_ = lean_nat_dec_eq(v___x_779_, v___x_780_);
v___x_782_ = lean_box(v___x_781_);
if (v_isShared_775_ == 0)
{
lean_ctor_set(v___x_774_, 0, v___x_782_);
v___x_784_ = v___x_774_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v___x_782_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
else
{
uint8_t v___x_786_; lean_object* v___x_787_; lean_object* v___x_789_; 
lean_dec(v_a_772_);
v___x_786_ = 1;
v___x_787_ = lean_box(v___x_786_);
if (v_isShared_775_ == 0)
{
lean_ctor_set(v___x_774_, 0, v___x_787_);
v___x_789_ = v___x_774_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v___x_787_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
}
}
else
{
lean_object* v_a_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_799_; 
v_a_792_ = lean_ctor_get(v___x_771_, 0);
v_isSharedCheck_799_ = !lean_is_exclusive(v___x_771_);
if (v_isSharedCheck_799_ == 0)
{
v___x_794_ = v___x_771_;
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_a_792_);
lean_dec(v___x_771_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_797_; 
if (v_isShared_795_ == 0)
{
v___x_797_ = v___x_794_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v_a_792_);
v___x_797_ = v_reuseFailAlloc_798_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
return v___x_797_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isShorter___redArg___boxed(lean_object* v_u_800_, lean_object* v_v_801_, lean_object* v_k_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_){
_start:
{
lean_object* v_res_807_; 
v_res_807_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isShorter___redArg(v_u_800_, v_v_801_, v_k_802_, v_a_803_, v_a_804_, v_a_805_);
lean_dec_ref(v_a_805_);
lean_dec(v_a_804_);
lean_dec(v_a_803_);
lean_dec_ref(v_k_802_);
lean_dec(v_v_801_);
lean_dec(v_u_800_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isShorter(lean_object* v_u_808_, lean_object* v_v_809_, lean_object* v_k_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_){
_start:
{
lean_object* v___x_823_; 
v___x_823_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isShorter___redArg(v_u_808_, v_v_809_, v_k_810_, v_a_811_, v_a_812_, v_a_820_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isShorter___boxed(lean_object* v_u_824_, lean_object* v_v_825_, lean_object* v_k_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isShorter(v_u_824_, v_v_825_, v_k_826_, v_a_827_, v_a_828_, v_a_829_, v_a_830_, v_a_831_, v_a_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_, v_a_837_);
lean_dec(v_a_837_);
lean_dec_ref(v_a_836_);
lean_dec(v_a_835_);
lean_dec_ref(v_a_834_);
lean_dec(v_a_833_);
lean_dec_ref(v_a_832_);
lean_dec(v_a_831_);
lean_dec_ref(v_a_830_);
lean_dec(v_a_829_);
lean_dec(v_a_828_);
lean_dec(v_a_827_);
lean_dec_ref(v_k_826_);
lean_dec(v_v_825_);
lean_dec(v_u_824_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___lam__0(lean_object* v_p_840_, lean_object* v_s_841_){
_start:
{
lean_object* v_id_842_; lean_object* v_nodes_843_; lean_object* v_nodeMap_844_; lean_object* v_cnstrs_845_; lean_object* v_cnstrsOf_846_; lean_object* v_sources_847_; lean_object* v_targets_848_; lean_object* v_proofs_849_; lean_object* v_propagate_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_858_; 
v_id_842_ = lean_ctor_get(v_s_841_, 0);
v_nodes_843_ = lean_ctor_get(v_s_841_, 1);
v_nodeMap_844_ = lean_ctor_get(v_s_841_, 2);
v_cnstrs_845_ = lean_ctor_get(v_s_841_, 3);
v_cnstrsOf_846_ = lean_ctor_get(v_s_841_, 4);
v_sources_847_ = lean_ctor_get(v_s_841_, 5);
v_targets_848_ = lean_ctor_get(v_s_841_, 6);
v_proofs_849_ = lean_ctor_get(v_s_841_, 7);
v_propagate_850_ = lean_ctor_get(v_s_841_, 8);
v_isSharedCheck_858_ = !lean_is_exclusive(v_s_841_);
if (v_isSharedCheck_858_ == 0)
{
v___x_852_ = v_s_841_;
v_isShared_853_ = v_isSharedCheck_858_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_propagate_850_);
lean_inc(v_proofs_849_);
lean_inc(v_targets_848_);
lean_inc(v_sources_847_);
lean_inc(v_cnstrsOf_846_);
lean_inc(v_cnstrs_845_);
lean_inc(v_nodeMap_844_);
lean_inc(v_nodes_843_);
lean_inc(v_id_842_);
lean_dec(v_s_841_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_858_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_854_; lean_object* v___x_856_; 
v___x_854_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_854_, 0, v_p_840_);
lean_ctor_set(v___x_854_, 1, v_propagate_850_);
if (v_isShared_853_ == 0)
{
lean_ctor_set(v___x_852_, 8, v___x_854_);
v___x_856_ = v___x_852_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v_id_842_);
lean_ctor_set(v_reuseFailAlloc_857_, 1, v_nodes_843_);
lean_ctor_set(v_reuseFailAlloc_857_, 2, v_nodeMap_844_);
lean_ctor_set(v_reuseFailAlloc_857_, 3, v_cnstrs_845_);
lean_ctor_set(v_reuseFailAlloc_857_, 4, v_cnstrsOf_846_);
lean_ctor_set(v_reuseFailAlloc_857_, 5, v_sources_847_);
lean_ctor_set(v_reuseFailAlloc_857_, 6, v_targets_848_);
lean_ctor_set(v_reuseFailAlloc_857_, 7, v_proofs_849_);
lean_ctor_set(v_reuseFailAlloc_857_, 8, v___x_854_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0_spec__0(lean_object* v_msgData_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_){
_start:
{
lean_object* v___x_865_; lean_object* v_env_866_; uint8_t v___x_867_; lean_object* v_env_868_; lean_object* v___x_869_; lean_object* v_toCold_870_; lean_object* v_mctx_871_; lean_object* v_lctx_872_; lean_object* v_options_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_865_ = lean_st_ref_get(v___y_863_);
v_env_866_ = lean_ctor_get(v___x_865_, 0);
lean_inc_ref(v_env_866_);
lean_dec(v___x_865_);
v___x_867_ = 0;
v_env_868_ = l_Lean_Environment_setRecordingDeps(v_env_866_, v___x_867_);
v___x_869_ = lean_st_ref_get(v___y_861_);
v_toCold_870_ = lean_ctor_get(v___y_862_, 0);
v_mctx_871_ = lean_ctor_get(v___x_869_, 0);
lean_inc_ref(v_mctx_871_);
lean_dec(v___x_869_);
v_lctx_872_ = lean_ctor_get(v___y_860_, 2);
v_options_873_ = lean_ctor_get(v_toCold_870_, 2);
lean_inc_ref(v_options_873_);
lean_inc_ref(v_lctx_872_);
v___x_874_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_874_, 0, v_env_868_);
lean_ctor_set(v___x_874_, 1, v_mctx_871_);
lean_ctor_set(v___x_874_, 2, v_lctx_872_);
lean_ctor_set(v___x_874_, 3, v_options_873_);
v___x_875_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_875_, 0, v___x_874_);
lean_ctor_set(v___x_875_, 1, v_msgData_859_);
v___x_876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_876_, 0, v___x_875_);
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0_spec__0___boxed(lean_object* v_msgData_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0_spec__0(v_msgData_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_);
lean_dec(v___y_881_);
lean_dec_ref(v___y_880_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
return v_res_883_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_884_; double v___x_885_; 
v___x_884_ = lean_unsigned_to_nat(0u);
v___x_885_ = lean_float_of_nat(v___x_884_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(lean_object* v_cls_889_, lean_object* v_msg_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_){
_start:
{
lean_object* v_ref_896_; lean_object* v___x_897_; lean_object* v_a_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_943_; 
v_ref_896_ = lean_ctor_get(v___y_893_, 2);
v___x_897_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0_spec__0(v_msg_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_);
v_a_898_ = lean_ctor_get(v___x_897_, 0);
v_isSharedCheck_943_ = !lean_is_exclusive(v___x_897_);
if (v_isSharedCheck_943_ == 0)
{
v___x_900_ = v___x_897_;
v_isShared_901_ = v_isSharedCheck_943_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_a_898_);
lean_dec(v___x_897_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_943_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v___x_902_; lean_object* v_traceState_903_; lean_object* v_env_904_; lean_object* v_nextMacroScope_905_; lean_object* v_ngen_906_; lean_object* v_auxDeclNGen_907_; lean_object* v_cache_908_; lean_object* v_recordedDeps_909_; lean_object* v_messages_910_; lean_object* v_infoState_911_; lean_object* v_snapshotTasks_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_942_; 
v___x_902_ = lean_st_ref_take(v___y_894_);
v_traceState_903_ = lean_ctor_get(v___x_902_, 4);
v_env_904_ = lean_ctor_get(v___x_902_, 0);
v_nextMacroScope_905_ = lean_ctor_get(v___x_902_, 1);
v_ngen_906_ = lean_ctor_get(v___x_902_, 2);
v_auxDeclNGen_907_ = lean_ctor_get(v___x_902_, 3);
v_cache_908_ = lean_ctor_get(v___x_902_, 5);
v_recordedDeps_909_ = lean_ctor_get(v___x_902_, 6);
v_messages_910_ = lean_ctor_get(v___x_902_, 7);
v_infoState_911_ = lean_ctor_get(v___x_902_, 8);
v_snapshotTasks_912_ = lean_ctor_get(v___x_902_, 9);
v_isSharedCheck_942_ = !lean_is_exclusive(v___x_902_);
if (v_isSharedCheck_942_ == 0)
{
v___x_914_ = v___x_902_;
v_isShared_915_ = v_isSharedCheck_942_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_snapshotTasks_912_);
lean_inc(v_infoState_911_);
lean_inc(v_messages_910_);
lean_inc(v_recordedDeps_909_);
lean_inc(v_cache_908_);
lean_inc(v_traceState_903_);
lean_inc(v_auxDeclNGen_907_);
lean_inc(v_ngen_906_);
lean_inc(v_nextMacroScope_905_);
lean_inc(v_env_904_);
lean_dec(v___x_902_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_942_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
uint64_t v_tid_916_; lean_object* v_traces_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_941_; 
v_tid_916_ = lean_ctor_get_uint64(v_traceState_903_, sizeof(void*)*1);
v_traces_917_ = lean_ctor_get(v_traceState_903_, 0);
v_isSharedCheck_941_ = !lean_is_exclusive(v_traceState_903_);
if (v_isSharedCheck_941_ == 0)
{
v___x_919_ = v_traceState_903_;
v_isShared_920_ = v_isSharedCheck_941_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_traces_917_);
lean_dec(v_traceState_903_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_941_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_921_; lean_object* v___x_922_; double v___x_923_; uint8_t v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_932_; 
v___x_921_ = lean_box(0);
v___x_922_ = lean_box(0);
v___x_923_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg___closed__0);
v___x_924_ = 0;
v___x_925_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg___closed__1));
v___x_926_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_926_, 0, v_cls_889_);
lean_ctor_set(v___x_926_, 1, v___x_922_);
lean_ctor_set(v___x_926_, 2, v___x_925_);
lean_ctor_set_float(v___x_926_, sizeof(void*)*3, v___x_923_);
lean_ctor_set_float(v___x_926_, sizeof(void*)*3 + 8, v___x_923_);
lean_ctor_set_uint8(v___x_926_, sizeof(void*)*3 + 16, v___x_924_);
v___x_927_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg___closed__2));
v___x_928_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_928_, 0, v___x_926_);
lean_ctor_set(v___x_928_, 1, v_a_898_);
lean_ctor_set(v___x_928_, 2, v___x_927_);
lean_inc(v_ref_896_);
v___x_929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_929_, 0, v_ref_896_);
lean_ctor_set(v___x_929_, 1, v___x_928_);
v___x_930_ = l_Lean_PersistentArray_push___redArg(v_traces_917_, v___x_929_);
if (v_isShared_920_ == 0)
{
lean_ctor_set(v___x_919_, 0, v___x_930_);
v___x_932_ = v___x_919_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v___x_930_);
lean_ctor_set_uint64(v_reuseFailAlloc_940_, sizeof(void*)*1, v_tid_916_);
v___x_932_ = v_reuseFailAlloc_940_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
lean_object* v___x_934_; 
if (v_isShared_915_ == 0)
{
lean_ctor_set(v___x_914_, 4, v___x_932_);
v___x_934_ = v___x_914_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v_env_904_);
lean_ctor_set(v_reuseFailAlloc_939_, 1, v_nextMacroScope_905_);
lean_ctor_set(v_reuseFailAlloc_939_, 2, v_ngen_906_);
lean_ctor_set(v_reuseFailAlloc_939_, 3, v_auxDeclNGen_907_);
lean_ctor_set(v_reuseFailAlloc_939_, 4, v___x_932_);
lean_ctor_set(v_reuseFailAlloc_939_, 5, v_cache_908_);
lean_ctor_set(v_reuseFailAlloc_939_, 6, v_recordedDeps_909_);
lean_ctor_set(v_reuseFailAlloc_939_, 7, v_messages_910_);
lean_ctor_set(v_reuseFailAlloc_939_, 8, v_infoState_911_);
lean_ctor_set(v_reuseFailAlloc_939_, 9, v_snapshotTasks_912_);
v___x_934_ = v_reuseFailAlloc_939_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
lean_object* v___x_935_; lean_object* v___x_937_; 
v___x_935_ = lean_st_ref_put(v___y_894_, v___x_934_);
if (v_isShared_901_ == 0)
{
lean_ctor_set(v___x_900_, 0, v___x_921_);
v___x_937_ = v___x_900_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v___x_921_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg___boxed(lean_object* v_cls_944_, lean_object* v_msg_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(v_cls_944_, v_msg_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_);
lean_dec(v___y_949_);
lean_dec_ref(v___y_948_);
lean_dec(v___y_947_);
lean_dec_ref(v___y_946_);
return v_res_951_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__7(void){
_start:
{
lean_object* v_cls_964_; lean_object* v___x_965_; lean_object* v___x_966_; 
v_cls_964_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__4));
v___x_965_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__6));
v___x_966_ = l_Lean_Name_append(v___x_965_, v_cls_964_);
return v___x_966_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate(lean_object* v_p_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_){
_start:
{
lean_object* v_toCold_980_; lean_object* v_options_981_; lean_object* v_inheritedTraceOptions_982_; uint8_t v_hasTrace_983_; lean_object* v___f_984_; 
v_toCold_980_ = lean_ctor_get(v_a_977_, 0);
v_options_981_ = lean_ctor_get(v_toCold_980_, 2);
v_inheritedTraceOptions_982_ = lean_ctor_get(v_toCold_980_, 11);
v_hasTrace_983_ = lean_ctor_get_uint8(v_options_981_, sizeof(void*)*1);
lean_inc_ref(v_p_967_);
v___f_984_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___lam__0), 2, 1);
lean_closure_set(v___f_984_, 0, v_p_967_);
if (v_hasTrace_983_ == 0)
{
lean_object* v___x_985_; 
lean_dec_ref(v_p_967_);
v___x_985_ = l_Lean_Meta_Grind_Order_modifyStruct___redArg(v___f_984_, v_a_968_, v_a_969_);
return v___x_985_;
}
else
{
lean_object* v_cls_986_; lean_object* v___x_987_; uint8_t v___x_988_; 
v_cls_986_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__4));
v___x_987_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__7, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__7);
v___x_988_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_982_, v_options_981_, v___x_987_);
if (v___x_988_ == 0)
{
lean_object* v___x_989_; 
lean_dec_ref(v_p_967_);
v___x_989_ = l_Lean_Meta_Grind_Order_modifyStruct___redArg(v___f_984_, v_a_968_, v_a_969_);
return v___x_989_;
}
else
{
lean_object* v___x_990_; 
v___x_990_ = l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg(v_p_967_, v_a_968_, v_a_969_, v_a_977_);
if (lean_obj_tag(v___x_990_) == 0)
{
lean_object* v_a_991_; lean_object* v___x_992_; 
v_a_991_ = lean_ctor_get(v___x_990_, 0);
lean_inc(v_a_991_);
lean_dec_ref_known(v___x_990_, 1);
v___x_992_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(v_cls_986_, v_a_991_, v_a_975_, v_a_976_, v_a_977_, v_a_978_);
if (lean_obj_tag(v___x_992_) == 0)
{
lean_object* v___x_993_; 
lean_dec_ref_known(v___x_992_, 1);
v___x_993_ = l_Lean_Meta_Grind_Order_modifyStruct___redArg(v___f_984_, v_a_968_, v_a_969_);
return v___x_993_;
}
else
{
lean_dec_ref(v___f_984_);
return v___x_992_;
}
}
else
{
lean_object* v_a_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1001_; 
lean_dec_ref(v___f_984_);
v_a_994_ = lean_ctor_get(v___x_990_, 0);
v_isSharedCheck_1001_ = !lean_is_exclusive(v___x_990_);
if (v_isSharedCheck_1001_ == 0)
{
v___x_996_ = v___x_990_;
v_isShared_997_ = v_isSharedCheck_1001_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_a_994_);
lean_dec(v___x_990_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1001_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v___x_999_; 
if (v_isShared_997_ == 0)
{
v___x_999_ = v___x_996_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v_a_994_);
v___x_999_ = v_reuseFailAlloc_1000_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
return v___x_999_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___boxed(lean_object* v_p_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate(v_p_1002_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_);
lean_dec(v_a_1013_);
lean_dec_ref(v_a_1012_);
lean_dec(v_a_1011_);
lean_dec_ref(v_a_1010_);
lean_dec(v_a_1009_);
lean_dec_ref(v_a_1008_);
lean_dec(v_a_1007_);
lean_dec_ref(v_a_1006_);
lean_dec(v_a_1005_);
lean_dec(v_a_1004_);
lean_dec(v_a_1003_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0(lean_object* v_cls_1016_, lean_object* v_msg_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_){
_start:
{
lean_object* v___x_1030_; 
v___x_1030_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(v_cls_1016_, v_msg_1017_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___boxed(lean_object* v_cls_1031_, lean_object* v_msg_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_){
_start:
{
lean_object* v_res_1045_; 
v_res_1045_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0(v_cls_1031_, v_msg_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_);
lean_dec(v___y_1043_);
lean_dec_ref(v___y_1042_);
lean_dec(v___y_1041_);
lean_dec_ref(v___y_1040_);
lean_dec(v___y_1039_);
lean_dec_ref(v___y_1038_);
lean_dec(v___y_1037_);
lean_dec_ref(v___y_1036_);
lean_dec(v___y_1035_);
lean_dec(v___y_1034_);
lean_dec(v___y_1033_);
return v_res_1045_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1046_, lean_object* v_vals_1047_, lean_object* v_i_1048_, lean_object* v_k_1049_){
_start:
{
lean_object* v___x_1050_; uint8_t v___x_1051_; 
v___x_1050_ = lean_array_get_size(v_keys_1046_);
v___x_1051_ = lean_nat_dec_lt(v_i_1048_, v___x_1050_);
if (v___x_1051_ == 0)
{
lean_object* v___x_1052_; 
lean_dec(v_i_1048_);
v___x_1052_ = lean_box(0);
return v___x_1052_;
}
else
{
lean_object* v_k_x27_1053_; size_t v___x_1054_; size_t v___x_1055_; uint8_t v___x_1056_; 
v_k_x27_1053_ = lean_array_fget_borrowed(v_keys_1046_, v_i_1048_);
v___x_1054_ = lean_ptr_addr(v_k_1049_);
v___x_1055_ = lean_ptr_addr(v_k_x27_1053_);
v___x_1056_ = lean_usize_dec_eq(v___x_1054_, v___x_1055_);
if (v___x_1056_ == 0)
{
lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1057_ = lean_unsigned_to_nat(1u);
v___x_1058_ = lean_nat_add(v_i_1048_, v___x_1057_);
lean_dec(v_i_1048_);
v_i_1048_ = v___x_1058_;
goto _start;
}
else
{
lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1060_ = lean_array_fget_borrowed(v_vals_1047_, v_i_1048_);
lean_dec(v_i_1048_);
lean_inc(v___x_1060_);
v___x_1061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1060_);
return v___x_1061_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1062_, lean_object* v_vals_1063_, lean_object* v_i_1064_, lean_object* v_k_1065_){
_start:
{
lean_object* v_res_1066_; 
v_res_1066_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0_spec__1___redArg(v_keys_1062_, v_vals_1063_, v_i_1064_, v_k_1065_);
lean_dec_ref(v_k_1065_);
lean_dec_ref(v_vals_1063_);
lean_dec_ref(v_keys_1062_);
return v_res_1066_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg(lean_object* v_x_1067_, size_t v_x_1068_, lean_object* v_x_1069_){
_start:
{
if (lean_obj_tag(v_x_1067_) == 0)
{
lean_object* v_es_1070_; lean_object* v___x_1071_; size_t v___x_1072_; size_t v___x_1073_; lean_object* v_j_1074_; lean_object* v___x_1075_; 
v_es_1070_ = lean_ctor_get(v_x_1067_, 0);
v___x_1071_ = lean_box(2);
v___x_1072_ = ((size_t)31ULL);
v___x_1073_ = lean_usize_land(v_x_1068_, v___x_1072_);
v_j_1074_ = lean_usize_to_nat(v___x_1073_);
v___x_1075_ = lean_array_get_borrowed(v___x_1071_, v_es_1070_, v_j_1074_);
lean_dec(v_j_1074_);
switch(lean_obj_tag(v___x_1075_))
{
case 0:
{
lean_object* v_key_1076_; lean_object* v_val_1077_; size_t v___x_1078_; size_t v___x_1079_; uint8_t v___x_1080_; 
v_key_1076_ = lean_ctor_get(v___x_1075_, 0);
v_val_1077_ = lean_ctor_get(v___x_1075_, 1);
v___x_1078_ = lean_ptr_addr(v_x_1069_);
v___x_1079_ = lean_ptr_addr(v_key_1076_);
v___x_1080_ = lean_usize_dec_eq(v___x_1078_, v___x_1079_);
if (v___x_1080_ == 0)
{
lean_object* v___x_1081_; 
v___x_1081_ = lean_box(0);
return v___x_1081_;
}
else
{
lean_object* v___x_1082_; 
lean_inc(v_val_1077_);
v___x_1082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1082_, 0, v_val_1077_);
return v___x_1082_;
}
}
case 1:
{
lean_object* v_node_1083_; size_t v___x_1084_; size_t v___x_1085_; 
v_node_1083_ = lean_ctor_get(v___x_1075_, 0);
v___x_1084_ = ((size_t)5ULL);
v___x_1085_ = lean_usize_shift_right(v_x_1068_, v___x_1084_);
v_x_1067_ = v_node_1083_;
v_x_1068_ = v___x_1085_;
goto _start;
}
default: 
{
lean_object* v___x_1087_; 
v___x_1087_ = lean_box(0);
return v___x_1087_;
}
}
}
else
{
lean_object* v_ks_1088_; lean_object* v_vs_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; 
v_ks_1088_ = lean_ctor_get(v_x_1067_, 0);
v_vs_1089_ = lean_ctor_get(v_x_1067_, 1);
v___x_1090_ = lean_unsigned_to_nat(0u);
v___x_1091_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0_spec__1___redArg(v_ks_1088_, v_vs_1089_, v___x_1090_, v_x_1069_);
return v___x_1091_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg___boxed(lean_object* v_x_1092_, lean_object* v_x_1093_, lean_object* v_x_1094_){
_start:
{
size_t v_x_9901__boxed_1095_; lean_object* v_res_1096_; 
v_x_9901__boxed_1095_ = lean_unbox_usize(v_x_1093_);
lean_dec(v_x_1093_);
v_res_1096_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg(v_x_1092_, v_x_9901__boxed_1095_, v_x_1094_);
lean_dec_ref(v_x_1094_);
lean_dec_ref(v_x_1092_);
return v_res_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(lean_object* v_x_1097_, lean_object* v_x_1098_){
_start:
{
size_t v___x_1099_; size_t v___x_1100_; size_t v___x_1101_; uint64_t v___x_1102_; size_t v___x_1103_; lean_object* v___x_1104_; 
v___x_1099_ = lean_ptr_addr(v_x_1098_);
v___x_1100_ = ((size_t)3ULL);
v___x_1101_ = lean_usize_shift_right(v___x_1099_, v___x_1100_);
v___x_1102_ = lean_usize_to_uint64(v___x_1101_);
v___x_1103_ = lean_uint64_to_usize(v___x_1102_);
v___x_1104_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg(v_x_1097_, v___x_1103_, v_x_1098_);
return v___x_1104_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg___boxed(lean_object* v_x_1105_, lean_object* v_x_1106_){
_start:
{
lean_object* v_res_1107_; 
v_res_1107_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_x_1105_, v_x_1106_);
lean_dec_ref(v_x_1106_);
lean_dec_ref(v_x_1105_);
return v_res_1107_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5(void){
_start:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1117_ = lean_box(0);
v___x_1118_ = ((lean_object*)(l_Lean_Meta_Grind_Order_propagateEqTrue___closed__4));
v___x_1119_ = l_Lean_mkConst(v___x_1118_, v___x_1117_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateEqTrue(lean_object* v_c_1120_, lean_object* v_e_1121_, lean_object* v_u_1122_, lean_object* v_v_1123_, lean_object* v_k_1124_, lean_object* v_k_x27_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_){
_start:
{
lean_object* v_h_1139_; lean_object* v___y_1140_; lean_object* v___y_1141_; lean_object* v___y_1142_; lean_object* v___y_1143_; lean_object* v___y_1144_; lean_object* v___y_1145_; lean_object* v___y_1146_; lean_object* v___x_1166_; 
v___x_1166_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath(v_u_1122_, v_v_1123_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_);
if (lean_obj_tag(v___x_1166_) == 0)
{
lean_object* v_a_1167_; lean_object* v___x_1168_; 
v_a_1167_ = lean_ctor_get(v___x_1166_, 0);
lean_inc(v_a_1167_);
lean_dec_ref_known(v___x_1166_, 1);
v___x_1168_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_u_1122_, v_a_1126_, v_a_1127_, v_a_1135_);
if (lean_obj_tag(v___x_1168_) == 0)
{
lean_object* v_a_1169_; lean_object* v___x_1170_; 
v_a_1169_ = lean_ctor_get(v___x_1168_, 0);
lean_inc(v_a_1169_);
lean_dec_ref_known(v___x_1168_, 1);
v___x_1170_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_v_1123_, v_a_1126_, v_a_1127_, v_a_1135_);
if (lean_obj_tag(v___x_1170_) == 0)
{
lean_object* v_a_1171_; lean_object* v___x_1172_; 
v_a_1171_ = lean_ctor_get(v___x_1170_, 0);
lean_inc(v_a_1171_);
lean_dec_ref_known(v___x_1170_, 1);
v___x_1172_ = l_Lean_Meta_Grind_Order_mkPropagateEqTrueProof(v_a_1169_, v_a_1171_, v_k_1124_, v_a_1167_, v_k_x27_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_);
if (lean_obj_tag(v___x_1172_) == 0)
{
lean_object* v_h_x3f_1173_; 
v_h_x3f_1173_ = lean_ctor_get(v_c_1120_, 4);
lean_inc(v_h_x3f_1173_);
if (lean_obj_tag(v_h_x3f_1173_) == 1)
{
lean_object* v_a_1174_; lean_object* v_e_1175_; lean_object* v_val_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; 
v_a_1174_ = lean_ctor_get(v___x_1172_, 0);
lean_inc(v_a_1174_);
lean_dec_ref_known(v___x_1172_, 1);
v_e_1175_ = lean_ctor_get(v_c_1120_, 3);
lean_inc_ref(v_e_1175_);
lean_dec_ref(v_c_1120_);
v_val_1176_ = lean_ctor_get(v_h_x3f_1173_, 0);
lean_inc(v_val_1176_);
lean_dec_ref_known(v_h_x3f_1173_, 1);
v___x_1177_ = lean_obj_once(&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5, &l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5_once, _init_l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5);
lean_inc_ref(v_e_1121_);
v___x_1178_ = l_Lean_mkApp4(v___x_1177_, v_e_1121_, v_e_1175_, v_val_1176_, v_a_1174_);
v_h_1139_ = v___x_1178_;
v___y_1140_ = v_a_1127_;
v___y_1141_ = v_a_1129_;
v___y_1142_ = v_a_1131_;
v___y_1143_ = v_a_1133_;
v___y_1144_ = v_a_1134_;
v___y_1145_ = v_a_1135_;
v___y_1146_ = v_a_1136_;
goto v___jp_1138_;
}
else
{
lean_object* v_a_1179_; 
lean_dec(v_h_x3f_1173_);
lean_dec_ref(v_c_1120_);
v_a_1179_ = lean_ctor_get(v___x_1172_, 0);
lean_inc(v_a_1179_);
lean_dec_ref_known(v___x_1172_, 1);
v_h_1139_ = v_a_1179_;
v___y_1140_ = v_a_1127_;
v___y_1141_ = v_a_1129_;
v___y_1142_ = v_a_1131_;
v___y_1143_ = v_a_1133_;
v___y_1144_ = v_a_1134_;
v___y_1145_ = v_a_1135_;
v___y_1146_ = v_a_1136_;
goto v___jp_1138_;
}
}
else
{
lean_object* v_a_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1187_; 
lean_dec_ref(v_e_1121_);
lean_dec_ref(v_c_1120_);
v_a_1180_ = lean_ctor_get(v___x_1172_, 0);
v_isSharedCheck_1187_ = !lean_is_exclusive(v___x_1172_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1182_ = v___x_1172_;
v_isShared_1183_ = v_isSharedCheck_1187_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_a_1180_);
lean_dec(v___x_1172_);
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
else
{
lean_object* v_a_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1195_; 
lean_dec(v_a_1169_);
lean_dec(v_a_1167_);
lean_dec_ref(v_e_1121_);
lean_dec_ref(v_c_1120_);
v_a_1188_ = lean_ctor_get(v___x_1170_, 0);
v_isSharedCheck_1195_ = !lean_is_exclusive(v___x_1170_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1190_ = v___x_1170_;
v_isShared_1191_ = v_isSharedCheck_1195_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_a_1188_);
lean_dec(v___x_1170_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1195_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v___x_1193_; 
if (v_isShared_1191_ == 0)
{
v___x_1193_ = v___x_1190_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_a_1188_);
v___x_1193_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
return v___x_1193_;
}
}
}
}
else
{
lean_object* v_a_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1203_; 
lean_dec(v_a_1167_);
lean_dec_ref(v_e_1121_);
lean_dec_ref(v_c_1120_);
v_a_1196_ = lean_ctor_get(v___x_1168_, 0);
v_isSharedCheck_1203_ = !lean_is_exclusive(v___x_1168_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1198_ = v___x_1168_;
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_a_1196_);
lean_dec(v___x_1168_);
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
lean_dec_ref(v_e_1121_);
lean_dec_ref(v_c_1120_);
v_a_1204_ = lean_ctor_get(v___x_1166_, 0);
v_isSharedCheck_1211_ = !lean_is_exclusive(v___x_1166_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1206_ = v___x_1166_;
v_isShared_1207_ = v_isSharedCheck_1211_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_a_1204_);
lean_dec(v___x_1166_);
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
v___jp_1138_:
{
lean_object* v___x_1147_; 
v___x_1147_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v___y_1140_, v___y_1145_);
if (lean_obj_tag(v___x_1147_) == 0)
{
lean_object* v_a_1148_; lean_object* v_termMapInv_1149_; lean_object* v___x_1150_; 
v_a_1148_ = lean_ctor_get(v___x_1147_, 0);
lean_inc(v_a_1148_);
lean_dec_ref_known(v___x_1147_, 1);
v_termMapInv_1149_ = lean_ctor_get(v_a_1148_, 4);
lean_inc_ref(v_termMapInv_1149_);
lean_dec(v_a_1148_);
v___x_1150_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMapInv_1149_, v_e_1121_);
lean_dec_ref(v_termMapInv_1149_);
if (lean_obj_tag(v___x_1150_) == 1)
{
lean_object* v_val_1151_; lean_object* v_fst_1152_; lean_object* v_snd_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; 
v_val_1151_ = lean_ctor_get(v___x_1150_, 0);
lean_inc(v_val_1151_);
lean_dec_ref_known(v___x_1150_, 1);
v_fst_1152_ = lean_ctor_get(v_val_1151_, 0);
lean_inc_n(v_fst_1152_, 2);
v_snd_1153_ = lean_ctor_get(v_val_1151_, 1);
lean_inc(v_snd_1153_);
lean_dec(v_val_1151_);
v___x_1154_ = lean_obj_once(&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5, &l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5_once, _init_l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5);
v___x_1155_ = l_Lean_mkApp4(v___x_1154_, v_fst_1152_, v_e_1121_, v_snd_1153_, v_h_1139_);
v___x_1156_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_fst_1152_, v___x_1155_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_);
return v___x_1156_;
}
else
{
lean_object* v___x_1157_; 
lean_dec(v___x_1150_);
v___x_1157_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_e_1121_, v_h_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_);
return v___x_1157_;
}
}
else
{
lean_object* v_a_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1165_; 
lean_dec_ref(v_h_1139_);
lean_dec_ref(v_e_1121_);
v_a_1158_ = lean_ctor_get(v___x_1147_, 0);
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1160_ = v___x_1147_;
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_a_1158_);
lean_dec(v___x_1147_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1163_; 
if (v_isShared_1161_ == 0)
{
v___x_1163_ = v___x_1160_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_a_1158_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateEqTrue___boxed(lean_object** _args){
lean_object* v_c_1212_ = _args[0];
lean_object* v_e_1213_ = _args[1];
lean_object* v_u_1214_ = _args[2];
lean_object* v_v_1215_ = _args[3];
lean_object* v_k_1216_ = _args[4];
lean_object* v_k_x27_1217_ = _args[5];
lean_object* v_a_1218_ = _args[6];
lean_object* v_a_1219_ = _args[7];
lean_object* v_a_1220_ = _args[8];
lean_object* v_a_1221_ = _args[9];
lean_object* v_a_1222_ = _args[10];
lean_object* v_a_1223_ = _args[11];
lean_object* v_a_1224_ = _args[12];
lean_object* v_a_1225_ = _args[13];
lean_object* v_a_1226_ = _args[14];
lean_object* v_a_1227_ = _args[15];
lean_object* v_a_1228_ = _args[16];
lean_object* v_a_1229_ = _args[17];
_start:
{
lean_object* v_res_1230_; 
v_res_1230_ = l_Lean_Meta_Grind_Order_propagateEqTrue(v_c_1212_, v_e_1213_, v_u_1214_, v_v_1215_, v_k_1216_, v_k_x27_1217_, v_a_1218_, v_a_1219_, v_a_1220_, v_a_1221_, v_a_1222_, v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_);
lean_dec(v_a_1228_);
lean_dec_ref(v_a_1227_);
lean_dec(v_a_1226_);
lean_dec_ref(v_a_1225_);
lean_dec(v_a_1224_);
lean_dec_ref(v_a_1223_);
lean_dec(v_a_1222_);
lean_dec_ref(v_a_1221_);
lean_dec(v_a_1220_);
lean_dec(v_a_1219_);
lean_dec(v_a_1218_);
lean_dec_ref(v_k_x27_1217_);
lean_dec_ref(v_k_1216_);
lean_dec(v_v_1215_);
lean_dec(v_u_1214_);
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0(lean_object* v_00_u03b2_1231_, lean_object* v_x_1232_, lean_object* v_x_1233_){
_start:
{
lean_object* v___x_1234_; 
v___x_1234_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_x_1232_, v_x_1233_);
return v___x_1234_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___boxed(lean_object* v_00_u03b2_1235_, lean_object* v_x_1236_, lean_object* v_x_1237_){
_start:
{
lean_object* v_res_1238_; 
v_res_1238_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0(v_00_u03b2_1235_, v_x_1236_, v_x_1237_);
lean_dec_ref(v_x_1237_);
lean_dec_ref(v_x_1236_);
return v_res_1238_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0(lean_object* v_00_u03b2_1239_, lean_object* v_x_1240_, size_t v_x_1241_, lean_object* v_x_1242_){
_start:
{
lean_object* v___x_1243_; 
v___x_1243_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg(v_x_1240_, v_x_1241_, v_x_1242_);
return v___x_1243_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1244_, lean_object* v_x_1245_, lean_object* v_x_1246_, lean_object* v_x_1247_){
_start:
{
size_t v_x_10169__boxed_1248_; lean_object* v_res_1249_; 
v_x_10169__boxed_1248_ = lean_unbox_usize(v_x_1246_);
lean_dec(v_x_1246_);
v_res_1249_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0(v_00_u03b2_1244_, v_x_1245_, v_x_10169__boxed_1248_, v_x_1247_);
lean_dec_ref(v_x_1247_);
lean_dec_ref(v_x_1245_);
return v_res_1249_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1250_, lean_object* v_keys_1251_, lean_object* v_vals_1252_, lean_object* v_heq_1253_, lean_object* v_i_1254_, lean_object* v_k_1255_){
_start:
{
lean_object* v___x_1256_; 
v___x_1256_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0_spec__1___redArg(v_keys_1251_, v_vals_1252_, v_i_1254_, v_k_1255_);
return v___x_1256_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1257_, lean_object* v_keys_1258_, lean_object* v_vals_1259_, lean_object* v_heq_1260_, lean_object* v_i_1261_, lean_object* v_k_1262_){
_start:
{
lean_object* v_res_1263_; 
v_res_1263_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0_spec__1(v_00_u03b2_1257_, v_keys_1258_, v_vals_1259_, v_heq_1260_, v_i_1261_, v_k_1262_);
lean_dec_ref(v_k_1262_);
lean_dec_ref(v_vals_1259_);
lean_dec_ref(v_keys_1258_);
return v_res_1263_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1264_; 
v___x_1264_ = l_Lean_Meta_Grind_instInhabitedGoalM___redArg();
return v___x_1264_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0(lean_object* v_msg_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_){
_start:
{
lean_object* v___x_1278_; lean_object* v___f_1279_; lean_object* v___x_5398__overap_1280_; lean_object* v___x_1281_; 
v___x_1278_ = lean_obj_once(&l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0___closed__0, &l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0___closed__0_once, _init_l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0___closed__0);
v___f_1279_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1279_, 0, v___x_1278_);
v___x_5398__overap_1280_ = lean_panic_fn_borrowed(v___f_1279_, v_msg_1265_);
lean_dec_ref(v___f_1279_);
lean_inc(v___y_1276_);
lean_inc_ref(v___y_1275_);
lean_inc(v___y_1274_);
lean_inc_ref(v___y_1273_);
lean_inc(v___y_1272_);
lean_inc_ref(v___y_1271_);
lean_inc(v___y_1270_);
lean_inc_ref(v___y_1269_);
lean_inc(v___y_1268_);
lean_inc(v___y_1267_);
lean_inc(v___y_1266_);
v___x_1281_ = lean_apply_12(v___x_5398__overap_1280_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_, lean_box(0));
return v___x_1281_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0___boxed(lean_object* v_msg_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_){
_start:
{
lean_object* v_res_1295_; 
v_res_1295_ = l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0(v_msg_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_);
lean_dec(v___y_1293_);
lean_dec_ref(v___y_1292_);
lean_dec(v___y_1291_);
lean_dec_ref(v___y_1290_);
lean_dec(v___y_1289_);
lean_dec_ref(v___y_1288_);
lean_dec(v___y_1287_);
lean_dec_ref(v___y_1286_);
lean_dec(v___y_1285_);
lean_dec(v___y_1284_);
lean_dec(v___y_1283_);
return v_res_1295_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__3(void){
_start:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; 
v___x_1299_ = ((lean_object*)(l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__2));
v___x_1300_ = lean_unsigned_to_nat(2u);
v___x_1301_ = lean_unsigned_to_nat(86u);
v___x_1302_ = ((lean_object*)(l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__1));
v___x_1303_ = ((lean_object*)(l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__0));
v___x_1304_ = l_mkPanicMessageWithDecl(v___x_1303_, v___x_1302_, v___x_1301_, v___x_1300_, v___x_1299_);
return v___x_1304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateSelfEqTrue(lean_object* v_c_1305_, lean_object* v_e_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_){
_start:
{
lean_object* v_h_1320_; lean_object* v___y_1321_; lean_object* v___y_1322_; lean_object* v___y_1323_; lean_object* v___y_1324_; lean_object* v___y_1325_; lean_object* v___y_1326_; lean_object* v___y_1327_; lean_object* v_u_1347_; lean_object* v_v_1348_; lean_object* v_e_1349_; lean_object* v_h_x3f_1350_; lean_object* v___x_1351_; 
v_u_1347_ = lean_ctor_get(v_c_1305_, 0);
v_v_1348_ = lean_ctor_get(v_c_1305_, 1);
v_e_1349_ = lean_ctor_get(v_c_1305_, 3);
lean_inc_ref(v_e_1349_);
v_h_x3f_1350_ = lean_ctor_get(v_c_1305_, 4);
lean_inc(v_h_x3f_1350_);
v___x_1351_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_u_1347_, v_a_1307_, v_a_1308_, v_a_1316_);
if (lean_obj_tag(v___x_1351_) == 0)
{
lean_object* v_a_1352_; uint8_t v___x_1353_; 
v_a_1352_ = lean_ctor_get(v___x_1351_, 0);
lean_inc(v_a_1352_);
lean_dec_ref_known(v___x_1351_, 1);
v___x_1353_ = lean_nat_dec_eq(v_u_1347_, v_v_1348_);
if (v___x_1353_ == 0)
{
lean_object* v___x_1354_; lean_object* v___x_1355_; 
lean_dec(v_a_1352_);
lean_dec(v_h_x3f_1350_);
lean_dec_ref(v_e_1349_);
lean_dec_ref(v_e_1306_);
lean_dec_ref(v_c_1305_);
v___x_1354_ = lean_obj_once(&l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__3, &l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__3_once, _init_l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__3);
v___x_1355_ = l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0(v___x_1354_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_);
return v___x_1355_;
}
else
{
lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___x_1356_ = l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(v_c_1305_);
lean_dec_ref(v_c_1305_);
v___x_1357_ = l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof(v_a_1352_, v___x_1356_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_);
lean_dec_ref(v___x_1356_);
if (lean_obj_tag(v___x_1357_) == 0)
{
if (lean_obj_tag(v_h_x3f_1350_) == 1)
{
lean_object* v_a_1358_; lean_object* v_val_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; 
v_a_1358_ = lean_ctor_get(v___x_1357_, 0);
lean_inc(v_a_1358_);
lean_dec_ref_known(v___x_1357_, 1);
v_val_1359_ = lean_ctor_get(v_h_x3f_1350_, 0);
lean_inc(v_val_1359_);
lean_dec_ref_known(v_h_x3f_1350_, 1);
v___x_1360_ = lean_obj_once(&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5, &l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5_once, _init_l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5);
lean_inc_ref(v_e_1306_);
v___x_1361_ = l_Lean_mkApp4(v___x_1360_, v_e_1306_, v_e_1349_, v_val_1359_, v_a_1358_);
v_h_1320_ = v___x_1361_;
v___y_1321_ = v_a_1308_;
v___y_1322_ = v_a_1310_;
v___y_1323_ = v_a_1312_;
v___y_1324_ = v_a_1314_;
v___y_1325_ = v_a_1315_;
v___y_1326_ = v_a_1316_;
v___y_1327_ = v_a_1317_;
goto v___jp_1319_;
}
else
{
lean_object* v_a_1362_; 
lean_dec(v_h_x3f_1350_);
lean_dec_ref(v_e_1349_);
v_a_1362_ = lean_ctor_get(v___x_1357_, 0);
lean_inc(v_a_1362_);
lean_dec_ref_known(v___x_1357_, 1);
v_h_1320_ = v_a_1362_;
v___y_1321_ = v_a_1308_;
v___y_1322_ = v_a_1310_;
v___y_1323_ = v_a_1312_;
v___y_1324_ = v_a_1314_;
v___y_1325_ = v_a_1315_;
v___y_1326_ = v_a_1316_;
v___y_1327_ = v_a_1317_;
goto v___jp_1319_;
}
}
else
{
lean_object* v_a_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1370_; 
lean_dec(v_h_x3f_1350_);
lean_dec_ref(v_e_1349_);
lean_dec_ref(v_e_1306_);
v_a_1363_ = lean_ctor_get(v___x_1357_, 0);
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1357_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1365_ = v___x_1357_;
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_a_1363_);
lean_dec(v___x_1357_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v___x_1368_; 
if (v_isShared_1366_ == 0)
{
v___x_1368_ = v___x_1365_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v_a_1363_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
}
}
}
else
{
lean_object* v_a_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1378_; 
lean_dec(v_h_x3f_1350_);
lean_dec_ref(v_e_1349_);
lean_dec_ref(v_e_1306_);
lean_dec_ref(v_c_1305_);
v_a_1371_ = lean_ctor_get(v___x_1351_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1351_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1373_ = v___x_1351_;
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_a_1371_);
lean_dec(v___x_1351_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1376_; 
if (v_isShared_1374_ == 0)
{
v___x_1376_ = v___x_1373_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_a_1371_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
v___jp_1319_:
{
lean_object* v___x_1328_; 
v___x_1328_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v___y_1321_, v___y_1326_);
if (lean_obj_tag(v___x_1328_) == 0)
{
lean_object* v_a_1329_; lean_object* v_termMapInv_1330_; lean_object* v___x_1331_; 
v_a_1329_ = lean_ctor_get(v___x_1328_, 0);
lean_inc(v_a_1329_);
lean_dec_ref_known(v___x_1328_, 1);
v_termMapInv_1330_ = lean_ctor_get(v_a_1329_, 4);
lean_inc_ref(v_termMapInv_1330_);
lean_dec(v_a_1329_);
v___x_1331_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMapInv_1330_, v_e_1306_);
lean_dec_ref(v_termMapInv_1330_);
if (lean_obj_tag(v___x_1331_) == 1)
{
lean_object* v_val_1332_; lean_object* v_fst_1333_; lean_object* v_snd_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; 
v_val_1332_ = lean_ctor_get(v___x_1331_, 0);
lean_inc(v_val_1332_);
lean_dec_ref_known(v___x_1331_, 1);
v_fst_1333_ = lean_ctor_get(v_val_1332_, 0);
lean_inc_n(v_fst_1333_, 2);
v_snd_1334_ = lean_ctor_get(v_val_1332_, 1);
lean_inc(v_snd_1334_);
lean_dec(v_val_1332_);
v___x_1335_ = lean_obj_once(&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5, &l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5_once, _init_l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5);
v___x_1336_ = l_Lean_mkApp4(v___x_1335_, v_fst_1333_, v_e_1306_, v_snd_1334_, v_h_1320_);
v___x_1337_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_fst_1333_, v___x_1336_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_);
return v___x_1337_;
}
else
{
lean_object* v___x_1338_; 
lean_dec(v___x_1331_);
v___x_1338_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_e_1306_, v_h_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_);
return v___x_1338_;
}
}
else
{
lean_object* v_a_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1346_; 
lean_dec_ref(v_h_1320_);
lean_dec_ref(v_e_1306_);
v_a_1339_ = lean_ctor_get(v___x_1328_, 0);
v_isSharedCheck_1346_ = !lean_is_exclusive(v___x_1328_);
if (v_isSharedCheck_1346_ == 0)
{
v___x_1341_ = v___x_1328_;
v_isShared_1342_ = v_isSharedCheck_1346_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_a_1339_);
lean_dec(v___x_1328_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1346_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v___x_1344_; 
if (v_isShared_1342_ == 0)
{
v___x_1344_ = v___x_1341_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v_a_1339_);
v___x_1344_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
return v___x_1344_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateSelfEqTrue___boxed(lean_object* v_c_1379_, lean_object* v_e_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_){
_start:
{
lean_object* v_res_1393_; 
v_res_1393_ = l_Lean_Meta_Grind_Order_propagateSelfEqTrue(v_c_1379_, v_e_1380_, v_a_1381_, v_a_1382_, v_a_1383_, v_a_1384_, v_a_1385_, v_a_1386_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_);
lean_dec(v_a_1391_);
lean_dec_ref(v_a_1390_);
lean_dec(v_a_1389_);
lean_dec_ref(v_a_1388_);
lean_dec(v_a_1387_);
lean_dec_ref(v_a_1386_);
lean_dec(v_a_1385_);
lean_dec_ref(v_a_1384_);
lean_dec(v_a_1383_);
lean_dec(v_a_1382_);
lean_dec(v_a_1381_);
return v_res_1393_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2(void){
_start:
{
lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; 
v___x_1400_ = lean_box(0);
v___x_1401_ = ((lean_object*)(l_Lean_Meta_Grind_Order_propagateEqFalse___closed__1));
v___x_1402_ = l_Lean_mkConst(v___x_1401_, v___x_1400_);
return v___x_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateEqFalse(lean_object* v_c_1403_, lean_object* v_e_1404_, lean_object* v_u_1405_, lean_object* v_v_1406_, lean_object* v_k_1407_, lean_object* v_k_x27_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_, lean_object* v_a_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_){
_start:
{
lean_object* v_h_1422_; lean_object* v___y_1423_; lean_object* v___y_1424_; lean_object* v___y_1425_; lean_object* v___y_1426_; lean_object* v___y_1427_; lean_object* v___y_1428_; lean_object* v___y_1429_; lean_object* v___x_1449_; 
v___x_1449_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath(v_u_1405_, v_v_1406_, v_a_1409_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_, v_a_1414_, v_a_1415_, v_a_1416_, v_a_1417_, v_a_1418_, v_a_1419_);
if (lean_obj_tag(v___x_1449_) == 0)
{
lean_object* v_a_1450_; lean_object* v___x_1451_; 
v_a_1450_ = lean_ctor_get(v___x_1449_, 0);
lean_inc(v_a_1450_);
lean_dec_ref_known(v___x_1449_, 1);
v___x_1451_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_u_1405_, v_a_1409_, v_a_1410_, v_a_1418_);
if (lean_obj_tag(v___x_1451_) == 0)
{
lean_object* v_a_1452_; lean_object* v___x_1453_; 
v_a_1452_ = lean_ctor_get(v___x_1451_, 0);
lean_inc(v_a_1452_);
lean_dec_ref_known(v___x_1451_, 1);
v___x_1453_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_v_1406_, v_a_1409_, v_a_1410_, v_a_1418_);
if (lean_obj_tag(v___x_1453_) == 0)
{
lean_object* v_a_1454_; lean_object* v___x_1455_; 
v_a_1454_ = lean_ctor_get(v___x_1453_, 0);
lean_inc(v_a_1454_);
lean_dec_ref_known(v___x_1453_, 1);
v___x_1455_ = l_Lean_Meta_Grind_Order_mkPropagateEqFalseProof(v_a_1452_, v_a_1454_, v_k_1407_, v_a_1450_, v_k_x27_1408_, v_a_1409_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_, v_a_1414_, v_a_1415_, v_a_1416_, v_a_1417_, v_a_1418_, v_a_1419_);
if (lean_obj_tag(v___x_1455_) == 0)
{
lean_object* v_h_x3f_1456_; 
v_h_x3f_1456_ = lean_ctor_get(v_c_1403_, 4);
lean_inc(v_h_x3f_1456_);
if (lean_obj_tag(v_h_x3f_1456_) == 1)
{
lean_object* v_a_1457_; lean_object* v_e_1458_; lean_object* v_val_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; 
v_a_1457_ = lean_ctor_get(v___x_1455_, 0);
lean_inc(v_a_1457_);
lean_dec_ref_known(v___x_1455_, 1);
v_e_1458_ = lean_ctor_get(v_c_1403_, 3);
lean_inc_ref(v_e_1458_);
lean_dec_ref(v_c_1403_);
v_val_1459_ = lean_ctor_get(v_h_x3f_1456_, 0);
lean_inc(v_val_1459_);
lean_dec_ref_known(v_h_x3f_1456_, 1);
v___x_1460_ = lean_obj_once(&l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2, &l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2_once, _init_l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2);
lean_inc_ref(v_e_1404_);
v___x_1461_ = l_Lean_mkApp4(v___x_1460_, v_e_1404_, v_e_1458_, v_val_1459_, v_a_1457_);
v_h_1422_ = v___x_1461_;
v___y_1423_ = v_a_1410_;
v___y_1424_ = v_a_1412_;
v___y_1425_ = v_a_1414_;
v___y_1426_ = v_a_1416_;
v___y_1427_ = v_a_1417_;
v___y_1428_ = v_a_1418_;
v___y_1429_ = v_a_1419_;
goto v___jp_1421_;
}
else
{
lean_object* v_a_1462_; 
lean_dec(v_h_x3f_1456_);
lean_dec_ref(v_c_1403_);
v_a_1462_ = lean_ctor_get(v___x_1455_, 0);
lean_inc(v_a_1462_);
lean_dec_ref_known(v___x_1455_, 1);
v_h_1422_ = v_a_1462_;
v___y_1423_ = v_a_1410_;
v___y_1424_ = v_a_1412_;
v___y_1425_ = v_a_1414_;
v___y_1426_ = v_a_1416_;
v___y_1427_ = v_a_1417_;
v___y_1428_ = v_a_1418_;
v___y_1429_ = v_a_1419_;
goto v___jp_1421_;
}
}
else
{
lean_object* v_a_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1470_; 
lean_dec_ref(v_e_1404_);
lean_dec_ref(v_c_1403_);
v_a_1463_ = lean_ctor_get(v___x_1455_, 0);
v_isSharedCheck_1470_ = !lean_is_exclusive(v___x_1455_);
if (v_isSharedCheck_1470_ == 0)
{
v___x_1465_ = v___x_1455_;
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_a_1463_);
lean_dec(v___x_1455_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
lean_object* v___x_1468_; 
if (v_isShared_1466_ == 0)
{
v___x_1468_ = v___x_1465_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v_a_1463_);
v___x_1468_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
return v___x_1468_;
}
}
}
}
else
{
lean_object* v_a_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1478_; 
lean_dec(v_a_1452_);
lean_dec(v_a_1450_);
lean_dec_ref(v_e_1404_);
lean_dec_ref(v_c_1403_);
v_a_1471_ = lean_ctor_get(v___x_1453_, 0);
v_isSharedCheck_1478_ = !lean_is_exclusive(v___x_1453_);
if (v_isSharedCheck_1478_ == 0)
{
v___x_1473_ = v___x_1453_;
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_a_1471_);
lean_dec(v___x_1453_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1478_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1476_; 
if (v_isShared_1474_ == 0)
{
v___x_1476_ = v___x_1473_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v_a_1471_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
}
}
else
{
lean_object* v_a_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1486_; 
lean_dec(v_a_1450_);
lean_dec_ref(v_e_1404_);
lean_dec_ref(v_c_1403_);
v_a_1479_ = lean_ctor_get(v___x_1451_, 0);
v_isSharedCheck_1486_ = !lean_is_exclusive(v___x_1451_);
if (v_isSharedCheck_1486_ == 0)
{
v___x_1481_ = v___x_1451_;
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_a_1479_);
lean_dec(v___x_1451_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1486_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v___x_1484_; 
if (v_isShared_1482_ == 0)
{
v___x_1484_ = v___x_1481_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v_a_1479_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
}
}
else
{
lean_object* v_a_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1494_; 
lean_dec_ref(v_e_1404_);
lean_dec_ref(v_c_1403_);
v_a_1487_ = lean_ctor_get(v___x_1449_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1449_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1489_ = v___x_1449_;
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_a_1487_);
lean_dec(v___x_1449_);
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
v___jp_1421_:
{
lean_object* v___x_1430_; 
v___x_1430_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v___y_1423_, v___y_1428_);
if (lean_obj_tag(v___x_1430_) == 0)
{
lean_object* v_a_1431_; lean_object* v_termMapInv_1432_; lean_object* v___x_1433_; 
v_a_1431_ = lean_ctor_get(v___x_1430_, 0);
lean_inc(v_a_1431_);
lean_dec_ref_known(v___x_1430_, 1);
v_termMapInv_1432_ = lean_ctor_get(v_a_1431_, 4);
lean_inc_ref(v_termMapInv_1432_);
lean_dec(v_a_1431_);
v___x_1433_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMapInv_1432_, v_e_1404_);
lean_dec_ref(v_termMapInv_1432_);
if (lean_obj_tag(v___x_1433_) == 1)
{
lean_object* v_val_1434_; lean_object* v_fst_1435_; lean_object* v_snd_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; 
v_val_1434_ = lean_ctor_get(v___x_1433_, 0);
lean_inc(v_val_1434_);
lean_dec_ref_known(v___x_1433_, 1);
v_fst_1435_ = lean_ctor_get(v_val_1434_, 0);
lean_inc_n(v_fst_1435_, 2);
v_snd_1436_ = lean_ctor_get(v_val_1434_, 1);
lean_inc(v_snd_1436_);
lean_dec(v_val_1434_);
v___x_1437_ = lean_obj_once(&l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2, &l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2_once, _init_l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2);
v___x_1438_ = l_Lean_mkApp4(v___x_1437_, v_fst_1435_, v_e_1404_, v_snd_1436_, v_h_1422_);
v___x_1439_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_fst_1435_, v___x_1438_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_);
return v___x_1439_;
}
else
{
lean_object* v___x_1440_; 
lean_dec(v___x_1433_);
v___x_1440_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_e_1404_, v_h_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_);
return v___x_1440_;
}
}
else
{
lean_object* v_a_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1448_; 
lean_dec_ref(v_h_1422_);
lean_dec_ref(v_e_1404_);
v_a_1441_ = lean_ctor_get(v___x_1430_, 0);
v_isSharedCheck_1448_ = !lean_is_exclusive(v___x_1430_);
if (v_isSharedCheck_1448_ == 0)
{
v___x_1443_ = v___x_1430_;
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
else
{
lean_inc(v_a_1441_);
lean_dec(v___x_1430_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v___x_1446_; 
if (v_isShared_1444_ == 0)
{
v___x_1446_ = v___x_1443_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v_a_1441_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
return v___x_1446_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateEqFalse___boxed(lean_object** _args){
lean_object* v_c_1495_ = _args[0];
lean_object* v_e_1496_ = _args[1];
lean_object* v_u_1497_ = _args[2];
lean_object* v_v_1498_ = _args[3];
lean_object* v_k_1499_ = _args[4];
lean_object* v_k_x27_1500_ = _args[5];
lean_object* v_a_1501_ = _args[6];
lean_object* v_a_1502_ = _args[7];
lean_object* v_a_1503_ = _args[8];
lean_object* v_a_1504_ = _args[9];
lean_object* v_a_1505_ = _args[10];
lean_object* v_a_1506_ = _args[11];
lean_object* v_a_1507_ = _args[12];
lean_object* v_a_1508_ = _args[13];
lean_object* v_a_1509_ = _args[14];
lean_object* v_a_1510_ = _args[15];
lean_object* v_a_1511_ = _args[16];
lean_object* v_a_1512_ = _args[17];
_start:
{
lean_object* v_res_1513_; 
v_res_1513_ = l_Lean_Meta_Grind_Order_propagateEqFalse(v_c_1495_, v_e_1496_, v_u_1497_, v_v_1498_, v_k_1499_, v_k_x27_1500_, v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_);
lean_dec(v_a_1511_);
lean_dec_ref(v_a_1510_);
lean_dec(v_a_1509_);
lean_dec_ref(v_a_1508_);
lean_dec(v_a_1507_);
lean_dec_ref(v_a_1506_);
lean_dec(v_a_1505_);
lean_dec_ref(v_a_1504_);
lean_dec(v_a_1503_);
lean_dec(v_a_1502_);
lean_dec(v_a_1501_);
lean_dec_ref(v_k_x27_1500_);
lean_dec_ref(v_k_1499_);
lean_dec(v_v_1498_);
lean_dec(v_u_1497_);
return v_res_1513_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_propagateSelfEqFalse___closed__1(void){
_start:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; 
v___x_1515_ = ((lean_object*)(l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__2));
v___x_1516_ = lean_unsigned_to_nat(2u);
v___x_1517_ = lean_unsigned_to_nat(111u);
v___x_1518_ = ((lean_object*)(l_Lean_Meta_Grind_Order_propagateSelfEqFalse___closed__0));
v___x_1519_ = ((lean_object*)(l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__0));
v___x_1520_ = l_mkPanicMessageWithDecl(v___x_1519_, v___x_1518_, v___x_1517_, v___x_1516_, v___x_1515_);
return v___x_1520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateSelfEqFalse(lean_object* v_c_1521_, lean_object* v_e_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_){
_start:
{
lean_object* v_h_1536_; lean_object* v___y_1537_; lean_object* v___y_1538_; lean_object* v___y_1539_; lean_object* v___y_1540_; lean_object* v___y_1541_; lean_object* v___y_1542_; lean_object* v___y_1543_; lean_object* v_u_1563_; lean_object* v_v_1564_; lean_object* v_e_1565_; lean_object* v_h_x3f_1566_; lean_object* v___x_1567_; 
v_u_1563_ = lean_ctor_get(v_c_1521_, 0);
v_v_1564_ = lean_ctor_get(v_c_1521_, 1);
v_e_1565_ = lean_ctor_get(v_c_1521_, 3);
lean_inc_ref(v_e_1565_);
v_h_x3f_1566_ = lean_ctor_get(v_c_1521_, 4);
lean_inc(v_h_x3f_1566_);
v___x_1567_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_u_1563_, v_a_1523_, v_a_1524_, v_a_1532_);
if (lean_obj_tag(v___x_1567_) == 0)
{
lean_object* v_a_1568_; uint8_t v___x_1569_; 
v_a_1568_ = lean_ctor_get(v___x_1567_, 0);
lean_inc(v_a_1568_);
lean_dec_ref_known(v___x_1567_, 1);
v___x_1569_ = lean_nat_dec_eq(v_u_1563_, v_v_1564_);
if (v___x_1569_ == 0)
{
lean_object* v___x_1570_; lean_object* v___x_1571_; 
lean_dec(v_a_1568_);
lean_dec(v_h_x3f_1566_);
lean_dec_ref(v_e_1565_);
lean_dec_ref(v_e_1522_);
lean_dec_ref(v_c_1521_);
v___x_1570_ = lean_obj_once(&l_Lean_Meta_Grind_Order_propagateSelfEqFalse___closed__1, &l_Lean_Meta_Grind_Order_propagateSelfEqFalse___closed__1_once, _init_l_Lean_Meta_Grind_Order_propagateSelfEqFalse___closed__1);
v___x_1571_ = l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0(v___x_1570_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_, v_a_1527_, v_a_1528_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_);
return v___x_1571_;
}
else
{
lean_object* v___x_1572_; lean_object* v___x_1573_; 
v___x_1572_ = l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(v_c_1521_);
lean_dec_ref(v_c_1521_);
v___x_1573_ = l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof(v_a_1568_, v___x_1572_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_, v_a_1527_, v_a_1528_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_);
lean_dec_ref(v___x_1572_);
if (lean_obj_tag(v___x_1573_) == 0)
{
if (lean_obj_tag(v_h_x3f_1566_) == 1)
{
lean_object* v_a_1574_; lean_object* v_val_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; 
v_a_1574_ = lean_ctor_get(v___x_1573_, 0);
lean_inc(v_a_1574_);
lean_dec_ref_known(v___x_1573_, 1);
v_val_1575_ = lean_ctor_get(v_h_x3f_1566_, 0);
lean_inc(v_val_1575_);
lean_dec_ref_known(v_h_x3f_1566_, 1);
v___x_1576_ = lean_obj_once(&l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2, &l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2_once, _init_l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2);
lean_inc_ref(v_e_1522_);
v___x_1577_ = l_Lean_mkApp4(v___x_1576_, v_e_1522_, v_e_1565_, v_val_1575_, v_a_1574_);
v_h_1536_ = v___x_1577_;
v___y_1537_ = v_a_1524_;
v___y_1538_ = v_a_1526_;
v___y_1539_ = v_a_1528_;
v___y_1540_ = v_a_1530_;
v___y_1541_ = v_a_1531_;
v___y_1542_ = v_a_1532_;
v___y_1543_ = v_a_1533_;
goto v___jp_1535_;
}
else
{
lean_object* v_a_1578_; 
lean_dec(v_h_x3f_1566_);
lean_dec_ref(v_e_1565_);
v_a_1578_ = lean_ctor_get(v___x_1573_, 0);
lean_inc(v_a_1578_);
lean_dec_ref_known(v___x_1573_, 1);
v_h_1536_ = v_a_1578_;
v___y_1537_ = v_a_1524_;
v___y_1538_ = v_a_1526_;
v___y_1539_ = v_a_1528_;
v___y_1540_ = v_a_1530_;
v___y_1541_ = v_a_1531_;
v___y_1542_ = v_a_1532_;
v___y_1543_ = v_a_1533_;
goto v___jp_1535_;
}
}
else
{
lean_object* v_a_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1586_; 
lean_dec(v_h_x3f_1566_);
lean_dec_ref(v_e_1565_);
lean_dec_ref(v_e_1522_);
v_a_1579_ = lean_ctor_get(v___x_1573_, 0);
v_isSharedCheck_1586_ = !lean_is_exclusive(v___x_1573_);
if (v_isSharedCheck_1586_ == 0)
{
v___x_1581_ = v___x_1573_;
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_a_1579_);
lean_dec(v___x_1573_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v___x_1584_; 
if (v_isShared_1582_ == 0)
{
v___x_1584_ = v___x_1581_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v_a_1579_);
v___x_1584_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
return v___x_1584_;
}
}
}
}
}
else
{
lean_object* v_a_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1594_; 
lean_dec(v_h_x3f_1566_);
lean_dec_ref(v_e_1565_);
lean_dec_ref(v_e_1522_);
lean_dec_ref(v_c_1521_);
v_a_1587_ = lean_ctor_get(v___x_1567_, 0);
v_isSharedCheck_1594_ = !lean_is_exclusive(v___x_1567_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1589_ = v___x_1567_;
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_a_1587_);
lean_dec(v___x_1567_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v___x_1592_; 
if (v_isShared_1590_ == 0)
{
v___x_1592_ = v___x_1589_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_a_1587_);
v___x_1592_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
return v___x_1592_;
}
}
}
v___jp_1535_:
{
lean_object* v___x_1544_; 
v___x_1544_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v___y_1537_, v___y_1542_);
if (lean_obj_tag(v___x_1544_) == 0)
{
lean_object* v_a_1545_; lean_object* v_termMapInv_1546_; lean_object* v___x_1547_; 
v_a_1545_ = lean_ctor_get(v___x_1544_, 0);
lean_inc(v_a_1545_);
lean_dec_ref_known(v___x_1544_, 1);
v_termMapInv_1546_ = lean_ctor_get(v_a_1545_, 4);
lean_inc_ref(v_termMapInv_1546_);
lean_dec(v_a_1545_);
v___x_1547_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMapInv_1546_, v_e_1522_);
lean_dec_ref(v_termMapInv_1546_);
if (lean_obj_tag(v___x_1547_) == 1)
{
lean_object* v_val_1548_; lean_object* v_fst_1549_; lean_object* v_snd_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; 
v_val_1548_ = lean_ctor_get(v___x_1547_, 0);
lean_inc(v_val_1548_);
lean_dec_ref_known(v___x_1547_, 1);
v_fst_1549_ = lean_ctor_get(v_val_1548_, 0);
lean_inc_n(v_fst_1549_, 2);
v_snd_1550_ = lean_ctor_get(v_val_1548_, 1);
lean_inc(v_snd_1550_);
lean_dec(v_val_1548_);
v___x_1551_ = lean_obj_once(&l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2, &l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2_once, _init_l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2);
v___x_1552_ = l_Lean_mkApp4(v___x_1551_, v_fst_1549_, v_e_1522_, v_snd_1550_, v_h_1536_);
v___x_1553_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_fst_1549_, v___x_1552_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_);
return v___x_1553_;
}
else
{
lean_object* v___x_1554_; 
lean_dec(v___x_1547_);
v___x_1554_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_e_1522_, v_h_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_);
return v___x_1554_;
}
}
else
{
lean_object* v_a_1555_; lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1562_; 
lean_dec_ref(v_h_1536_);
lean_dec_ref(v_e_1522_);
v_a_1555_ = lean_ctor_get(v___x_1544_, 0);
v_isSharedCheck_1562_ = !lean_is_exclusive(v___x_1544_);
if (v_isSharedCheck_1562_ == 0)
{
v___x_1557_ = v___x_1544_;
v_isShared_1558_ = v_isSharedCheck_1562_;
goto v_resetjp_1556_;
}
else
{
lean_inc(v_a_1555_);
lean_dec(v___x_1544_);
v___x_1557_ = lean_box(0);
v_isShared_1558_ = v_isSharedCheck_1562_;
goto v_resetjp_1556_;
}
v_resetjp_1556_:
{
lean_object* v___x_1560_; 
if (v_isShared_1558_ == 0)
{
v___x_1560_ = v___x_1557_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v_a_1555_);
v___x_1560_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
return v___x_1560_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateSelfEqFalse___boxed(lean_object* v_c_1595_, lean_object* v_e_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_){
_start:
{
lean_object* v_res_1609_; 
v_res_1609_ = l_Lean_Meta_Grind_Order_propagateSelfEqFalse(v_c_1595_, v_e_1596_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_, v_a_1607_);
lean_dec(v_a_1607_);
lean_dec_ref(v_a_1606_);
lean_dec(v_a_1605_);
lean_dec_ref(v_a_1604_);
lean_dec(v_a_1603_);
lean_dec_ref(v_a_1602_);
lean_dec(v_a_1601_);
lean_dec_ref(v_a_1600_);
lean_dec(v_a_1599_);
lean_dec(v_a_1598_);
lean_dec(v_a_1597_);
return v_res_1609_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f___redArg(lean_object* v_e_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_){
_start:
{
lean_object* v___x_1614_; 
v___x_1614_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_1611_, v_a_1612_);
if (lean_obj_tag(v___x_1614_) == 0)
{
lean_object* v_a_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1624_; 
v_a_1615_ = lean_ctor_get(v___x_1614_, 0);
v_isSharedCheck_1624_ = !lean_is_exclusive(v___x_1614_);
if (v_isSharedCheck_1624_ == 0)
{
v___x_1617_ = v___x_1614_;
v_isShared_1618_ = v_isSharedCheck_1624_;
goto v_resetjp_1616_;
}
else
{
lean_inc(v_a_1615_);
lean_dec(v___x_1614_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1624_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
lean_object* v_termMapInv_1619_; lean_object* v___x_1620_; lean_object* v___x_1622_; 
v_termMapInv_1619_ = lean_ctor_get(v_a_1615_, 4);
lean_inc_ref(v_termMapInv_1619_);
lean_dec(v_a_1615_);
v___x_1620_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMapInv_1619_, v_e_1610_);
lean_dec_ref(v_termMapInv_1619_);
if (v_isShared_1618_ == 0)
{
lean_ctor_set(v___x_1617_, 0, v___x_1620_);
v___x_1622_ = v___x_1617_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v___x_1620_);
v___x_1622_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
return v___x_1622_;
}
}
}
else
{
lean_object* v_a_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1632_; 
v_a_1625_ = lean_ctor_get(v___x_1614_, 0);
v_isSharedCheck_1632_ = !lean_is_exclusive(v___x_1614_);
if (v_isSharedCheck_1632_ == 0)
{
v___x_1627_ = v___x_1614_;
v_isShared_1628_ = v_isSharedCheck_1632_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_a_1625_);
lean_dec(v___x_1614_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1632_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v___x_1630_; 
if (v_isShared_1628_ == 0)
{
v___x_1630_ = v___x_1627_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v_a_1625_);
v___x_1630_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
return v___x_1630_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f___redArg___boxed(lean_object* v_e_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_){
_start:
{
lean_object* v_res_1637_; 
v_res_1637_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f___redArg(v_e_1633_, v_a_1634_, v_a_1635_);
lean_dec_ref(v_a_1635_);
lean_dec(v_a_1634_);
lean_dec_ref(v_e_1633_);
return v_res_1637_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f(lean_object* v_e_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_){
_start:
{
lean_object* v___x_1650_; 
v___x_1650_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f___redArg(v_e_1638_, v_a_1639_, v_a_1647_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f___boxed(lean_object* v_e_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_){
_start:
{
lean_object* v_res_1663_; 
v_res_1663_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f(v_e_1651_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_);
lean_dec(v_a_1661_);
lean_dec_ref(v_a_1660_);
lean_dec(v_a_1659_);
lean_dec_ref(v_a_1658_);
lean_dec(v_a_1657_);
lean_dec_ref(v_a_1656_);
lean_dec(v_a_1655_);
lean_dec_ref(v_a_1654_);
lean_dec(v_a_1653_);
lean_dec(v_a_1652_);
lean_dec_ref(v_e_1651_);
return v_res_1663_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending___lam__0(lean_object* v_s_1664_){
_start:
{
lean_object* v_id_1665_; lean_object* v_nodes_1666_; lean_object* v_nodeMap_1667_; lean_object* v_cnstrs_1668_; lean_object* v_cnstrsOf_1669_; lean_object* v_sources_1670_; lean_object* v_targets_1671_; lean_object* v_proofs_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1680_; 
v_id_1665_ = lean_ctor_get(v_s_1664_, 0);
v_nodes_1666_ = lean_ctor_get(v_s_1664_, 1);
v_nodeMap_1667_ = lean_ctor_get(v_s_1664_, 2);
v_cnstrs_1668_ = lean_ctor_get(v_s_1664_, 3);
v_cnstrsOf_1669_ = lean_ctor_get(v_s_1664_, 4);
v_sources_1670_ = lean_ctor_get(v_s_1664_, 5);
v_targets_1671_ = lean_ctor_get(v_s_1664_, 6);
v_proofs_1672_ = lean_ctor_get(v_s_1664_, 7);
v_isSharedCheck_1680_ = !lean_is_exclusive(v_s_1664_);
if (v_isSharedCheck_1680_ == 0)
{
lean_object* v_unused_1681_; 
v_unused_1681_ = lean_ctor_get(v_s_1664_, 8);
lean_dec(v_unused_1681_);
v___x_1674_ = v_s_1664_;
v_isShared_1675_ = v_isSharedCheck_1680_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_proofs_1672_);
lean_inc(v_targets_1671_);
lean_inc(v_sources_1670_);
lean_inc(v_cnstrsOf_1669_);
lean_inc(v_cnstrs_1668_);
lean_inc(v_nodeMap_1667_);
lean_inc(v_nodes_1666_);
lean_inc(v_id_1665_);
lean_dec(v_s_1664_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1680_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1676_; lean_object* v___x_1678_; 
v___x_1676_ = lean_box(0);
if (v_isShared_1675_ == 0)
{
lean_ctor_set(v___x_1674_, 8, v___x_1676_);
v___x_1678_ = v___x_1674_;
goto v_reusejp_1677_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v_id_1665_);
lean_ctor_set(v_reuseFailAlloc_1679_, 1, v_nodes_1666_);
lean_ctor_set(v_reuseFailAlloc_1679_, 2, v_nodeMap_1667_);
lean_ctor_set(v_reuseFailAlloc_1679_, 3, v_cnstrs_1668_);
lean_ctor_set(v_reuseFailAlloc_1679_, 4, v_cnstrsOf_1669_);
lean_ctor_set(v_reuseFailAlloc_1679_, 5, v_sources_1670_);
lean_ctor_set(v_reuseFailAlloc_1679_, 6, v_targets_1671_);
lean_ctor_set(v_reuseFailAlloc_1679_, 7, v_proofs_1672_);
lean_ctor_set(v_reuseFailAlloc_1679_, 8, v___x_1676_);
v___x_1678_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1677_;
}
v_reusejp_1677_:
{
return v___x_1678_;
}
}
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; 
v___x_1688_ = lean_box(0);
v___x_1689_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg___closed__1));
v___x_1690_ = l_Lean_mkConst(v___x_1689_, v___x_1688_);
return v___x_1690_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg(lean_object* v_as_x27_1691_, lean_object* v_b_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_){
_start:
{
if (lean_obj_tag(v_as_x27_1691_) == 0)
{
lean_object* v___x_1705_; 
v___x_1705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1705_, 0, v_b_1692_);
return v___x_1705_;
}
else
{
lean_object* v_head_1706_; lean_object* v_tail_1707_; lean_object* v___x_1708_; 
v_head_1706_ = lean_ctor_get(v_as_x27_1691_, 0);
v_tail_1707_ = lean_ctor_get(v_as_x27_1691_, 1);
v___x_1708_ = lean_box(0);
switch(lean_obj_tag(v_head_1706_))
{
case 0:
{
lean_object* v_c_1709_; lean_object* v_e_1710_; lean_object* v_u_1711_; lean_object* v_v_1712_; lean_object* v_k_1713_; lean_object* v_k_x27_1714_; lean_object* v___x_1715_; 
v_c_1709_ = lean_ctor_get(v_head_1706_, 0);
v_e_1710_ = lean_ctor_get(v_head_1706_, 1);
v_u_1711_ = lean_ctor_get(v_head_1706_, 2);
v_v_1712_ = lean_ctor_get(v_head_1706_, 3);
v_k_1713_ = lean_ctor_get(v_head_1706_, 4);
v_k_x27_1714_ = lean_ctor_get(v_head_1706_, 5);
lean_inc_ref(v_e_1710_);
lean_inc_ref(v_c_1709_);
v___x_1715_ = l_Lean_Meta_Grind_Order_propagateEqTrue(v_c_1709_, v_e_1710_, v_u_1711_, v_v_1712_, v_k_1713_, v_k_x27_1714_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
if (lean_obj_tag(v___x_1715_) == 0)
{
lean_dec_ref_known(v___x_1715_, 1);
v_as_x27_1691_ = v_tail_1707_;
v_b_1692_ = v___x_1708_;
goto _start;
}
else
{
return v___x_1715_;
}
}
case 1:
{
lean_object* v_c_1717_; lean_object* v_e_1718_; lean_object* v_u_1719_; lean_object* v_v_1720_; lean_object* v_k_1721_; lean_object* v_k_x27_1722_; lean_object* v___x_1723_; 
v_c_1717_ = lean_ctor_get(v_head_1706_, 0);
v_e_1718_ = lean_ctor_get(v_head_1706_, 1);
v_u_1719_ = lean_ctor_get(v_head_1706_, 2);
v_v_1720_ = lean_ctor_get(v_head_1706_, 3);
v_k_1721_ = lean_ctor_get(v_head_1706_, 4);
v_k_x27_1722_ = lean_ctor_get(v_head_1706_, 5);
lean_inc_ref(v_e_1718_);
lean_inc_ref(v_c_1717_);
v___x_1723_ = l_Lean_Meta_Grind_Order_propagateEqFalse(v_c_1717_, v_e_1718_, v_u_1719_, v_v_1720_, v_k_1721_, v_k_x27_1722_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
if (lean_obj_tag(v___x_1723_) == 0)
{
lean_dec_ref_known(v___x_1723_, 1);
v_as_x27_1691_ = v_tail_1707_;
v_b_1692_ = v___x_1708_;
goto _start;
}
else
{
return v___x_1723_;
}
}
default: 
{
lean_object* v_u_1725_; lean_object* v_v_1726_; lean_object* v___x_1727_; 
v_u_1725_ = lean_ctor_get(v_head_1706_, 0);
v_v_1726_ = lean_ctor_get(v_head_1706_, 1);
v___x_1727_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_u_1725_, v___y_1693_, v___y_1694_, v___y_1702_);
if (lean_obj_tag(v___x_1727_) == 0)
{
lean_object* v_a_1728_; lean_object* v___x_1729_; 
v_a_1728_ = lean_ctor_get(v___x_1727_, 0);
lean_inc(v_a_1728_);
lean_dec_ref_known(v___x_1727_, 1);
v___x_1729_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_v_1726_, v___y_1693_, v___y_1694_, v___y_1702_);
if (lean_obj_tag(v___x_1729_) == 0)
{
lean_object* v_a_1730_; lean_object* v___y_1732_; lean_object* v___y_1733_; lean_object* v___y_1734_; lean_object* v___y_1735_; lean_object* v___y_1736_; lean_object* v___y_1737_; lean_object* v___y_1738_; lean_object* v___y_1739_; lean_object* v___y_1740_; lean_object* v___y_1741_; lean_object* v___y_1742_; lean_object* v___y_1743_; lean_object* v___y_1744_; lean_object* v___y_1745_; lean_object* v___y_1746_; lean_object* v___y_1747_; lean_object* v___y_1820_; lean_object* v___y_1821_; lean_object* v___y_1822_; lean_object* v___y_1823_; lean_object* v___y_1824_; lean_object* v___y_1825_; lean_object* v___y_1826_; lean_object* v___y_1827_; lean_object* v___y_1828_; lean_object* v___y_1829_; lean_object* v___y_1830_; lean_object* v___y_1864_; lean_object* v___x_1918_; 
v_a_1730_ = lean_ctor_get(v___x_1729_, 0);
lean_inc(v_a_1730_);
lean_dec_ref_known(v___x_1729_, 1);
v___x_1918_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_a_1728_, v___y_1694_);
if (lean_obj_tag(v___x_1918_) == 0)
{
lean_object* v_a_1919_; uint8_t v___x_1920_; 
v_a_1919_ = lean_ctor_get(v___x_1918_, 0);
v___x_1920_ = lean_unbox(v_a_1919_);
if (v___x_1920_ == 0)
{
v___y_1864_ = v___x_1918_;
goto v___jp_1863_;
}
else
{
lean_object* v___x_1921_; 
lean_dec_ref_known(v___x_1918_, 1);
v___x_1921_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_a_1730_, v___y_1694_);
v___y_1864_ = v___x_1921_;
goto v___jp_1863_;
}
}
else
{
v___y_1864_ = v___x_1918_;
goto v___jp_1863_;
}
v___jp_1731_:
{
if (lean_obj_tag(v___y_1747_) == 0)
{
lean_object* v_a_1748_; uint8_t v___x_1749_; 
v_a_1748_ = lean_ctor_get(v___y_1747_, 0);
lean_inc(v_a_1748_);
lean_dec_ref_known(v___y_1747_, 1);
v___x_1749_ = lean_unbox(v_a_1748_);
lean_dec(v_a_1748_);
if (v___x_1749_ == 0)
{
lean_dec_ref(v___y_1745_);
lean_dec_ref(v___y_1741_);
lean_dec_ref(v___y_1737_);
lean_dec_ref(v___y_1733_);
lean_dec(v_a_1730_);
lean_dec(v_a_1728_);
v_as_x27_1691_ = v_tail_1707_;
v_b_1692_ = v___x_1708_;
goto _start;
}
else
{
lean_object* v___x_1751_; 
v___x_1751_ = l_Lean_Meta_Grind_isEqv___redArg(v___y_1745_, v___y_1733_, v___y_1743_);
if (lean_obj_tag(v___x_1751_) == 0)
{
lean_object* v_a_1752_; uint8_t v___x_1753_; 
v_a_1752_ = lean_ctor_get(v___x_1751_, 0);
lean_inc(v_a_1752_);
lean_dec_ref_known(v___x_1751_, 1);
v___x_1753_ = lean_unbox(v_a_1752_);
if (v___x_1753_ == 0)
{
lean_object* v___x_1754_; 
v___x_1754_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath(v_u_1725_, v_v_1726_, v___y_1736_, v___y_1743_, v___y_1744_, v___y_1732_, v___y_1734_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1746_, v___y_1742_, v___y_1735_);
if (lean_obj_tag(v___x_1754_) == 0)
{
lean_object* v_a_1755_; lean_object* v___x_1756_; 
v_a_1755_ = lean_ctor_get(v___x_1754_, 0);
lean_inc(v_a_1755_);
lean_dec_ref_known(v___x_1754_, 1);
v___x_1756_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath(v_v_1726_, v_u_1725_, v___y_1736_, v___y_1743_, v___y_1744_, v___y_1732_, v___y_1734_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1746_, v___y_1742_, v___y_1735_);
if (lean_obj_tag(v___x_1756_) == 0)
{
lean_object* v_a_1757_; lean_object* v___x_1758_; 
v_a_1757_ = lean_ctor_get(v___x_1756_, 0);
lean_inc(v_a_1757_);
lean_dec_ref_known(v___x_1756_, 1);
lean_inc(v_a_1730_);
lean_inc(v_a_1728_);
v___x_1758_ = l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLe(v_a_1728_, v_a_1730_, v_a_1755_, v_a_1757_, v___y_1736_, v___y_1743_, v___y_1744_, v___y_1732_, v___y_1734_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1746_, v___y_1742_, v___y_1735_);
if (lean_obj_tag(v___x_1758_) == 0)
{
lean_object* v_a_1759_; lean_object* v___x_1760_; 
v_a_1759_ = lean_ctor_get(v___x_1758_, 0);
lean_inc(v_a_1759_);
lean_dec_ref_known(v___x_1758_, 1);
lean_inc(v___y_1735_);
lean_inc_ref(v___y_1742_);
lean_inc(v___y_1746_);
lean_inc_ref(v___y_1740_);
lean_inc(v_a_1728_);
v___x_1760_ = lean_infer_type(v_a_1728_, v___y_1740_, v___y_1746_, v___y_1742_, v___y_1735_);
if (lean_obj_tag(v___x_1760_) == 0)
{
lean_object* v_a_1761_; lean_object* v___x_1762_; uint8_t v___x_1763_; 
v_a_1761_ = lean_ctor_get(v___x_1760_, 0);
lean_inc(v_a_1761_);
lean_dec_ref_known(v___x_1760_, 1);
v___x_1762_ = l_Lean_Int_mkType;
v___x_1763_ = lean_expr_eqv(v_a_1761_, v___x_1762_);
lean_dec(v_a_1761_);
if (v___x_1763_ == 0)
{
lean_dec(v_a_1759_);
lean_dec(v_a_1752_);
lean_dec_ref(v___y_1745_);
lean_dec_ref(v___y_1741_);
lean_dec_ref(v___y_1737_);
lean_dec_ref(v___y_1733_);
lean_dec(v_a_1730_);
lean_dec(v_a_1728_);
v_as_x27_1691_ = v_tail_1707_;
v_b_1692_ = v___x_1708_;
goto _start;
}
else
{
lean_object* v___x_1765_; lean_object* v___x_1766_; uint8_t v___x_1767_; lean_object* v___x_1768_; 
v___x_1765_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg___closed__2, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg___closed__2);
lean_inc_ref(v___y_1733_);
lean_inc_ref(v___y_1745_);
v___x_1766_ = l_Lean_mkApp7(v___x_1765_, v___y_1745_, v___y_1733_, v_a_1728_, v_a_1730_, v___y_1741_, v___y_1737_, v_a_1759_);
v___x_1767_ = lean_unbox(v_a_1752_);
lean_dec(v_a_1752_);
v___x_1768_ = l_Lean_Meta_Grind_pushEqCore___redArg(v___y_1745_, v___y_1733_, v___x_1766_, v___x_1767_, v___y_1743_, v___y_1732_, v___y_1740_, v___y_1746_, v___y_1742_, v___y_1735_);
if (lean_obj_tag(v___x_1768_) == 0)
{
lean_dec_ref_known(v___x_1768_, 1);
v_as_x27_1691_ = v_tail_1707_;
v_b_1692_ = v___x_1708_;
goto _start;
}
else
{
return v___x_1768_;
}
}
}
else
{
lean_object* v_a_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1777_; 
lean_dec(v_a_1759_);
lean_dec(v_a_1752_);
lean_dec_ref(v___y_1745_);
lean_dec_ref(v___y_1741_);
lean_dec_ref(v___y_1737_);
lean_dec_ref(v___y_1733_);
lean_dec(v_a_1730_);
lean_dec(v_a_1728_);
v_a_1770_ = lean_ctor_get(v___x_1760_, 0);
v_isSharedCheck_1777_ = !lean_is_exclusive(v___x_1760_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1772_ = v___x_1760_;
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_a_1770_);
lean_dec(v___x_1760_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1775_; 
if (v_isShared_1773_ == 0)
{
v___x_1775_ = v___x_1772_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v_a_1770_);
v___x_1775_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
return v___x_1775_;
}
}
}
}
else
{
lean_object* v_a_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1785_; 
lean_dec(v_a_1752_);
lean_dec_ref(v___y_1745_);
lean_dec_ref(v___y_1741_);
lean_dec_ref(v___y_1737_);
lean_dec_ref(v___y_1733_);
lean_dec(v_a_1730_);
lean_dec(v_a_1728_);
v_a_1778_ = lean_ctor_get(v___x_1758_, 0);
v_isSharedCheck_1785_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1785_ == 0)
{
v___x_1780_ = v___x_1758_;
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_a_1778_);
lean_dec(v___x_1758_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v___x_1783_; 
if (v_isShared_1781_ == 0)
{
v___x_1783_ = v___x_1780_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v_a_1778_);
v___x_1783_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
return v___x_1783_;
}
}
}
}
else
{
lean_object* v_a_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1793_; 
lean_dec(v_a_1755_);
lean_dec(v_a_1752_);
lean_dec_ref(v___y_1745_);
lean_dec_ref(v___y_1741_);
lean_dec_ref(v___y_1737_);
lean_dec_ref(v___y_1733_);
lean_dec(v_a_1730_);
lean_dec(v_a_1728_);
v_a_1786_ = lean_ctor_get(v___x_1756_, 0);
v_isSharedCheck_1793_ = !lean_is_exclusive(v___x_1756_);
if (v_isSharedCheck_1793_ == 0)
{
v___x_1788_ = v___x_1756_;
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_a_1786_);
lean_dec(v___x_1756_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v___x_1791_; 
if (v_isShared_1789_ == 0)
{
v___x_1791_ = v___x_1788_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_a_1786_);
v___x_1791_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
return v___x_1791_;
}
}
}
}
else
{
lean_object* v_a_1794_; lean_object* v___x_1796_; uint8_t v_isShared_1797_; uint8_t v_isSharedCheck_1801_; 
lean_dec(v_a_1752_);
lean_dec_ref(v___y_1745_);
lean_dec_ref(v___y_1741_);
lean_dec_ref(v___y_1737_);
lean_dec_ref(v___y_1733_);
lean_dec(v_a_1730_);
lean_dec(v_a_1728_);
v_a_1794_ = lean_ctor_get(v___x_1754_, 0);
v_isSharedCheck_1801_ = !lean_is_exclusive(v___x_1754_);
if (v_isSharedCheck_1801_ == 0)
{
v___x_1796_ = v___x_1754_;
v_isShared_1797_ = v_isSharedCheck_1801_;
goto v_resetjp_1795_;
}
else
{
lean_inc(v_a_1794_);
lean_dec(v___x_1754_);
v___x_1796_ = lean_box(0);
v_isShared_1797_ = v_isSharedCheck_1801_;
goto v_resetjp_1795_;
}
v_resetjp_1795_:
{
lean_object* v___x_1799_; 
if (v_isShared_1797_ == 0)
{
v___x_1799_ = v___x_1796_;
goto v_reusejp_1798_;
}
else
{
lean_object* v_reuseFailAlloc_1800_; 
v_reuseFailAlloc_1800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1800_, 0, v_a_1794_);
v___x_1799_ = v_reuseFailAlloc_1800_;
goto v_reusejp_1798_;
}
v_reusejp_1798_:
{
return v___x_1799_;
}
}
}
}
else
{
lean_dec(v_a_1752_);
lean_dec_ref(v___y_1745_);
lean_dec_ref(v___y_1741_);
lean_dec_ref(v___y_1737_);
lean_dec_ref(v___y_1733_);
lean_dec(v_a_1730_);
lean_dec(v_a_1728_);
v_as_x27_1691_ = v_tail_1707_;
v_b_1692_ = v___x_1708_;
goto _start;
}
}
else
{
lean_object* v_a_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1810_; 
lean_dec_ref(v___y_1745_);
lean_dec_ref(v___y_1741_);
lean_dec_ref(v___y_1737_);
lean_dec_ref(v___y_1733_);
lean_dec(v_a_1730_);
lean_dec(v_a_1728_);
v_a_1803_ = lean_ctor_get(v___x_1751_, 0);
v_isSharedCheck_1810_ = !lean_is_exclusive(v___x_1751_);
if (v_isSharedCheck_1810_ == 0)
{
v___x_1805_ = v___x_1751_;
v_isShared_1806_ = v_isSharedCheck_1810_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_a_1803_);
lean_dec(v___x_1751_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1810_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v___x_1808_; 
if (v_isShared_1806_ == 0)
{
v___x_1808_ = v___x_1805_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v_a_1803_);
v___x_1808_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
return v___x_1808_;
}
}
}
}
}
else
{
lean_object* v_a_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1818_; 
lean_dec_ref(v___y_1745_);
lean_dec_ref(v___y_1741_);
lean_dec_ref(v___y_1737_);
lean_dec_ref(v___y_1733_);
lean_dec(v_a_1730_);
lean_dec(v_a_1728_);
v_a_1811_ = lean_ctor_get(v___y_1747_, 0);
v_isSharedCheck_1818_ = !lean_is_exclusive(v___y_1747_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1813_ = v___y_1747_;
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_a_1811_);
lean_dec(v___y_1747_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1816_; 
if (v_isShared_1814_ == 0)
{
v___x_1816_ = v___x_1813_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_a_1811_);
v___x_1816_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
return v___x_1816_;
}
}
}
}
v___jp_1819_:
{
lean_object* v___x_1831_; 
v___x_1831_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f___redArg(v_a_1728_, v___y_1821_, v___y_1829_);
if (lean_obj_tag(v___x_1831_) == 0)
{
lean_object* v_a_1832_; 
v_a_1832_ = lean_ctor_get(v___x_1831_, 0);
lean_inc(v_a_1832_);
lean_dec_ref_known(v___x_1831_, 1);
if (lean_obj_tag(v_a_1832_) == 1)
{
lean_object* v_val_1833_; lean_object* v_fst_1834_; lean_object* v_snd_1835_; lean_object* v___x_1836_; 
v_val_1833_ = lean_ctor_get(v_a_1832_, 0);
lean_inc(v_val_1833_);
lean_dec_ref_known(v_a_1832_, 1);
v_fst_1834_ = lean_ctor_get(v_val_1833_, 0);
lean_inc(v_fst_1834_);
v_snd_1835_ = lean_ctor_get(v_val_1833_, 1);
lean_inc(v_snd_1835_);
lean_dec(v_val_1833_);
v___x_1836_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f___redArg(v_a_1730_, v___y_1821_, v___y_1829_);
if (lean_obj_tag(v___x_1836_) == 0)
{
lean_object* v_a_1837_; 
v_a_1837_ = lean_ctor_get(v___x_1836_, 0);
lean_inc(v_a_1837_);
lean_dec_ref_known(v___x_1836_, 1);
if (lean_obj_tag(v_a_1837_) == 1)
{
lean_object* v_val_1838_; lean_object* v_fst_1839_; lean_object* v_snd_1840_; lean_object* v___x_1841_; 
v_val_1838_ = lean_ctor_get(v_a_1837_, 0);
lean_inc(v_val_1838_);
lean_dec_ref_known(v_a_1837_, 1);
v_fst_1839_ = lean_ctor_get(v_val_1838_, 0);
lean_inc(v_fst_1839_);
v_snd_1840_ = lean_ctor_get(v_val_1838_, 1);
lean_inc(v_snd_1840_);
lean_dec(v_val_1838_);
v___x_1841_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_fst_1834_, v___y_1821_);
if (lean_obj_tag(v___x_1841_) == 0)
{
lean_object* v_a_1842_; uint8_t v___x_1843_; 
v_a_1842_ = lean_ctor_get(v___x_1841_, 0);
v___x_1843_ = lean_unbox(v_a_1842_);
if (v___x_1843_ == 0)
{
v___y_1732_ = v___y_1823_;
v___y_1733_ = v_fst_1839_;
v___y_1734_ = v___y_1824_;
v___y_1735_ = v___y_1830_;
v___y_1736_ = v___y_1820_;
v___y_1737_ = v_snd_1840_;
v___y_1738_ = v___y_1825_;
v___y_1739_ = v___y_1826_;
v___y_1740_ = v___y_1827_;
v___y_1741_ = v_snd_1835_;
v___y_1742_ = v___y_1829_;
v___y_1743_ = v___y_1821_;
v___y_1744_ = v___y_1822_;
v___y_1745_ = v_fst_1834_;
v___y_1746_ = v___y_1828_;
v___y_1747_ = v___x_1841_;
goto v___jp_1731_;
}
else
{
lean_object* v___x_1844_; 
lean_dec_ref_known(v___x_1841_, 1);
v___x_1844_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_fst_1839_, v___y_1821_);
v___y_1732_ = v___y_1823_;
v___y_1733_ = v_fst_1839_;
v___y_1734_ = v___y_1824_;
v___y_1735_ = v___y_1830_;
v___y_1736_ = v___y_1820_;
v___y_1737_ = v_snd_1840_;
v___y_1738_ = v___y_1825_;
v___y_1739_ = v___y_1826_;
v___y_1740_ = v___y_1827_;
v___y_1741_ = v_snd_1835_;
v___y_1742_ = v___y_1829_;
v___y_1743_ = v___y_1821_;
v___y_1744_ = v___y_1822_;
v___y_1745_ = v_fst_1834_;
v___y_1746_ = v___y_1828_;
v___y_1747_ = v___x_1844_;
goto v___jp_1731_;
}
}
else
{
v___y_1732_ = v___y_1823_;
v___y_1733_ = v_fst_1839_;
v___y_1734_ = v___y_1824_;
v___y_1735_ = v___y_1830_;
v___y_1736_ = v___y_1820_;
v___y_1737_ = v_snd_1840_;
v___y_1738_ = v___y_1825_;
v___y_1739_ = v___y_1826_;
v___y_1740_ = v___y_1827_;
v___y_1741_ = v_snd_1835_;
v___y_1742_ = v___y_1829_;
v___y_1743_ = v___y_1821_;
v___y_1744_ = v___y_1822_;
v___y_1745_ = v_fst_1834_;
v___y_1746_ = v___y_1828_;
v___y_1747_ = v___x_1841_;
goto v___jp_1731_;
}
}
else
{
lean_dec(v_a_1837_);
lean_dec(v_snd_1835_);
lean_dec(v_fst_1834_);
lean_dec(v_a_1730_);
lean_dec(v_a_1728_);
v_as_x27_1691_ = v_tail_1707_;
v_b_1692_ = v___x_1708_;
goto _start;
}
}
else
{
lean_object* v_a_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1853_; 
lean_dec(v_snd_1835_);
lean_dec(v_fst_1834_);
lean_dec(v_a_1730_);
lean_dec(v_a_1728_);
v_a_1846_ = lean_ctor_get(v___x_1836_, 0);
v_isSharedCheck_1853_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1853_ == 0)
{
v___x_1848_ = v___x_1836_;
v_isShared_1849_ = v_isSharedCheck_1853_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_a_1846_);
lean_dec(v___x_1836_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1853_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v___x_1851_; 
if (v_isShared_1849_ == 0)
{
v___x_1851_ = v___x_1848_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v_a_1846_);
v___x_1851_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
return v___x_1851_;
}
}
}
}
else
{
lean_dec(v_a_1832_);
lean_dec(v_a_1730_);
lean_dec(v_a_1728_);
v_as_x27_1691_ = v_tail_1707_;
v_b_1692_ = v___x_1708_;
goto _start;
}
}
else
{
lean_object* v_a_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1862_; 
lean_dec(v_a_1730_);
lean_dec(v_a_1728_);
v_a_1855_ = lean_ctor_get(v___x_1831_, 0);
v_isSharedCheck_1862_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1857_ = v___x_1831_;
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
else
{
lean_inc(v_a_1855_);
lean_dec(v___x_1831_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v___x_1860_; 
if (v_isShared_1858_ == 0)
{
v___x_1860_ = v___x_1857_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v_a_1855_);
v___x_1860_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
return v___x_1860_;
}
}
}
}
v___jp_1863_:
{
if (lean_obj_tag(v___y_1864_) == 0)
{
lean_object* v_a_1865_; uint8_t v___x_1866_; 
v_a_1865_ = lean_ctor_get(v___y_1864_, 0);
lean_inc(v_a_1865_);
lean_dec_ref_known(v___y_1864_, 1);
v___x_1866_ = lean_unbox(v_a_1865_);
lean_dec(v_a_1865_);
if (v___x_1866_ == 0)
{
v___y_1820_ = v___y_1693_;
v___y_1821_ = v___y_1694_;
v___y_1822_ = v___y_1695_;
v___y_1823_ = v___y_1696_;
v___y_1824_ = v___y_1697_;
v___y_1825_ = v___y_1698_;
v___y_1826_ = v___y_1699_;
v___y_1827_ = v___y_1700_;
v___y_1828_ = v___y_1701_;
v___y_1829_ = v___y_1702_;
v___y_1830_ = v___y_1703_;
goto v___jp_1819_;
}
else
{
lean_object* v___x_1867_; 
v___x_1867_ = l_Lean_Meta_Grind_isEqv___redArg(v_a_1728_, v_a_1730_, v___y_1694_);
if (lean_obj_tag(v___x_1867_) == 0)
{
lean_object* v_a_1868_; uint8_t v___x_1869_; 
v_a_1868_ = lean_ctor_get(v___x_1867_, 0);
lean_inc(v_a_1868_);
lean_dec_ref_known(v___x_1867_, 1);
v___x_1869_ = lean_unbox(v_a_1868_);
if (v___x_1869_ == 0)
{
lean_object* v___x_1870_; 
v___x_1870_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath(v_u_1725_, v_v_1726_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
if (lean_obj_tag(v___x_1870_) == 0)
{
lean_object* v_a_1871_; lean_object* v___x_1872_; 
v_a_1871_ = lean_ctor_get(v___x_1870_, 0);
lean_inc(v_a_1871_);
lean_dec_ref_known(v___x_1870_, 1);
v___x_1872_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath(v_v_1726_, v_u_1725_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
if (lean_obj_tag(v___x_1872_) == 0)
{
lean_object* v_a_1873_; lean_object* v___x_1874_; 
v_a_1873_ = lean_ctor_get(v___x_1872_, 0);
lean_inc(v_a_1873_);
lean_dec_ref_known(v___x_1872_, 1);
lean_inc(v_a_1730_);
lean_inc(v_a_1728_);
v___x_1874_ = l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLe(v_a_1728_, v_a_1730_, v_a_1871_, v_a_1873_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
if (lean_obj_tag(v___x_1874_) == 0)
{
lean_object* v_a_1875_; uint8_t v___x_1876_; lean_object* v___x_1877_; 
v_a_1875_ = lean_ctor_get(v___x_1874_, 0);
lean_inc(v_a_1875_);
lean_dec_ref_known(v___x_1874_, 1);
v___x_1876_ = lean_unbox(v_a_1868_);
lean_dec(v_a_1868_);
lean_inc(v_a_1730_);
lean_inc(v_a_1728_);
v___x_1877_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_a_1728_, v_a_1730_, v_a_1875_, v___x_1876_, v___y_1694_, v___y_1696_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
if (lean_obj_tag(v___x_1877_) == 0)
{
lean_dec_ref_known(v___x_1877_, 1);
v___y_1820_ = v___y_1693_;
v___y_1821_ = v___y_1694_;
v___y_1822_ = v___y_1695_;
v___y_1823_ = v___y_1696_;
v___y_1824_ = v___y_1697_;
v___y_1825_ = v___y_1698_;
v___y_1826_ = v___y_1699_;
v___y_1827_ = v___y_1700_;
v___y_1828_ = v___y_1701_;
v___y_1829_ = v___y_1702_;
v___y_1830_ = v___y_1703_;
goto v___jp_1819_;
}
else
{
lean_dec(v_a_1730_);
lean_dec(v_a_1728_);
return v___x_1877_;
}
}
else
{
lean_object* v_a_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1885_; 
lean_dec(v_a_1868_);
lean_dec(v_a_1730_);
lean_dec(v_a_1728_);
v_a_1878_ = lean_ctor_get(v___x_1874_, 0);
v_isSharedCheck_1885_ = !lean_is_exclusive(v___x_1874_);
if (v_isSharedCheck_1885_ == 0)
{
v___x_1880_ = v___x_1874_;
v_isShared_1881_ = v_isSharedCheck_1885_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_a_1878_);
lean_dec(v___x_1874_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1885_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v___x_1883_; 
if (v_isShared_1881_ == 0)
{
v___x_1883_ = v___x_1880_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v_a_1878_);
v___x_1883_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
return v___x_1883_;
}
}
}
}
else
{
lean_object* v_a_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1893_; 
lean_dec(v_a_1871_);
lean_dec(v_a_1868_);
lean_dec(v_a_1730_);
lean_dec(v_a_1728_);
v_a_1886_ = lean_ctor_get(v___x_1872_, 0);
v_isSharedCheck_1893_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1888_ = v___x_1872_;
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_a_1886_);
lean_dec(v___x_1872_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v___x_1891_; 
if (v_isShared_1889_ == 0)
{
v___x_1891_ = v___x_1888_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_a_1886_);
v___x_1891_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
return v___x_1891_;
}
}
}
}
else
{
lean_object* v_a_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1901_; 
lean_dec(v_a_1868_);
lean_dec(v_a_1730_);
lean_dec(v_a_1728_);
v_a_1894_ = lean_ctor_get(v___x_1870_, 0);
v_isSharedCheck_1901_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1896_ = v___x_1870_;
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_a_1894_);
lean_dec(v___x_1870_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1899_; 
if (v_isShared_1897_ == 0)
{
v___x_1899_ = v___x_1896_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v_a_1894_);
v___x_1899_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
return v___x_1899_;
}
}
}
}
else
{
lean_dec(v_a_1868_);
v___y_1820_ = v___y_1693_;
v___y_1821_ = v___y_1694_;
v___y_1822_ = v___y_1695_;
v___y_1823_ = v___y_1696_;
v___y_1824_ = v___y_1697_;
v___y_1825_ = v___y_1698_;
v___y_1826_ = v___y_1699_;
v___y_1827_ = v___y_1700_;
v___y_1828_ = v___y_1701_;
v___y_1829_ = v___y_1702_;
v___y_1830_ = v___y_1703_;
goto v___jp_1819_;
}
}
else
{
lean_object* v_a_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1909_; 
lean_dec(v_a_1730_);
lean_dec(v_a_1728_);
v_a_1902_ = lean_ctor_get(v___x_1867_, 0);
v_isSharedCheck_1909_ = !lean_is_exclusive(v___x_1867_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1904_ = v___x_1867_;
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_a_1902_);
lean_dec(v___x_1867_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
lean_object* v___x_1907_; 
if (v_isShared_1905_ == 0)
{
v___x_1907_ = v___x_1904_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v_a_1902_);
v___x_1907_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
return v___x_1907_;
}
}
}
}
}
else
{
lean_object* v_a_1910_; lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_1917_; 
lean_dec(v_a_1730_);
lean_dec(v_a_1728_);
v_a_1910_ = lean_ctor_get(v___y_1864_, 0);
v_isSharedCheck_1917_ = !lean_is_exclusive(v___y_1864_);
if (v_isSharedCheck_1917_ == 0)
{
v___x_1912_ = v___y_1864_;
v_isShared_1913_ = v_isSharedCheck_1917_;
goto v_resetjp_1911_;
}
else
{
lean_inc(v_a_1910_);
lean_dec(v___y_1864_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_1917_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
lean_object* v___x_1915_; 
if (v_isShared_1913_ == 0)
{
v___x_1915_ = v___x_1912_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v_a_1910_);
v___x_1915_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
return v___x_1915_;
}
}
}
}
}
else
{
lean_object* v_a_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1929_; 
lean_dec(v_a_1728_);
v_a_1922_ = lean_ctor_get(v___x_1729_, 0);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1729_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1924_ = v___x_1729_;
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_a_1922_);
lean_dec(v___x_1729_);
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
v_a_1930_ = lean_ctor_get(v___x_1727_, 0);
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1727_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1932_ = v___x_1727_;
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_a_1930_);
lean_dec(v___x_1727_);
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
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg___boxed(lean_object* v_as_x27_1938_, lean_object* v_b_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_){
_start:
{
lean_object* v_res_1952_; 
v_res_1952_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg(v_as_x27_1938_, v_b_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
lean_dec(v___y_1950_);
lean_dec_ref(v___y_1949_);
lean_dec(v___y_1948_);
lean_dec_ref(v___y_1947_);
lean_dec(v___y_1946_);
lean_dec_ref(v___y_1945_);
lean_dec(v___y_1944_);
lean_dec_ref(v___y_1943_);
lean_dec(v___y_1942_);
lean_dec(v___y_1941_);
lean_dec(v___y_1940_);
lean_dec(v_as_x27_1938_);
return v_res_1952_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending(lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_){
_start:
{
lean_object* v___f_1966_; lean_object* v___x_1967_; 
v___f_1966_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending___closed__0));
v___x_1967_ = l_Lean_Meta_Grind_Order_getStruct___redArg(v_a_1954_, v_a_1955_, v_a_1963_);
if (lean_obj_tag(v___x_1967_) == 0)
{
lean_object* v_a_1968_; lean_object* v_propagate_1969_; lean_object* v___x_1970_; 
v_a_1968_ = lean_ctor_get(v___x_1967_, 0);
lean_inc(v_a_1968_);
lean_dec_ref_known(v___x_1967_, 1);
v_propagate_1969_ = lean_ctor_get(v_a_1968_, 8);
lean_inc(v_propagate_1969_);
lean_dec(v_a_1968_);
v___x_1970_ = l_Lean_Meta_Grind_Order_modifyStruct___redArg(v___f_1966_, v_a_1954_, v_a_1955_);
if (lean_obj_tag(v___x_1970_) == 0)
{
lean_object* v___x_1971_; lean_object* v___x_1972_; 
lean_dec_ref_known(v___x_1970_, 1);
v___x_1971_ = lean_box(0);
v___x_1972_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg(v_propagate_1969_, v___x_1971_, v_a_1954_, v_a_1955_, v_a_1956_, v_a_1957_, v_a_1958_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_);
lean_dec(v_propagate_1969_);
if (lean_obj_tag(v___x_1972_) == 0)
{
lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_1979_; 
v_isSharedCheck_1979_ = !lean_is_exclusive(v___x_1972_);
if (v_isSharedCheck_1979_ == 0)
{
lean_object* v_unused_1980_; 
v_unused_1980_ = lean_ctor_get(v___x_1972_, 0);
lean_dec(v_unused_1980_);
v___x_1974_ = v___x_1972_;
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
else
{
lean_dec(v___x_1972_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
lean_object* v___x_1977_; 
if (v_isShared_1975_ == 0)
{
lean_ctor_set(v___x_1974_, 0, v___x_1971_);
v___x_1977_ = v___x_1974_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v___x_1971_);
v___x_1977_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
return v___x_1977_;
}
}
}
else
{
return v___x_1972_;
}
}
else
{
lean_dec(v_propagate_1969_);
return v___x_1970_;
}
}
else
{
lean_object* v_a_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_1988_; 
v_a_1981_ = lean_ctor_get(v___x_1967_, 0);
v_isSharedCheck_1988_ = !lean_is_exclusive(v___x_1967_);
if (v_isSharedCheck_1988_ == 0)
{
v___x_1983_ = v___x_1967_;
v_isShared_1984_ = v_isSharedCheck_1988_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_a_1981_);
lean_dec(v___x_1967_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending___boxed(lean_object* v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_, lean_object* v_a_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_){
_start:
{
lean_object* v_res_2001_; 
v_res_2001_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending(v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_, v_a_1997_, v_a_1998_, v_a_1999_);
lean_dec(v_a_1999_);
lean_dec_ref(v_a_1998_);
lean_dec(v_a_1997_);
lean_dec_ref(v_a_1996_);
lean_dec(v_a_1995_);
lean_dec_ref(v_a_1994_);
lean_dec(v_a_1993_);
lean_dec_ref(v_a_1992_);
lean_dec(v_a_1991_);
lean_dec(v_a_1990_);
lean_dec(v_a_1989_);
return v_res_2001_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0(lean_object* v_as_2002_, lean_object* v_as_x27_2003_, lean_object* v_b_2004_, lean_object* v_a_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_){
_start:
{
lean_object* v___x_2018_; 
v___x_2018_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg(v_as_x27_2003_, v_b_2004_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_);
return v___x_2018_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___boxed(lean_object* v_as_2019_, lean_object* v_as_x27_2020_, lean_object* v_b_2021_, lean_object* v_a_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_){
_start:
{
lean_object* v_res_2035_; 
v_res_2035_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0(v_as_2019_, v_as_x27_2020_, v_b_2021_, v_a_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_);
lean_dec(v___y_2033_);
lean_dec_ref(v___y_2032_);
lean_dec(v___y_2031_);
lean_dec_ref(v___y_2030_);
lean_dec(v___y_2029_);
lean_dec_ref(v___y_2028_);
lean_dec(v___y_2027_);
lean_dec_ref(v___y_2026_);
lean_dec(v___y_2025_);
lean_dec(v___y_2024_);
lean_dec(v___y_2023_);
lean_dec(v_as_x27_2020_);
lean_dec(v_as_2019_);
return v_res_2035_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue___redArg(lean_object* v_e_2036_, lean_object* v_a_2037_, lean_object* v_a_2038_, lean_object* v_a_2039_, lean_object* v_a_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_){
_start:
{
lean_object* v___x_2044_; 
v___x_2044_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_2037_, v_a_2041_);
if (lean_obj_tag(v___x_2044_) == 0)
{
lean_object* v_a_2045_; lean_object* v_termMapInv_2046_; lean_object* v___x_2047_; 
v_a_2045_ = lean_ctor_get(v___x_2044_, 0);
lean_inc(v_a_2045_);
lean_dec_ref_known(v___x_2044_, 1);
v_termMapInv_2046_ = lean_ctor_get(v_a_2045_, 4);
lean_inc_ref(v_termMapInv_2046_);
lean_dec(v_a_2045_);
v___x_2047_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMapInv_2046_, v_e_2036_);
lean_dec_ref(v_termMapInv_2046_);
if (lean_obj_tag(v___x_2047_) == 1)
{
lean_object* v_val_2048_; lean_object* v_fst_2049_; lean_object* v___x_2050_; 
lean_dec_ref(v_e_2036_);
v_val_2048_ = lean_ctor_get(v___x_2047_, 0);
lean_inc(v_val_2048_);
lean_dec_ref_known(v___x_2047_, 1);
v_fst_2049_ = lean_ctor_get(v_val_2048_, 0);
lean_inc(v_fst_2049_);
lean_dec(v_val_2048_);
v___x_2050_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_fst_2049_, v_a_2037_);
if (lean_obj_tag(v___x_2050_) == 0)
{
lean_object* v_a_2051_; uint8_t v___x_2052_; 
v_a_2051_ = lean_ctor_get(v___x_2050_, 0);
v___x_2052_ = lean_unbox(v_a_2051_);
if (v___x_2052_ == 0)
{
lean_dec(v_fst_2049_);
return v___x_2050_;
}
else
{
lean_object* v___x_2053_; 
lean_dec_ref_known(v___x_2050_, 1);
v___x_2053_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_fst_2049_, v_a_2037_, v_a_2038_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_);
return v___x_2053_;
}
}
else
{
lean_dec(v_fst_2049_);
return v___x_2050_;
}
}
else
{
lean_object* v___x_2054_; 
lean_dec(v___x_2047_);
v___x_2054_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_e_2036_, v_a_2037_);
if (lean_obj_tag(v___x_2054_) == 0)
{
lean_object* v_a_2055_; uint8_t v___x_2056_; 
v_a_2055_ = lean_ctor_get(v___x_2054_, 0);
v___x_2056_ = lean_unbox(v_a_2055_);
if (v___x_2056_ == 0)
{
lean_dec_ref(v_e_2036_);
return v___x_2054_;
}
else
{
lean_object* v___x_2057_; 
lean_dec_ref_known(v___x_2054_, 1);
v___x_2057_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_2036_, v_a_2037_, v_a_2038_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_);
return v___x_2057_;
}
}
else
{
lean_dec_ref(v_e_2036_);
return v___x_2054_;
}
}
}
else
{
lean_object* v_a_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2065_; 
lean_dec_ref(v_e_2036_);
v_a_2058_ = lean_ctor_get(v___x_2044_, 0);
v_isSharedCheck_2065_ = !lean_is_exclusive(v___x_2044_);
if (v_isSharedCheck_2065_ == 0)
{
v___x_2060_ = v___x_2044_;
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_a_2058_);
lean_dec(v___x_2044_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v___x_2063_; 
if (v_isShared_2061_ == 0)
{
v___x_2063_ = v___x_2060_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v_a_2058_);
v___x_2063_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
return v___x_2063_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue___redArg___boxed(lean_object* v_e_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_, lean_object* v_a_2073_){
_start:
{
lean_object* v_res_2074_; 
v_res_2074_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue___redArg(v_e_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_);
lean_dec(v_a_2072_);
lean_dec_ref(v_a_2071_);
lean_dec(v_a_2070_);
lean_dec_ref(v_a_2069_);
lean_dec_ref(v_a_2068_);
lean_dec(v_a_2067_);
return v_res_2074_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue(lean_object* v_e_2075_, lean_object* v_a_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_){
_start:
{
lean_object* v___x_2088_; 
v___x_2088_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue___redArg(v_e_2075_, v_a_2077_, v_a_2081_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_);
return v___x_2088_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue___boxed(lean_object* v_e_2089_, lean_object* v_a_2090_, lean_object* v_a_2091_, lean_object* v_a_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_){
_start:
{
lean_object* v_res_2102_; 
v_res_2102_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue(v_e_2089_, v_a_2090_, v_a_2091_, v_a_2092_, v_a_2093_, v_a_2094_, v_a_2095_, v_a_2096_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_);
lean_dec(v_a_2100_);
lean_dec_ref(v_a_2099_);
lean_dec(v_a_2098_);
lean_dec_ref(v_a_2097_);
lean_dec(v_a_2096_);
lean_dec_ref(v_a_2095_);
lean_dec(v_a_2094_);
lean_dec_ref(v_a_2093_);
lean_dec(v_a_2092_);
lean_dec(v_a_2091_);
lean_dec(v_a_2090_);
return v_res_2102_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__2(void){
_start:
{
lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; 
v___x_2109_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__1));
v___x_2110_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__6));
v___x_2111_ = l_Lean_Name_append(v___x_2110_, v___x_2109_);
return v___x_2111_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4(void){
_start:
{
lean_object* v___x_2113_; lean_object* v___x_2114_; 
v___x_2113_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__3));
v___x_2114_ = l_Lean_stringToMessageData(v___x_2113_);
return v___x_2114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue(lean_object* v_u_2116_, lean_object* v_v_2117_, lean_object* v_k_2118_, lean_object* v_c_2119_, lean_object* v_e_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_){
_start:
{
lean_object* v___x_2133_; 
lean_inc_ref(v_e_2120_);
v___x_2133_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue___redArg(v_e_2120_, v_a_2122_, v_a_2126_, v_a_2128_, v_a_2129_, v_a_2130_, v_a_2131_);
if (lean_obj_tag(v___x_2133_) == 0)
{
lean_object* v_a_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2233_; 
v_a_2134_ = lean_ctor_get(v___x_2133_, 0);
v_isSharedCheck_2233_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2233_ == 0)
{
v___x_2136_ = v___x_2133_;
v_isShared_2137_ = v_isSharedCheck_2233_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_a_2134_);
lean_dec(v___x_2133_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2233_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
uint8_t v___x_2138_; 
v___x_2138_ = lean_unbox(v_a_2134_);
lean_dec(v_a_2134_);
if (v___x_2138_ == 0)
{
lean_object* v_toCold_2139_; lean_object* v_options_2140_; lean_object* v_inheritedTraceOptions_2141_; uint8_t v_hasTrace_2142_; lean_object* v___x_2143_; lean_object* v___y_2145_; lean_object* v___y_2146_; lean_object* v___y_2147_; lean_object* v___y_2148_; lean_object* v___y_2149_; lean_object* v___y_2150_; lean_object* v___y_2151_; lean_object* v___y_2152_; lean_object* v___y_2153_; lean_object* v___y_2154_; lean_object* v___y_2155_; 
v_toCold_2139_ = lean_ctor_get(v_a_2130_, 0);
v_options_2140_ = lean_ctor_get(v_toCold_2139_, 2);
v_inheritedTraceOptions_2141_ = lean_ctor_get(v_toCold_2139_, 11);
v_hasTrace_2142_ = lean_ctor_get_uint8(v_options_2140_, sizeof(void*)*1);
v___x_2143_ = l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(v_c_2119_);
if (v_hasTrace_2142_ == 0)
{
v___y_2145_ = v_a_2121_;
v___y_2146_ = v_a_2122_;
v___y_2147_ = v_a_2123_;
v___y_2148_ = v_a_2124_;
v___y_2149_ = v_a_2125_;
v___y_2150_ = v_a_2126_;
v___y_2151_ = v_a_2127_;
v___y_2152_ = v_a_2128_;
v___y_2153_ = v_a_2129_;
v___y_2154_ = v_a_2130_;
v___y_2155_ = v_a_2131_;
goto v___jp_2144_;
}
else
{
lean_object* v___x_2163_; lean_object* v___x_2164_; uint8_t v___x_2165_; 
v___x_2163_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__1));
v___x_2164_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__2, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__2);
v___x_2165_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2141_, v_options_2140_, v___x_2164_);
if (v___x_2165_ == 0)
{
v___y_2145_ = v_a_2121_;
v___y_2146_ = v_a_2122_;
v___y_2147_ = v_a_2123_;
v___y_2148_ = v_a_2124_;
v___y_2149_ = v_a_2125_;
v___y_2150_ = v_a_2126_;
v___y_2151_ = v_a_2127_;
v___y_2152_ = v_a_2128_;
v___y_2153_ = v_a_2129_;
v___y_2154_ = v_a_2130_;
v___y_2155_ = v_a_2131_;
goto v___jp_2144_;
}
else
{
lean_object* v___x_2166_; 
v___x_2166_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_u_2116_, v_a_2121_, v_a_2122_, v_a_2130_);
if (lean_obj_tag(v___x_2166_) == 0)
{
lean_object* v_a_2167_; lean_object* v___x_2168_; 
v_a_2167_ = lean_ctor_get(v___x_2166_, 0);
lean_inc(v_a_2167_);
lean_dec_ref_known(v___x_2166_, 1);
v___x_2168_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_v_2117_, v_a_2121_, v_a_2122_, v_a_2130_);
if (lean_obj_tag(v___x_2168_) == 0)
{
lean_object* v_a_2169_; lean_object* v___x_2170_; 
v_a_2169_ = lean_ctor_get(v___x_2168_, 0);
lean_inc(v_a_2169_);
lean_dec_ref_known(v___x_2168_, 1);
v___x_2170_ = l_Lean_Meta_Grind_Order_Cnstr_pp___redArg(v_c_2119_, v_a_2121_, v_a_2122_, v_a_2130_);
if (lean_obj_tag(v___x_2170_) == 0)
{
lean_object* v_a_2171_; lean_object* v_k_2172_; uint8_t v_strict_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___y_2177_; lean_object* v___y_2178_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___y_2190_; 
v_a_2171_ = lean_ctor_get(v___x_2170_, 0);
lean_inc(v_a_2171_);
lean_dec_ref_known(v___x_2170_, 1);
v_k_2172_ = lean_ctor_get(v_k_2118_, 0);
v_strict_2173_ = lean_ctor_get_uint8(v_k_2118_, sizeof(void*)*1);
v___x_2174_ = l_Lean_MessageData_ofExpr(v_a_2167_);
v___x_2175_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4);
v___x_2185_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2185_, 0, v___x_2174_);
lean_ctor_set(v___x_2185_, 1, v___x_2175_);
v___x_2186_ = l_Lean_MessageData_ofExpr(v_a_2169_);
v___x_2187_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2187_, 0, v___x_2185_);
lean_ctor_set(v___x_2187_, 1, v___x_2186_);
v___x_2188_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2188_, 0, v___x_2187_);
lean_ctor_set(v___x_2188_, 1, v___x_2175_);
if (v_strict_2173_ == 0)
{
lean_object* v___x_2201_; 
v___x_2201_ = l_Int_repr(v_k_2172_);
v___y_2190_ = v___x_2201_;
goto v___jp_2189_;
}
else
{
lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; 
v___x_2202_ = l_Int_repr(v_k_2172_);
v___x_2203_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5));
v___x_2204_ = lean_string_append(v___x_2202_, v___x_2203_);
v___y_2190_ = v___x_2204_;
goto v___jp_2189_;
}
v___jp_2176_:
{
lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; 
v___x_2179_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2179_, 0, v___y_2178_);
v___x_2180_ = l_Lean_MessageData_ofFormat(v___x_2179_);
v___x_2181_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2181_, 0, v___y_2177_);
lean_ctor_set(v___x_2181_, 1, v___x_2180_);
v___x_2182_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2182_, 0, v___x_2181_);
lean_ctor_set(v___x_2182_, 1, v___x_2175_);
v___x_2183_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2183_, 0, v___x_2182_);
lean_ctor_set(v___x_2183_, 1, v_a_2171_);
v___x_2184_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(v___x_2163_, v___x_2183_, v_a_2128_, v_a_2129_, v_a_2130_, v_a_2131_);
if (lean_obj_tag(v___x_2184_) == 0)
{
lean_dec_ref_known(v___x_2184_, 1);
v___y_2145_ = v_a_2121_;
v___y_2146_ = v_a_2122_;
v___y_2147_ = v_a_2123_;
v___y_2148_ = v_a_2124_;
v___y_2149_ = v_a_2125_;
v___y_2150_ = v_a_2126_;
v___y_2151_ = v_a_2127_;
v___y_2152_ = v_a_2128_;
v___y_2153_ = v_a_2129_;
v___y_2154_ = v_a_2130_;
v___y_2155_ = v_a_2131_;
goto v___jp_2144_;
}
else
{
lean_dec_ref(v___x_2143_);
lean_del_object(v___x_2136_);
lean_dec_ref(v_e_2120_);
lean_dec_ref(v_c_2119_);
lean_dec_ref(v_k_2118_);
lean_dec(v_v_2117_);
lean_dec(v_u_2116_);
return v___x_2184_;
}
}
v___jp_2189_:
{
lean_object* v_k_2191_; uint8_t v_strict_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; 
v_k_2191_ = lean_ctor_get(v___x_2143_, 0);
v_strict_2192_ = lean_ctor_get_uint8(v___x_2143_, sizeof(void*)*1);
v___x_2193_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2193_, 0, v___y_2190_);
v___x_2194_ = l_Lean_MessageData_ofFormat(v___x_2193_);
v___x_2195_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2195_, 0, v___x_2188_);
lean_ctor_set(v___x_2195_, 1, v___x_2194_);
v___x_2196_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2196_, 0, v___x_2195_);
lean_ctor_set(v___x_2196_, 1, v___x_2175_);
if (v_strict_2192_ == 0)
{
lean_object* v___x_2197_; 
v___x_2197_ = l_Int_repr(v_k_2191_);
v___y_2177_ = v___x_2196_;
v___y_2178_ = v___x_2197_;
goto v___jp_2176_;
}
else
{
lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; 
v___x_2198_ = l_Int_repr(v_k_2191_);
v___x_2199_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5));
v___x_2200_ = lean_string_append(v___x_2198_, v___x_2199_);
v___y_2177_ = v___x_2196_;
v___y_2178_ = v___x_2200_;
goto v___jp_2176_;
}
}
}
else
{
lean_object* v_a_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2212_; 
lean_dec(v_a_2169_);
lean_dec(v_a_2167_);
lean_dec_ref(v___x_2143_);
lean_del_object(v___x_2136_);
lean_dec_ref(v_e_2120_);
lean_dec_ref(v_c_2119_);
lean_dec_ref(v_k_2118_);
lean_dec(v_v_2117_);
lean_dec(v_u_2116_);
v_a_2205_ = lean_ctor_get(v___x_2170_, 0);
v_isSharedCheck_2212_ = !lean_is_exclusive(v___x_2170_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2207_ = v___x_2170_;
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_a_2205_);
lean_dec(v___x_2170_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v___x_2210_; 
if (v_isShared_2208_ == 0)
{
v___x_2210_ = v___x_2207_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v_a_2205_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
}
}
else
{
lean_object* v_a_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2220_; 
lean_dec(v_a_2167_);
lean_dec_ref(v___x_2143_);
lean_del_object(v___x_2136_);
lean_dec_ref(v_e_2120_);
lean_dec_ref(v_c_2119_);
lean_dec_ref(v_k_2118_);
lean_dec(v_v_2117_);
lean_dec(v_u_2116_);
v_a_2213_ = lean_ctor_get(v___x_2168_, 0);
v_isSharedCheck_2220_ = !lean_is_exclusive(v___x_2168_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_2215_ = v___x_2168_;
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_a_2213_);
lean_dec(v___x_2168_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v___x_2218_; 
if (v_isShared_2216_ == 0)
{
v___x_2218_ = v___x_2215_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v_a_2213_);
v___x_2218_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
return v___x_2218_;
}
}
}
}
else
{
lean_object* v_a_2221_; lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2228_; 
lean_dec_ref(v___x_2143_);
lean_del_object(v___x_2136_);
lean_dec_ref(v_e_2120_);
lean_dec_ref(v_c_2119_);
lean_dec_ref(v_k_2118_);
lean_dec(v_v_2117_);
lean_dec(v_u_2116_);
v_a_2221_ = lean_ctor_get(v___x_2166_, 0);
v_isSharedCheck_2228_ = !lean_is_exclusive(v___x_2166_);
if (v_isSharedCheck_2228_ == 0)
{
v___x_2223_ = v___x_2166_;
v_isShared_2224_ = v_isSharedCheck_2228_;
goto v_resetjp_2222_;
}
else
{
lean_inc(v_a_2221_);
lean_dec(v___x_2166_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2228_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
lean_object* v___x_2226_; 
if (v_isShared_2224_ == 0)
{
v___x_2226_ = v___x_2223_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v_a_2221_);
v___x_2226_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
return v___x_2226_;
}
}
}
}
}
v___jp_2144_:
{
uint8_t v___x_2156_; 
v___x_2156_ = l_Lean_Meta_Grind_Order_instDecidableLEWeight(v_k_2118_, v___x_2143_);
if (v___x_2156_ == 0)
{
lean_object* v___x_2157_; lean_object* v___x_2159_; 
lean_dec_ref(v___x_2143_);
lean_dec_ref(v_e_2120_);
lean_dec_ref(v_c_2119_);
lean_dec_ref(v_k_2118_);
lean_dec(v_v_2117_);
lean_dec(v_u_2116_);
v___x_2157_ = lean_box(0);
if (v_isShared_2137_ == 0)
{
lean_ctor_set(v___x_2136_, 0, v___x_2157_);
v___x_2159_ = v___x_2136_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v___x_2157_);
v___x_2159_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
return v___x_2159_;
}
}
else
{
lean_object* v___x_2161_; lean_object* v___x_2162_; 
lean_del_object(v___x_2136_);
v___x_2161_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2161_, 0, v_c_2119_);
lean_ctor_set(v___x_2161_, 1, v_e_2120_);
lean_ctor_set(v___x_2161_, 2, v_u_2116_);
lean_ctor_set(v___x_2161_, 3, v_v_2117_);
lean_ctor_set(v___x_2161_, 4, v_k_2118_);
lean_ctor_set(v___x_2161_, 5, v___x_2143_);
v___x_2162_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate(v___x_2161_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_);
return v___x_2162_;
}
}
}
else
{
lean_object* v___x_2229_; lean_object* v___x_2231_; 
lean_dec_ref(v_e_2120_);
lean_dec_ref(v_c_2119_);
lean_dec_ref(v_k_2118_);
lean_dec(v_v_2117_);
lean_dec(v_u_2116_);
v___x_2229_ = lean_box(0);
if (v_isShared_2137_ == 0)
{
lean_ctor_set(v___x_2136_, 0, v___x_2229_);
v___x_2231_ = v___x_2136_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v___x_2229_);
v___x_2231_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
return v___x_2231_;
}
}
}
}
else
{
lean_object* v_a_2234_; lean_object* v___x_2236_; uint8_t v_isShared_2237_; uint8_t v_isSharedCheck_2241_; 
lean_dec_ref(v_e_2120_);
lean_dec_ref(v_c_2119_);
lean_dec_ref(v_k_2118_);
lean_dec(v_v_2117_);
lean_dec(v_u_2116_);
v_a_2234_ = lean_ctor_get(v___x_2133_, 0);
v_isSharedCheck_2241_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2241_ == 0)
{
v___x_2236_ = v___x_2133_;
v_isShared_2237_ = v_isSharedCheck_2241_;
goto v_resetjp_2235_;
}
else
{
lean_inc(v_a_2234_);
lean_dec(v___x_2133_);
v___x_2236_ = lean_box(0);
v_isShared_2237_ = v_isSharedCheck_2241_;
goto v_resetjp_2235_;
}
v_resetjp_2235_:
{
lean_object* v___x_2239_; 
if (v_isShared_2237_ == 0)
{
v___x_2239_ = v___x_2236_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v_a_2234_);
v___x_2239_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
return v___x_2239_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___boxed(lean_object** _args){
lean_object* v_u_2242_ = _args[0];
lean_object* v_v_2243_ = _args[1];
lean_object* v_k_2244_ = _args[2];
lean_object* v_c_2245_ = _args[3];
lean_object* v_e_2246_ = _args[4];
lean_object* v_a_2247_ = _args[5];
lean_object* v_a_2248_ = _args[6];
lean_object* v_a_2249_ = _args[7];
lean_object* v_a_2250_ = _args[8];
lean_object* v_a_2251_ = _args[9];
lean_object* v_a_2252_ = _args[10];
lean_object* v_a_2253_ = _args[11];
lean_object* v_a_2254_ = _args[12];
lean_object* v_a_2255_ = _args[13];
lean_object* v_a_2256_ = _args[14];
lean_object* v_a_2257_ = _args[15];
lean_object* v_a_2258_ = _args[16];
_start:
{
lean_object* v_res_2259_; 
v_res_2259_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue(v_u_2242_, v_v_2243_, v_k_2244_, v_c_2245_, v_e_2246_, v_a_2247_, v_a_2248_, v_a_2249_, v_a_2250_, v_a_2251_, v_a_2252_, v_a_2253_, v_a_2254_, v_a_2255_, v_a_2256_, v_a_2257_);
lean_dec(v_a_2257_);
lean_dec_ref(v_a_2256_);
lean_dec(v_a_2255_);
lean_dec_ref(v_a_2254_);
lean_dec(v_a_2253_);
lean_dec_ref(v_a_2252_);
lean_dec(v_a_2251_);
lean_dec_ref(v_a_2250_);
lean_dec(v_a_2249_);
lean_dec(v_a_2248_);
lean_dec(v_a_2247_);
return v_res_2259_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse___redArg(lean_object* v_e_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_){
_start:
{
lean_object* v___x_2268_; 
v___x_2268_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_2261_, v_a_2265_);
if (lean_obj_tag(v___x_2268_) == 0)
{
lean_object* v_a_2269_; lean_object* v_termMapInv_2270_; lean_object* v___x_2271_; 
v_a_2269_ = lean_ctor_get(v___x_2268_, 0);
lean_inc(v_a_2269_);
lean_dec_ref_known(v___x_2268_, 1);
v_termMapInv_2270_ = lean_ctor_get(v_a_2269_, 4);
lean_inc_ref(v_termMapInv_2270_);
lean_dec(v_a_2269_);
v___x_2271_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMapInv_2270_, v_e_2260_);
lean_dec_ref(v_termMapInv_2270_);
if (lean_obj_tag(v___x_2271_) == 1)
{
lean_object* v_val_2272_; lean_object* v_fst_2273_; lean_object* v___x_2274_; 
lean_dec_ref(v_e_2260_);
v_val_2272_ = lean_ctor_get(v___x_2271_, 0);
lean_inc(v_val_2272_);
lean_dec_ref_known(v___x_2271_, 1);
v_fst_2273_ = lean_ctor_get(v_val_2272_, 0);
lean_inc(v_fst_2273_);
lean_dec(v_val_2272_);
v___x_2274_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_fst_2273_, v_a_2261_);
if (lean_obj_tag(v___x_2274_) == 0)
{
lean_object* v_a_2275_; uint8_t v___x_2276_; 
v_a_2275_ = lean_ctor_get(v___x_2274_, 0);
v___x_2276_ = lean_unbox(v_a_2275_);
if (v___x_2276_ == 0)
{
lean_dec(v_fst_2273_);
return v___x_2274_;
}
else
{
lean_object* v___x_2277_; 
lean_dec_ref_known(v___x_2274_, 1);
v___x_2277_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_fst_2273_, v_a_2261_, v_a_2262_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_);
return v___x_2277_;
}
}
else
{
lean_dec(v_fst_2273_);
return v___x_2274_;
}
}
else
{
lean_object* v___x_2278_; 
lean_dec(v___x_2271_);
v___x_2278_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_e_2260_, v_a_2261_);
if (lean_obj_tag(v___x_2278_) == 0)
{
lean_object* v_a_2279_; uint8_t v___x_2280_; 
v_a_2279_ = lean_ctor_get(v___x_2278_, 0);
v___x_2280_ = lean_unbox(v_a_2279_);
if (v___x_2280_ == 0)
{
lean_dec_ref(v_e_2260_);
return v___x_2278_;
}
else
{
lean_object* v___x_2281_; 
lean_dec_ref_known(v___x_2278_, 1);
v___x_2281_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_2260_, v_a_2261_, v_a_2262_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_);
return v___x_2281_;
}
}
else
{
lean_dec_ref(v_e_2260_);
return v___x_2278_;
}
}
}
else
{
lean_object* v_a_2282_; lean_object* v___x_2284_; uint8_t v_isShared_2285_; uint8_t v_isSharedCheck_2289_; 
lean_dec_ref(v_e_2260_);
v_a_2282_ = lean_ctor_get(v___x_2268_, 0);
v_isSharedCheck_2289_ = !lean_is_exclusive(v___x_2268_);
if (v_isSharedCheck_2289_ == 0)
{
v___x_2284_ = v___x_2268_;
v_isShared_2285_ = v_isSharedCheck_2289_;
goto v_resetjp_2283_;
}
else
{
lean_inc(v_a_2282_);
lean_dec(v___x_2268_);
v___x_2284_ = lean_box(0);
v_isShared_2285_ = v_isSharedCheck_2289_;
goto v_resetjp_2283_;
}
v_resetjp_2283_:
{
lean_object* v___x_2287_; 
if (v_isShared_2285_ == 0)
{
v___x_2287_ = v___x_2284_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v_a_2282_);
v___x_2287_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
return v___x_2287_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse___redArg___boxed(lean_object* v_e_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_){
_start:
{
lean_object* v_res_2298_; 
v_res_2298_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse___redArg(v_e_2290_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_);
lean_dec(v_a_2296_);
lean_dec_ref(v_a_2295_);
lean_dec(v_a_2294_);
lean_dec_ref(v_a_2293_);
lean_dec_ref(v_a_2292_);
lean_dec(v_a_2291_);
return v_res_2298_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse(lean_object* v_e_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_){
_start:
{
lean_object* v___x_2312_; 
v___x_2312_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse___redArg(v_e_2299_, v_a_2301_, v_a_2305_, v_a_2307_, v_a_2308_, v_a_2309_, v_a_2310_);
return v___x_2312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse___boxed(lean_object* v_e_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_, lean_object* v_a_2318_, lean_object* v_a_2319_, lean_object* v_a_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_){
_start:
{
lean_object* v_res_2326_; 
v_res_2326_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse(v_e_2313_, v_a_2314_, v_a_2315_, v_a_2316_, v_a_2317_, v_a_2318_, v_a_2319_, v_a_2320_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_);
lean_dec(v_a_2324_);
lean_dec_ref(v_a_2323_);
lean_dec(v_a_2322_);
lean_dec_ref(v_a_2321_);
lean_dec(v_a_2320_);
lean_dec_ref(v_a_2319_);
lean_dec(v_a_2318_);
lean_dec_ref(v_a_2317_);
lean_dec(v_a_2316_);
lean_dec(v_a_2315_);
lean_dec(v_a_2314_);
return v_res_2326_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__2(void){
_start:
{
lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; 
v___x_2333_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__1));
v___x_2334_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__6));
v___x_2335_ = l_Lean_Name_append(v___x_2334_, v___x_2333_);
return v___x_2335_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__4(void){
_start:
{
lean_object* v___x_2337_; lean_object* v___x_2338_; 
v___x_2337_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__3));
v___x_2338_ = l_Lean_stringToMessageData(v___x_2337_);
return v___x_2338_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse(lean_object* v_u_2339_, lean_object* v_v_2340_, lean_object* v_k_2341_, lean_object* v_c_2342_, lean_object* v_e_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_){
_start:
{
lean_object* v___x_2356_; 
lean_inc_ref(v_e_2343_);
v___x_2356_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse___redArg(v_e_2343_, v_a_2345_, v_a_2349_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_);
if (lean_obj_tag(v___x_2356_) == 0)
{
lean_object* v_a_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2458_; 
v_a_2357_ = lean_ctor_get(v___x_2356_, 0);
v_isSharedCheck_2458_ = !lean_is_exclusive(v___x_2356_);
if (v_isSharedCheck_2458_ == 0)
{
v___x_2359_ = v___x_2356_;
v_isShared_2360_ = v_isSharedCheck_2458_;
goto v_resetjp_2358_;
}
else
{
lean_inc(v_a_2357_);
lean_dec(v___x_2356_);
v___x_2359_ = lean_box(0);
v_isShared_2360_ = v_isSharedCheck_2458_;
goto v_resetjp_2358_;
}
v_resetjp_2358_:
{
uint8_t v___x_2361_; 
v___x_2361_ = lean_unbox(v_a_2357_);
lean_dec(v_a_2357_);
if (v___x_2361_ == 0)
{
lean_object* v_toCold_2362_; lean_object* v_options_2363_; lean_object* v_inheritedTraceOptions_2364_; uint8_t v_hasTrace_2365_; lean_object* v___x_2366_; lean_object* v___y_2368_; lean_object* v___y_2369_; lean_object* v___y_2370_; lean_object* v___y_2371_; lean_object* v___y_2372_; lean_object* v___y_2373_; lean_object* v___y_2374_; lean_object* v___y_2375_; lean_object* v___y_2376_; lean_object* v___y_2377_; lean_object* v___y_2378_; 
v_toCold_2362_ = lean_ctor_get(v_a_2353_, 0);
v_options_2363_ = lean_ctor_get(v_toCold_2362_, 2);
v_inheritedTraceOptions_2364_ = lean_ctor_get(v_toCold_2362_, 11);
v_hasTrace_2365_ = lean_ctor_get_uint8(v_options_2363_, sizeof(void*)*1);
v___x_2366_ = l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(v_c_2342_);
if (v_hasTrace_2365_ == 0)
{
v___y_2368_ = v_a_2344_;
v___y_2369_ = v_a_2345_;
v___y_2370_ = v_a_2346_;
v___y_2371_ = v_a_2347_;
v___y_2372_ = v_a_2348_;
v___y_2373_ = v_a_2349_;
v___y_2374_ = v_a_2350_;
v___y_2375_ = v_a_2351_;
v___y_2376_ = v_a_2352_;
v___y_2377_ = v_a_2353_;
v___y_2378_ = v_a_2354_;
goto v___jp_2367_;
}
else
{
lean_object* v___x_2387_; lean_object* v___x_2388_; uint8_t v___x_2389_; 
v___x_2387_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__1));
v___x_2388_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__2, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__2);
v___x_2389_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2364_, v_options_2363_, v___x_2388_);
if (v___x_2389_ == 0)
{
v___y_2368_ = v_a_2344_;
v___y_2369_ = v_a_2345_;
v___y_2370_ = v_a_2346_;
v___y_2371_ = v_a_2347_;
v___y_2372_ = v_a_2348_;
v___y_2373_ = v_a_2349_;
v___y_2374_ = v_a_2350_;
v___y_2375_ = v_a_2351_;
v___y_2376_ = v_a_2352_;
v___y_2377_ = v_a_2353_;
v___y_2378_ = v_a_2354_;
goto v___jp_2367_;
}
else
{
lean_object* v___x_2390_; 
v___x_2390_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_u_2339_, v_a_2344_, v_a_2345_, v_a_2353_);
if (lean_obj_tag(v___x_2390_) == 0)
{
lean_object* v_a_2391_; lean_object* v___x_2392_; 
v_a_2391_ = lean_ctor_get(v___x_2390_, 0);
lean_inc(v_a_2391_);
lean_dec_ref_known(v___x_2390_, 1);
v___x_2392_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_v_2340_, v_a_2344_, v_a_2345_, v_a_2353_);
if (lean_obj_tag(v___x_2392_) == 0)
{
lean_object* v_a_2393_; lean_object* v___x_2394_; 
v_a_2393_ = lean_ctor_get(v___x_2392_, 0);
lean_inc(v_a_2393_);
lean_dec_ref_known(v___x_2392_, 1);
v___x_2394_ = l_Lean_Meta_Grind_Order_Cnstr_pp___redArg(v_c_2342_, v_a_2344_, v_a_2345_, v_a_2353_);
if (lean_obj_tag(v___x_2394_) == 0)
{
lean_object* v_a_2395_; lean_object* v___y_2397_; lean_object* v___y_2398_; lean_object* v_k_2406_; uint8_t v_strict_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___y_2415_; 
v_a_2395_ = lean_ctor_get(v___x_2394_, 0);
lean_inc(v_a_2395_);
lean_dec_ref_known(v___x_2394_, 1);
v_k_2406_ = lean_ctor_get(v_k_2341_, 0);
v_strict_2407_ = lean_ctor_get_uint8(v_k_2341_, sizeof(void*)*1);
v___x_2408_ = l_Lean_MessageData_ofExpr(v_a_2391_);
v___x_2409_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4);
v___x_2410_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2410_, 0, v___x_2408_);
lean_ctor_set(v___x_2410_, 1, v___x_2409_);
v___x_2411_ = l_Lean_MessageData_ofExpr(v_a_2393_);
v___x_2412_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2412_, 0, v___x_2410_);
lean_ctor_set(v___x_2412_, 1, v___x_2411_);
v___x_2413_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2413_, 0, v___x_2412_);
lean_ctor_set(v___x_2413_, 1, v___x_2409_);
if (v_strict_2407_ == 0)
{
lean_object* v___x_2426_; 
v___x_2426_ = l_Int_repr(v_k_2406_);
v___y_2415_ = v___x_2426_;
goto v___jp_2414_;
}
else
{
lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; 
v___x_2427_ = l_Int_repr(v_k_2406_);
v___x_2428_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5));
v___x_2429_ = lean_string_append(v___x_2427_, v___x_2428_);
v___y_2415_ = v___x_2429_;
goto v___jp_2414_;
}
v___jp_2396_:
{
lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; 
v___x_2399_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2399_, 0, v___y_2398_);
v___x_2400_ = l_Lean_MessageData_ofFormat(v___x_2399_);
v___x_2401_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2401_, 0, v___y_2397_);
lean_ctor_set(v___x_2401_, 1, v___x_2400_);
v___x_2402_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__4);
v___x_2403_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2403_, 0, v___x_2401_);
lean_ctor_set(v___x_2403_, 1, v___x_2402_);
v___x_2404_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2404_, 0, v___x_2403_);
lean_ctor_set(v___x_2404_, 1, v_a_2395_);
v___x_2405_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(v___x_2387_, v___x_2404_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_);
if (lean_obj_tag(v___x_2405_) == 0)
{
lean_dec_ref_known(v___x_2405_, 1);
v___y_2368_ = v_a_2344_;
v___y_2369_ = v_a_2345_;
v___y_2370_ = v_a_2346_;
v___y_2371_ = v_a_2347_;
v___y_2372_ = v_a_2348_;
v___y_2373_ = v_a_2349_;
v___y_2374_ = v_a_2350_;
v___y_2375_ = v_a_2351_;
v___y_2376_ = v_a_2352_;
v___y_2377_ = v_a_2353_;
v___y_2378_ = v_a_2354_;
goto v___jp_2367_;
}
else
{
lean_dec_ref(v___x_2366_);
lean_del_object(v___x_2359_);
lean_dec_ref(v_e_2343_);
lean_dec_ref(v_c_2342_);
lean_dec_ref(v_k_2341_);
lean_dec(v_v_2340_);
lean_dec(v_u_2339_);
return v___x_2405_;
}
}
v___jp_2414_:
{
lean_object* v_k_2416_; uint8_t v_strict_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; 
v_k_2416_ = lean_ctor_get(v___x_2366_, 0);
v_strict_2417_ = lean_ctor_get_uint8(v___x_2366_, sizeof(void*)*1);
v___x_2418_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2418_, 0, v___y_2415_);
v___x_2419_ = l_Lean_MessageData_ofFormat(v___x_2418_);
v___x_2420_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2420_, 0, v___x_2413_);
lean_ctor_set(v___x_2420_, 1, v___x_2419_);
v___x_2421_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2421_, 0, v___x_2420_);
lean_ctor_set(v___x_2421_, 1, v___x_2409_);
if (v_strict_2417_ == 0)
{
lean_object* v___x_2422_; 
v___x_2422_ = l_Int_repr(v_k_2416_);
v___y_2397_ = v___x_2421_;
v___y_2398_ = v___x_2422_;
goto v___jp_2396_;
}
else
{
lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; 
v___x_2423_ = l_Int_repr(v_k_2416_);
v___x_2424_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5));
v___x_2425_ = lean_string_append(v___x_2423_, v___x_2424_);
v___y_2397_ = v___x_2421_;
v___y_2398_ = v___x_2425_;
goto v___jp_2396_;
}
}
}
else
{
lean_object* v_a_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2437_; 
lean_dec(v_a_2393_);
lean_dec(v_a_2391_);
lean_dec_ref(v___x_2366_);
lean_del_object(v___x_2359_);
lean_dec_ref(v_e_2343_);
lean_dec_ref(v_c_2342_);
lean_dec_ref(v_k_2341_);
lean_dec(v_v_2340_);
lean_dec(v_u_2339_);
v_a_2430_ = lean_ctor_get(v___x_2394_, 0);
v_isSharedCheck_2437_ = !lean_is_exclusive(v___x_2394_);
if (v_isSharedCheck_2437_ == 0)
{
v___x_2432_ = v___x_2394_;
v_isShared_2433_ = v_isSharedCheck_2437_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_a_2430_);
lean_dec(v___x_2394_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2437_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
lean_object* v___x_2435_; 
if (v_isShared_2433_ == 0)
{
v___x_2435_ = v___x_2432_;
goto v_reusejp_2434_;
}
else
{
lean_object* v_reuseFailAlloc_2436_; 
v_reuseFailAlloc_2436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2436_, 0, v_a_2430_);
v___x_2435_ = v_reuseFailAlloc_2436_;
goto v_reusejp_2434_;
}
v_reusejp_2434_:
{
return v___x_2435_;
}
}
}
}
else
{
lean_object* v_a_2438_; lean_object* v___x_2440_; uint8_t v_isShared_2441_; uint8_t v_isSharedCheck_2445_; 
lean_dec(v_a_2391_);
lean_dec_ref(v___x_2366_);
lean_del_object(v___x_2359_);
lean_dec_ref(v_e_2343_);
lean_dec_ref(v_c_2342_);
lean_dec_ref(v_k_2341_);
lean_dec(v_v_2340_);
lean_dec(v_u_2339_);
v_a_2438_ = lean_ctor_get(v___x_2392_, 0);
v_isSharedCheck_2445_ = !lean_is_exclusive(v___x_2392_);
if (v_isSharedCheck_2445_ == 0)
{
v___x_2440_ = v___x_2392_;
v_isShared_2441_ = v_isSharedCheck_2445_;
goto v_resetjp_2439_;
}
else
{
lean_inc(v_a_2438_);
lean_dec(v___x_2392_);
v___x_2440_ = lean_box(0);
v_isShared_2441_ = v_isSharedCheck_2445_;
goto v_resetjp_2439_;
}
v_resetjp_2439_:
{
lean_object* v___x_2443_; 
if (v_isShared_2441_ == 0)
{
v___x_2443_ = v___x_2440_;
goto v_reusejp_2442_;
}
else
{
lean_object* v_reuseFailAlloc_2444_; 
v_reuseFailAlloc_2444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2444_, 0, v_a_2438_);
v___x_2443_ = v_reuseFailAlloc_2444_;
goto v_reusejp_2442_;
}
v_reusejp_2442_:
{
return v___x_2443_;
}
}
}
}
else
{
lean_object* v_a_2446_; lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2453_; 
lean_dec_ref(v___x_2366_);
lean_del_object(v___x_2359_);
lean_dec_ref(v_e_2343_);
lean_dec_ref(v_c_2342_);
lean_dec_ref(v_k_2341_);
lean_dec(v_v_2340_);
lean_dec(v_u_2339_);
v_a_2446_ = lean_ctor_get(v___x_2390_, 0);
v_isSharedCheck_2453_ = !lean_is_exclusive(v___x_2390_);
if (v_isSharedCheck_2453_ == 0)
{
v___x_2448_ = v___x_2390_;
v_isShared_2449_ = v_isSharedCheck_2453_;
goto v_resetjp_2447_;
}
else
{
lean_inc(v_a_2446_);
lean_dec(v___x_2390_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2453_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
lean_object* v___x_2451_; 
if (v_isShared_2449_ == 0)
{
v___x_2451_ = v___x_2448_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v_a_2446_);
v___x_2451_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2450_;
}
v_reusejp_2450_:
{
return v___x_2451_;
}
}
}
}
}
v___jp_2367_:
{
lean_object* v___x_2379_; uint8_t v___x_2380_; 
lean_inc_ref(v___x_2366_);
v___x_2379_ = l_Lean_Meta_Grind_Order_Weight_add(v_k_2341_, v___x_2366_);
v___x_2380_ = l_Lean_Meta_Grind_Order_Weight_isNeg(v___x_2379_);
lean_dec_ref(v___x_2379_);
if (v___x_2380_ == 0)
{
lean_object* v___x_2381_; lean_object* v___x_2383_; 
lean_dec_ref(v___x_2366_);
lean_dec_ref(v_e_2343_);
lean_dec_ref(v_c_2342_);
lean_dec_ref(v_k_2341_);
lean_dec(v_v_2340_);
lean_dec(v_u_2339_);
v___x_2381_ = lean_box(0);
if (v_isShared_2360_ == 0)
{
lean_ctor_set(v___x_2359_, 0, v___x_2381_);
v___x_2383_ = v___x_2359_;
goto v_reusejp_2382_;
}
else
{
lean_object* v_reuseFailAlloc_2384_; 
v_reuseFailAlloc_2384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2384_, 0, v___x_2381_);
v___x_2383_ = v_reuseFailAlloc_2384_;
goto v_reusejp_2382_;
}
v_reusejp_2382_:
{
return v___x_2383_;
}
}
else
{
lean_object* v___x_2385_; lean_object* v___x_2386_; 
lean_del_object(v___x_2359_);
v___x_2385_ = lean_alloc_ctor(1, 6, 0);
lean_ctor_set(v___x_2385_, 0, v_c_2342_);
lean_ctor_set(v___x_2385_, 1, v_e_2343_);
lean_ctor_set(v___x_2385_, 2, v_u_2339_);
lean_ctor_set(v___x_2385_, 3, v_v_2340_);
lean_ctor_set(v___x_2385_, 4, v_k_2341_);
lean_ctor_set(v___x_2385_, 5, v___x_2366_);
v___x_2386_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate(v___x_2385_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_);
return v___x_2386_;
}
}
}
else
{
lean_object* v___x_2454_; lean_object* v___x_2456_; 
lean_dec_ref(v_e_2343_);
lean_dec_ref(v_c_2342_);
lean_dec_ref(v_k_2341_);
lean_dec(v_v_2340_);
lean_dec(v_u_2339_);
v___x_2454_ = lean_box(0);
if (v_isShared_2360_ == 0)
{
lean_ctor_set(v___x_2359_, 0, v___x_2454_);
v___x_2456_ = v___x_2359_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v___x_2454_);
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
lean_dec_ref(v_e_2343_);
lean_dec_ref(v_c_2342_);
lean_dec_ref(v_k_2341_);
lean_dec(v_v_2340_);
lean_dec(v_u_2339_);
v_a_2459_ = lean_ctor_get(v___x_2356_, 0);
v_isSharedCheck_2466_ = !lean_is_exclusive(v___x_2356_);
if (v_isSharedCheck_2466_ == 0)
{
v___x_2461_ = v___x_2356_;
v_isShared_2462_ = v_isSharedCheck_2466_;
goto v_resetjp_2460_;
}
else
{
lean_inc(v_a_2459_);
lean_dec(v___x_2356_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___boxed(lean_object** _args){
lean_object* v_u_2467_ = _args[0];
lean_object* v_v_2468_ = _args[1];
lean_object* v_k_2469_ = _args[2];
lean_object* v_c_2470_ = _args[3];
lean_object* v_e_2471_ = _args[4];
lean_object* v_a_2472_ = _args[5];
lean_object* v_a_2473_ = _args[6];
lean_object* v_a_2474_ = _args[7];
lean_object* v_a_2475_ = _args[8];
lean_object* v_a_2476_ = _args[9];
lean_object* v_a_2477_ = _args[10];
lean_object* v_a_2478_ = _args[11];
lean_object* v_a_2479_ = _args[12];
lean_object* v_a_2480_ = _args[13];
lean_object* v_a_2481_ = _args[14];
lean_object* v_a_2482_ = _args[15];
lean_object* v_a_2483_ = _args[16];
_start:
{
lean_object* v_res_2484_; 
v_res_2484_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse(v_u_2467_, v_v_2468_, v_k_2469_, v_c_2470_, v_e_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_, v_a_2476_, v_a_2477_, v_a_2478_, v_a_2479_, v_a_2480_, v_a_2481_, v_a_2482_);
lean_dec(v_a_2482_);
lean_dec_ref(v_a_2481_);
lean_dec(v_a_2480_);
lean_dec_ref(v_a_2479_);
lean_dec(v_a_2478_);
lean_dec_ref(v_a_2477_);
lean_dec(v_a_2476_);
lean_dec_ref(v_a_2475_);
lean_dec(v_a_2474_);
lean_dec(v_a_2473_);
lean_dec(v_a_2472_);
return v_res_2484_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___lam__0(lean_object* v_f_2485_, lean_object* v_x_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_){
_start:
{
lean_object* v_fst_2499_; lean_object* v_snd_2500_; lean_object* v___x_2501_; 
v_fst_2499_ = lean_ctor_get(v_x_2486_, 0);
lean_inc(v_fst_2499_);
v_snd_2500_ = lean_ctor_get(v_x_2486_, 1);
lean_inc(v_snd_2500_);
lean_dec_ref(v_x_2486_);
lean_inc(v___y_2497_);
lean_inc_ref(v___y_2496_);
lean_inc(v___y_2495_);
lean_inc_ref(v___y_2494_);
lean_inc(v___y_2493_);
lean_inc_ref(v___y_2492_);
lean_inc(v___y_2491_);
lean_inc_ref(v___y_2490_);
lean_inc(v___y_2489_);
lean_inc(v___y_2488_);
lean_inc(v___y_2487_);
v___x_2501_ = lean_apply_14(v_f_2485_, v_fst_2499_, v_snd_2500_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_, lean_box(0));
return v___x_2501_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___lam__0___boxed(lean_object* v_f_2502_, lean_object* v_x_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_){
_start:
{
lean_object* v_res_2516_; 
v_res_2516_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___lam__0(v_f_2502_, v_x_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_);
lean_dec(v___y_2514_);
lean_dec_ref(v___y_2513_);
lean_dec(v___y_2512_);
lean_dec_ref(v___y_2511_);
lean_dec(v___y_2510_);
lean_dec_ref(v___y_2509_);
lean_dec(v___y_2508_);
lean_dec_ref(v___y_2507_);
lean_dec(v___y_2506_);
lean_dec(v___y_2505_);
lean_dec(v___y_2504_);
return v_res_2516_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__2(void){
_start:
{
lean_object* v___x_2520_; lean_object* v___f_2521_; 
v___x_2520_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___f_2521_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2521_, 0, v___x_2520_);
return v___f_2521_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__3(void){
_start:
{
lean_object* v___f_2522_; lean_object* v___f_2523_; 
v___f_2522_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__2, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__2);
v___f_2523_ = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2523_, 0, v___f_2522_);
lean_closure_set(v___f_2523_, 1, v___f_2522_);
return v___f_2523_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf(lean_object* v_u_2524_, lean_object* v_v_2525_, lean_object* v_f_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_){
_start:
{
lean_object* v___x_2539_; lean_object* v_toApplicative_2540_; lean_object* v_toFunctor_2541_; lean_object* v_toSeq_2542_; lean_object* v_toSeqLeft_2543_; lean_object* v_toSeqRight_2544_; lean_object* v___f_2545_; lean_object* v___f_2546_; lean_object* v___f_2547_; lean_object* v___f_2548_; lean_object* v___x_2549_; lean_object* v___f_2550_; lean_object* v___f_2551_; lean_object* v___f_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v_toApplicative_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2617_; 
v___x_2539_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__1, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__1);
v_toApplicative_2540_ = lean_ctor_get(v___x_2539_, 0);
v_toFunctor_2541_ = lean_ctor_get(v_toApplicative_2540_, 0);
v_toSeq_2542_ = lean_ctor_get(v_toApplicative_2540_, 2);
v_toSeqLeft_2543_ = lean_ctor_get(v_toApplicative_2540_, 3);
v_toSeqRight_2544_ = lean_ctor_get(v_toApplicative_2540_, 4);
v___f_2545_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__2));
v___f_2546_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__3));
lean_inc_ref_n(v_toFunctor_2541_, 2);
v___f_2547_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2547_, 0, v_toFunctor_2541_);
v___f_2548_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2548_, 0, v_toFunctor_2541_);
v___x_2549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2549_, 0, v___f_2547_);
lean_ctor_set(v___x_2549_, 1, v___f_2548_);
lean_inc(v_toSeqRight_2544_);
v___f_2550_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2550_, 0, v_toSeqRight_2544_);
lean_inc(v_toSeqLeft_2543_);
v___f_2551_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2551_, 0, v_toSeqLeft_2543_);
lean_inc(v_toSeq_2542_);
v___f_2552_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2552_, 0, v_toSeq_2542_);
v___x_2553_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2553_, 0, v___x_2549_);
lean_ctor_set(v___x_2553_, 1, v___f_2545_);
lean_ctor_set(v___x_2553_, 2, v___f_2552_);
lean_ctor_set(v___x_2553_, 3, v___f_2551_);
lean_ctor_set(v___x_2553_, 4, v___f_2550_);
v___x_2554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2554_, 0, v___x_2553_);
lean_ctor_set(v___x_2554_, 1, v___f_2546_);
v___x_2555_ = l_StateRefT_x27_instMonad___redArg(v___x_2554_);
v_toApplicative_2556_ = lean_ctor_get(v___x_2555_, 0);
v_isSharedCheck_2617_ = !lean_is_exclusive(v___x_2555_);
if (v_isSharedCheck_2617_ == 0)
{
lean_object* v_unused_2618_; 
v_unused_2618_ = lean_ctor_get(v___x_2555_, 1);
lean_dec(v_unused_2618_);
v___x_2558_ = v___x_2555_;
v_isShared_2559_ = v_isSharedCheck_2617_;
goto v_resetjp_2557_;
}
else
{
lean_inc(v_toApplicative_2556_);
lean_dec(v___x_2555_);
v___x_2558_ = lean_box(0);
v_isShared_2559_ = v_isSharedCheck_2617_;
goto v_resetjp_2557_;
}
v_resetjp_2557_:
{
lean_object* v_toFunctor_2560_; lean_object* v_toSeq_2561_; lean_object* v_toSeqLeft_2562_; lean_object* v_toSeqRight_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2615_; 
v_toFunctor_2560_ = lean_ctor_get(v_toApplicative_2556_, 0);
v_toSeq_2561_ = lean_ctor_get(v_toApplicative_2556_, 2);
v_toSeqLeft_2562_ = lean_ctor_get(v_toApplicative_2556_, 3);
v_toSeqRight_2563_ = lean_ctor_get(v_toApplicative_2556_, 4);
v_isSharedCheck_2615_ = !lean_is_exclusive(v_toApplicative_2556_);
if (v_isSharedCheck_2615_ == 0)
{
lean_object* v_unused_2616_; 
v_unused_2616_ = lean_ctor_get(v_toApplicative_2556_, 1);
lean_dec(v_unused_2616_);
v___x_2565_ = v_toApplicative_2556_;
v_isShared_2566_ = v_isSharedCheck_2615_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_toSeqRight_2563_);
lean_inc(v_toSeqLeft_2562_);
lean_inc(v_toSeq_2561_);
lean_inc(v_toFunctor_2560_);
lean_dec(v_toApplicative_2556_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2615_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
lean_object* v___f_2567_; lean_object* v___f_2568_; lean_object* v___f_2569_; lean_object* v___f_2570_; lean_object* v___f_2571_; lean_object* v___x_2572_; lean_object* v___f_2573_; lean_object* v___f_2574_; lean_object* v___f_2575_; lean_object* v___x_2577_; 
v___f_2567_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___lam__0___boxed), 14, 1);
lean_closure_set(v___f_2567_, 0, v_f_2526_);
v___f_2568_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__4));
v___f_2569_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__5));
lean_inc_ref(v_toFunctor_2560_);
v___f_2570_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2570_, 0, v_toFunctor_2560_);
v___f_2571_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2571_, 0, v_toFunctor_2560_);
v___x_2572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2572_, 0, v___f_2570_);
lean_ctor_set(v___x_2572_, 1, v___f_2571_);
v___f_2573_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2573_, 0, v_toSeqRight_2563_);
v___f_2574_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2574_, 0, v_toSeqLeft_2562_);
v___f_2575_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2575_, 0, v_toSeq_2561_);
if (v_isShared_2566_ == 0)
{
lean_ctor_set(v___x_2565_, 4, v___f_2573_);
lean_ctor_set(v___x_2565_, 3, v___f_2574_);
lean_ctor_set(v___x_2565_, 2, v___f_2575_);
lean_ctor_set(v___x_2565_, 1, v___f_2568_);
lean_ctor_set(v___x_2565_, 0, v___x_2572_);
v___x_2577_ = v___x_2565_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v___x_2572_);
lean_ctor_set(v_reuseFailAlloc_2614_, 1, v___f_2568_);
lean_ctor_set(v_reuseFailAlloc_2614_, 2, v___f_2575_);
lean_ctor_set(v_reuseFailAlloc_2614_, 3, v___f_2574_);
lean_ctor_set(v_reuseFailAlloc_2614_, 4, v___f_2573_);
v___x_2577_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
lean_object* v___x_2579_; 
if (v_isShared_2559_ == 0)
{
lean_ctor_set(v___x_2558_, 1, v___f_2569_);
lean_ctor_set(v___x_2558_, 0, v___x_2577_);
v___x_2579_ = v___x_2558_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v___x_2577_);
lean_ctor_set(v_reuseFailAlloc_2613_, 1, v___f_2569_);
v___x_2579_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___f_2587_; lean_object* v___x_2588_; 
v___x_2580_ = l_StateRefT_x27_instMonad___redArg(v___x_2579_);
v___x_2581_ = l_ReaderT_instMonad___redArg(v___x_2580_);
v___x_2582_ = l_StateRefT_x27_instMonad___redArg(v___x_2581_);
v___x_2583_ = l_ReaderT_instMonad___redArg(v___x_2582_);
v___x_2584_ = l_ReaderT_instMonad___redArg(v___x_2583_);
v___x_2585_ = l_StateRefT_x27_instMonad___redArg(v___x_2584_);
v___x_2586_ = l_ReaderT_instMonad___redArg(v___x_2585_);
v___f_2587_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__1));
v___x_2588_ = l_Lean_Meta_Grind_Order_getStruct___redArg(v_a_2527_, v_a_2528_, v_a_2536_);
if (lean_obj_tag(v___x_2588_) == 0)
{
lean_object* v_a_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2604_; 
v_a_2589_ = lean_ctor_get(v___x_2588_, 0);
v_isSharedCheck_2604_ = !lean_is_exclusive(v___x_2588_);
if (v_isSharedCheck_2604_ == 0)
{
v___x_2591_ = v___x_2588_;
v_isShared_2592_ = v_isSharedCheck_2604_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_a_2589_);
lean_dec(v___x_2588_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2604_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v___f_2593_; lean_object* v_cnstrsOf_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; 
v___f_2593_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__3);
v_cnstrsOf_2594_ = lean_ctor_get(v_a_2589_, 4);
lean_inc_ref(v_cnstrsOf_2594_);
lean_dec(v_a_2589_);
v___x_2595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2595_, 0, v_u_2524_);
lean_ctor_set(v___x_2595_, 1, v_v_2525_);
v___x_2596_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_2593_, v___f_2587_, v_cnstrsOf_2594_, v___x_2595_);
lean_dec_ref(v_cnstrsOf_2594_);
if (lean_obj_tag(v___x_2596_) == 1)
{
lean_object* v_val_2597_; lean_object* v___x_1500__overap_2598_; lean_object* v___x_2599_; 
lean_del_object(v___x_2591_);
v_val_2597_ = lean_ctor_get(v___x_2596_, 0);
lean_inc(v_val_2597_);
lean_dec_ref_known(v___x_2596_, 1);
v___x_1500__overap_2598_ = l_List_forM___redArg(v___x_2586_, v_val_2597_, v___f_2567_);
lean_inc(v_a_2537_);
lean_inc_ref(v_a_2536_);
lean_inc(v_a_2535_);
lean_inc_ref(v_a_2534_);
lean_inc(v_a_2533_);
lean_inc_ref(v_a_2532_);
lean_inc(v_a_2531_);
lean_inc_ref(v_a_2530_);
lean_inc(v_a_2529_);
lean_inc(v_a_2528_);
lean_inc(v_a_2527_);
v___x_2599_ = lean_apply_12(v___x_1500__overap_2598_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_, v_a_2535_, v_a_2536_, v_a_2537_, lean_box(0));
return v___x_2599_;
}
else
{
lean_object* v___x_2600_; lean_object* v___x_2602_; 
lean_dec(v___x_2596_);
lean_dec_ref(v___x_2586_);
lean_dec_ref(v___f_2567_);
v___x_2600_ = lean_box(0);
if (v_isShared_2592_ == 0)
{
lean_ctor_set(v___x_2591_, 0, v___x_2600_);
v___x_2602_ = v___x_2591_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v___x_2600_);
v___x_2602_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
return v___x_2602_;
}
}
}
}
else
{
lean_object* v_a_2605_; lean_object* v___x_2607_; uint8_t v_isShared_2608_; uint8_t v_isSharedCheck_2612_; 
lean_dec_ref(v___x_2586_);
lean_dec_ref(v___f_2567_);
lean_dec(v_v_2525_);
lean_dec(v_u_2524_);
v_a_2605_ = lean_ctor_get(v___x_2588_, 0);
v_isSharedCheck_2612_ = !lean_is_exclusive(v___x_2588_);
if (v_isSharedCheck_2612_ == 0)
{
v___x_2607_ = v___x_2588_;
v_isShared_2608_ = v_isSharedCheck_2612_;
goto v_resetjp_2606_;
}
else
{
lean_inc(v_a_2605_);
lean_dec(v___x_2588_);
v___x_2607_ = lean_box(0);
v_isShared_2608_ = v_isSharedCheck_2612_;
goto v_resetjp_2606_;
}
v_resetjp_2606_:
{
lean_object* v___x_2610_; 
if (v_isShared_2608_ == 0)
{
v___x_2610_ = v___x_2607_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v_a_2605_);
v___x_2610_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
return v___x_2610_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___boxed(lean_object* v_u_2619_, lean_object* v_v_2620_, lean_object* v_f_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_){
_start:
{
lean_object* v_res_2634_; 
v_res_2634_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf(v_u_2619_, v_v_2620_, v_f_2621_, v_a_2622_, v_a_2623_, v_a_2624_, v_a_2625_, v_a_2626_, v_a_2627_, v_a_2628_, v_a_2629_, v_a_2630_, v_a_2631_, v_a_2632_);
lean_dec(v_a_2632_);
lean_dec_ref(v_a_2631_);
lean_dec(v_a_2630_);
lean_dec_ref(v_a_2629_);
lean_dec(v_a_2628_);
lean_dec_ref(v_a_2627_);
lean_dec(v_a_2626_);
lean_dec_ref(v_a_2625_);
lean_dec(v_a_2624_);
lean_dec(v_a_2623_);
lean_dec(v_a_2622_);
return v_res_2634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___redArg(lean_object* v_e_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_){
_start:
{
lean_object* v___x_2639_; 
v___x_2639_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_2636_, v_a_2637_);
if (lean_obj_tag(v___x_2639_) == 0)
{
lean_object* v_a_2640_; lean_object* v___x_2642_; uint8_t v_isShared_2643_; uint8_t v_isSharedCheck_2662_; 
v_a_2640_ = lean_ctor_get(v___x_2639_, 0);
v_isSharedCheck_2662_ = !lean_is_exclusive(v___x_2639_);
if (v_isSharedCheck_2662_ == 0)
{
v___x_2642_ = v___x_2639_;
v_isShared_2643_ = v_isSharedCheck_2662_;
goto v_resetjp_2641_;
}
else
{
lean_inc(v_a_2640_);
lean_dec(v___x_2639_);
v___x_2642_ = lean_box(0);
v_isShared_2643_ = v_isSharedCheck_2662_;
goto v_resetjp_2641_;
}
v_resetjp_2641_:
{
lean_object* v_termMapInv_2644_; lean_object* v___x_2645_; 
v_termMapInv_2644_ = lean_ctor_get(v_a_2640_, 4);
lean_inc_ref(v_termMapInv_2644_);
lean_dec(v_a_2640_);
v___x_2645_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMapInv_2644_, v_e_2635_);
lean_dec_ref(v_termMapInv_2644_);
if (lean_obj_tag(v___x_2645_) == 1)
{
lean_object* v_val_2646_; lean_object* v___x_2648_; uint8_t v_isShared_2649_; uint8_t v_isSharedCheck_2657_; 
v_val_2646_ = lean_ctor_get(v___x_2645_, 0);
v_isSharedCheck_2657_ = !lean_is_exclusive(v___x_2645_);
if (v_isSharedCheck_2657_ == 0)
{
v___x_2648_ = v___x_2645_;
v_isShared_2649_ = v_isSharedCheck_2657_;
goto v_resetjp_2647_;
}
else
{
lean_inc(v_val_2646_);
lean_dec(v___x_2645_);
v___x_2648_ = lean_box(0);
v_isShared_2649_ = v_isSharedCheck_2657_;
goto v_resetjp_2647_;
}
v_resetjp_2647_:
{
lean_object* v_fst_2650_; lean_object* v___x_2652_; 
v_fst_2650_ = lean_ctor_get(v_val_2646_, 0);
lean_inc(v_fst_2650_);
lean_dec(v_val_2646_);
if (v_isShared_2649_ == 0)
{
lean_ctor_set(v___x_2648_, 0, v_fst_2650_);
v___x_2652_ = v___x_2648_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2656_; 
v_reuseFailAlloc_2656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2656_, 0, v_fst_2650_);
v___x_2652_ = v_reuseFailAlloc_2656_;
goto v_reusejp_2651_;
}
v_reusejp_2651_:
{
lean_object* v___x_2654_; 
if (v_isShared_2643_ == 0)
{
lean_ctor_set(v___x_2642_, 0, v___x_2652_);
v___x_2654_ = v___x_2642_;
goto v_reusejp_2653_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v___x_2652_);
v___x_2654_ = v_reuseFailAlloc_2655_;
goto v_reusejp_2653_;
}
v_reusejp_2653_:
{
return v___x_2654_;
}
}
}
}
else
{
lean_object* v___x_2658_; lean_object* v___x_2660_; 
lean_dec(v___x_2645_);
v___x_2658_ = lean_box(0);
if (v_isShared_2643_ == 0)
{
lean_ctor_set(v___x_2642_, 0, v___x_2658_);
v___x_2660_ = v___x_2642_;
goto v_reusejp_2659_;
}
else
{
lean_object* v_reuseFailAlloc_2661_; 
v_reuseFailAlloc_2661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2661_, 0, v___x_2658_);
v___x_2660_ = v_reuseFailAlloc_2661_;
goto v_reusejp_2659_;
}
v_reusejp_2659_:
{
return v___x_2660_;
}
}
}
}
else
{
lean_object* v_a_2663_; lean_object* v___x_2665_; uint8_t v_isShared_2666_; uint8_t v_isSharedCheck_2670_; 
v_a_2663_ = lean_ctor_get(v___x_2639_, 0);
v_isSharedCheck_2670_ = !lean_is_exclusive(v___x_2639_);
if (v_isSharedCheck_2670_ == 0)
{
v___x_2665_ = v___x_2639_;
v_isShared_2666_ = v_isSharedCheck_2670_;
goto v_resetjp_2664_;
}
else
{
lean_inc(v_a_2663_);
lean_dec(v___x_2639_);
v___x_2665_ = lean_box(0);
v_isShared_2666_ = v_isSharedCheck_2670_;
goto v_resetjp_2664_;
}
v_resetjp_2664_:
{
lean_object* v___x_2668_; 
if (v_isShared_2666_ == 0)
{
v___x_2668_ = v___x_2665_;
goto v_reusejp_2667_;
}
else
{
lean_object* v_reuseFailAlloc_2669_; 
v_reuseFailAlloc_2669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2669_, 0, v_a_2663_);
v___x_2668_ = v_reuseFailAlloc_2669_;
goto v_reusejp_2667_;
}
v_reusejp_2667_:
{
return v___x_2668_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___redArg___boxed(lean_object* v_e_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_){
_start:
{
lean_object* v_res_2675_; 
v_res_2675_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___redArg(v_e_2671_, v_a_2672_, v_a_2673_);
lean_dec_ref(v_a_2673_);
lean_dec(v_a_2672_);
lean_dec_ref(v_e_2671_);
return v_res_2675_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f(lean_object* v_e_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_){
_start:
{
lean_object* v___x_2688_; 
v___x_2688_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___redArg(v_e_2676_, v_a_2677_, v_a_2685_);
return v___x_2688_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___boxed(lean_object* v_e_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_, lean_object* v_a_2700_){
_start:
{
lean_object* v_res_2701_; 
v_res_2701_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f(v_e_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_, v_a_2697_, v_a_2698_, v_a_2699_);
lean_dec(v_a_2699_);
lean_dec_ref(v_a_2698_);
lean_dec(v_a_2697_);
lean_dec_ref(v_a_2696_);
lean_dec(v_a_2695_);
lean_dec_ref(v_a_2694_);
lean_dec(v_a_2693_);
lean_dec_ref(v_a_2692_);
lean_dec(v_a_2691_);
lean_dec(v_a_2690_);
lean_dec_ref(v_e_2689_);
return v_res_2701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq(lean_object* v_u_2702_, lean_object* v_v_2703_, lean_object* v_k_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_){
_start:
{
lean_object* v___y_2718_; lean_object* v___y_2719_; lean_object* v___y_2720_; uint8_t v___x_2760_; 
v___x_2760_ = lean_nat_dec_eq(v_u_2702_, v_v_2703_);
if (v___x_2760_ == 0)
{
lean_object* v___x_2761_; 
v___x_2761_ = l_Lean_Meta_Grind_Order_isPartialOrder(v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_, v_a_2715_);
if (lean_obj_tag(v___x_2761_) == 0)
{
lean_object* v_a_2762_; lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2899_; 
v_a_2762_ = lean_ctor_get(v___x_2761_, 0);
v_isSharedCheck_2899_ = !lean_is_exclusive(v___x_2761_);
if (v_isSharedCheck_2899_ == 0)
{
v___x_2764_ = v___x_2761_;
v_isShared_2765_ = v_isSharedCheck_2899_;
goto v_resetjp_2763_;
}
else
{
lean_inc(v_a_2762_);
lean_dec(v___x_2761_);
v___x_2764_ = lean_box(0);
v_isShared_2765_ = v_isSharedCheck_2899_;
goto v_resetjp_2763_;
}
v_resetjp_2763_:
{
uint8_t v___x_2766_; 
v___x_2766_ = lean_unbox(v_a_2762_);
lean_dec(v_a_2762_);
if (v___x_2766_ == 0)
{
lean_object* v___x_2767_; lean_object* v___x_2769_; 
lean_dec(v_v_2703_);
lean_dec(v_u_2702_);
v___x_2767_ = lean_box(0);
if (v_isShared_2765_ == 0)
{
lean_ctor_set(v___x_2764_, 0, v___x_2767_);
v___x_2769_ = v___x_2764_;
goto v_reusejp_2768_;
}
else
{
lean_object* v_reuseFailAlloc_2770_; 
v_reuseFailAlloc_2770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2770_, 0, v___x_2767_);
v___x_2769_ = v_reuseFailAlloc_2770_;
goto v_reusejp_2768_;
}
v_reusejp_2768_:
{
return v___x_2769_;
}
}
else
{
uint8_t v___x_2771_; 
v___x_2771_ = l_Lean_Meta_Grind_Order_Weight_isZero(v_k_2704_);
if (v___x_2771_ == 0)
{
lean_object* v___x_2772_; lean_object* v___x_2774_; 
lean_dec(v_v_2703_);
lean_dec(v_u_2702_);
v___x_2772_ = lean_box(0);
if (v_isShared_2765_ == 0)
{
lean_ctor_set(v___x_2764_, 0, v___x_2772_);
v___x_2774_ = v___x_2764_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v___x_2772_);
v___x_2774_ = v_reuseFailAlloc_2775_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
return v___x_2774_;
}
}
else
{
lean_object* v___x_2776_; 
lean_del_object(v___x_2764_);
v___x_2776_ = l_Lean_Meta_Grind_Order_getDist_x3f___redArg(v_v_2703_, v_u_2702_, v_a_2705_, v_a_2706_, v_a_2714_);
if (lean_obj_tag(v___x_2776_) == 0)
{
lean_object* v_a_2777_; lean_object* v___x_2779_; uint8_t v_isShared_2780_; uint8_t v_isSharedCheck_2890_; 
v_a_2777_ = lean_ctor_get(v___x_2776_, 0);
v_isSharedCheck_2890_ = !lean_is_exclusive(v___x_2776_);
if (v_isSharedCheck_2890_ == 0)
{
v___x_2779_ = v___x_2776_;
v_isShared_2780_ = v_isSharedCheck_2890_;
goto v_resetjp_2778_;
}
else
{
lean_inc(v_a_2777_);
lean_dec(v___x_2776_);
v___x_2779_ = lean_box(0);
v_isShared_2780_ = v_isSharedCheck_2890_;
goto v_resetjp_2778_;
}
v_resetjp_2778_:
{
if (lean_obj_tag(v_a_2777_) == 1)
{
lean_object* v_val_2781_; uint8_t v___x_2782_; 
v_val_2781_ = lean_ctor_get(v_a_2777_, 0);
lean_inc(v_val_2781_);
lean_dec_ref_known(v_a_2777_, 1);
v___x_2782_ = l_Lean_Meta_Grind_Order_Weight_isZero(v_val_2781_);
lean_dec(v_val_2781_);
if (v___x_2782_ == 0)
{
lean_object* v___x_2783_; lean_object* v___x_2785_; 
lean_dec(v_v_2703_);
lean_dec(v_u_2702_);
v___x_2783_ = lean_box(0);
if (v_isShared_2780_ == 0)
{
lean_ctor_set(v___x_2779_, 0, v___x_2783_);
v___x_2785_ = v___x_2779_;
goto v_reusejp_2784_;
}
else
{
lean_object* v_reuseFailAlloc_2786_; 
v_reuseFailAlloc_2786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2786_, 0, v___x_2783_);
v___x_2785_ = v_reuseFailAlloc_2786_;
goto v_reusejp_2784_;
}
v_reusejp_2784_:
{
return v___x_2785_;
}
}
else
{
lean_object* v___x_2787_; 
lean_del_object(v___x_2779_);
v___x_2787_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_u_2702_, v_a_2705_, v_a_2706_, v_a_2714_);
if (lean_obj_tag(v___x_2787_) == 0)
{
lean_object* v_a_2788_; lean_object* v___x_2789_; 
v_a_2788_ = lean_ctor_get(v___x_2787_, 0);
lean_inc(v_a_2788_);
lean_dec_ref_known(v___x_2787_, 1);
v___x_2789_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_v_2703_, v_a_2705_, v_a_2706_, v_a_2714_);
if (lean_obj_tag(v___x_2789_) == 0)
{
lean_object* v_a_2790_; lean_object* v___y_2792_; lean_object* v___x_2866_; 
v_a_2790_ = lean_ctor_get(v___x_2789_, 0);
lean_inc(v_a_2790_);
lean_dec_ref_known(v___x_2789_, 1);
v___x_2866_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_a_2788_, v_a_2706_);
if (lean_obj_tag(v___x_2866_) == 0)
{
lean_object* v_a_2867_; uint8_t v___x_2868_; 
v_a_2867_ = lean_ctor_get(v___x_2866_, 0);
v___x_2868_ = lean_unbox(v_a_2867_);
if (v___x_2868_ == 0)
{
v___y_2792_ = v___x_2866_;
goto v___jp_2791_;
}
else
{
lean_object* v___x_2869_; 
lean_dec_ref_known(v___x_2866_, 1);
v___x_2869_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_a_2790_, v_a_2706_);
v___y_2792_ = v___x_2869_;
goto v___jp_2791_;
}
}
else
{
v___y_2792_ = v___x_2866_;
goto v___jp_2791_;
}
v___jp_2791_:
{
if (lean_obj_tag(v___y_2792_) == 0)
{
lean_object* v_a_2793_; uint8_t v___x_2794_; 
v_a_2793_ = lean_ctor_get(v___y_2792_, 0);
lean_inc(v_a_2793_);
lean_dec_ref_known(v___y_2792_, 1);
v___x_2794_ = lean_unbox(v_a_2793_);
lean_dec(v_a_2793_);
if (v___x_2794_ == 0)
{
lean_object* v___x_2795_; 
v___x_2795_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___redArg(v_a_2788_, v_a_2706_, v_a_2714_);
lean_dec(v_a_2788_);
if (lean_obj_tag(v___x_2795_) == 0)
{
lean_object* v_a_2796_; lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2828_; 
v_a_2796_ = lean_ctor_get(v___x_2795_, 0);
v_isSharedCheck_2828_ = !lean_is_exclusive(v___x_2795_);
if (v_isSharedCheck_2828_ == 0)
{
v___x_2798_ = v___x_2795_;
v_isShared_2799_ = v_isSharedCheck_2828_;
goto v_resetjp_2797_;
}
else
{
lean_inc(v_a_2796_);
lean_dec(v___x_2795_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2828_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
if (lean_obj_tag(v_a_2796_) == 1)
{
lean_object* v_val_2800_; lean_object* v___x_2801_; 
lean_del_object(v___x_2798_);
v_val_2800_ = lean_ctor_get(v_a_2796_, 0);
lean_inc(v_val_2800_);
lean_dec_ref_known(v_a_2796_, 1);
v___x_2801_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___redArg(v_a_2790_, v_a_2706_, v_a_2714_);
lean_dec(v_a_2790_);
if (lean_obj_tag(v___x_2801_) == 0)
{
lean_object* v_a_2802_; lean_object* v___x_2804_; uint8_t v_isShared_2805_; uint8_t v_isSharedCheck_2815_; 
v_a_2802_ = lean_ctor_get(v___x_2801_, 0);
v_isSharedCheck_2815_ = !lean_is_exclusive(v___x_2801_);
if (v_isSharedCheck_2815_ == 0)
{
v___x_2804_ = v___x_2801_;
v_isShared_2805_ = v_isSharedCheck_2815_;
goto v_resetjp_2803_;
}
else
{
lean_inc(v_a_2802_);
lean_dec(v___x_2801_);
v___x_2804_ = lean_box(0);
v_isShared_2805_ = v_isSharedCheck_2815_;
goto v_resetjp_2803_;
}
v_resetjp_2803_:
{
if (lean_obj_tag(v_a_2802_) == 1)
{
lean_object* v_val_2806_; lean_object* v___x_2807_; 
lean_del_object(v___x_2804_);
v_val_2806_ = lean_ctor_get(v_a_2802_, 0);
lean_inc(v_val_2806_);
lean_dec_ref_known(v_a_2802_, 1);
v___x_2807_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_val_2800_, v_a_2706_);
if (lean_obj_tag(v___x_2807_) == 0)
{
lean_object* v_a_2808_; uint8_t v___x_2809_; 
v_a_2808_ = lean_ctor_get(v___x_2807_, 0);
v___x_2809_ = lean_unbox(v_a_2808_);
if (v___x_2809_ == 0)
{
v___y_2718_ = v_val_2806_;
v___y_2719_ = v_val_2800_;
v___y_2720_ = v___x_2807_;
goto v___jp_2717_;
}
else
{
lean_object* v___x_2810_; 
lean_dec_ref_known(v___x_2807_, 1);
v___x_2810_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_val_2806_, v_a_2706_);
v___y_2718_ = v_val_2806_;
v___y_2719_ = v_val_2800_;
v___y_2720_ = v___x_2810_;
goto v___jp_2717_;
}
}
else
{
v___y_2718_ = v_val_2806_;
v___y_2719_ = v_val_2800_;
v___y_2720_ = v___x_2807_;
goto v___jp_2717_;
}
}
else
{
lean_object* v___x_2811_; lean_object* v___x_2813_; 
lean_dec(v_a_2802_);
lean_dec(v_val_2800_);
lean_dec(v_v_2703_);
lean_dec(v_u_2702_);
v___x_2811_ = lean_box(0);
if (v_isShared_2805_ == 0)
{
lean_ctor_set(v___x_2804_, 0, v___x_2811_);
v___x_2813_ = v___x_2804_;
goto v_reusejp_2812_;
}
else
{
lean_object* v_reuseFailAlloc_2814_; 
v_reuseFailAlloc_2814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2814_, 0, v___x_2811_);
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
else
{
lean_object* v_a_2816_; lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2823_; 
lean_dec(v_val_2800_);
lean_dec(v_v_2703_);
lean_dec(v_u_2702_);
v_a_2816_ = lean_ctor_get(v___x_2801_, 0);
v_isSharedCheck_2823_ = !lean_is_exclusive(v___x_2801_);
if (v_isSharedCheck_2823_ == 0)
{
v___x_2818_ = v___x_2801_;
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
else
{
lean_inc(v_a_2816_);
lean_dec(v___x_2801_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
lean_object* v___x_2821_; 
if (v_isShared_2819_ == 0)
{
v___x_2821_ = v___x_2818_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v_a_2816_);
v___x_2821_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
return v___x_2821_;
}
}
}
}
else
{
lean_object* v___x_2824_; lean_object* v___x_2826_; 
lean_dec(v_a_2796_);
lean_dec(v_a_2790_);
lean_dec(v_v_2703_);
lean_dec(v_u_2702_);
v___x_2824_ = lean_box(0);
if (v_isShared_2799_ == 0)
{
lean_ctor_set(v___x_2798_, 0, v___x_2824_);
v___x_2826_ = v___x_2798_;
goto v_reusejp_2825_;
}
else
{
lean_object* v_reuseFailAlloc_2827_; 
v_reuseFailAlloc_2827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2827_, 0, v___x_2824_);
v___x_2826_ = v_reuseFailAlloc_2827_;
goto v_reusejp_2825_;
}
v_reusejp_2825_:
{
return v___x_2826_;
}
}
}
}
else
{
lean_object* v_a_2829_; lean_object* v___x_2831_; uint8_t v_isShared_2832_; uint8_t v_isSharedCheck_2836_; 
lean_dec(v_a_2790_);
lean_dec(v_v_2703_);
lean_dec(v_u_2702_);
v_a_2829_ = lean_ctor_get(v___x_2795_, 0);
v_isSharedCheck_2836_ = !lean_is_exclusive(v___x_2795_);
if (v_isSharedCheck_2836_ == 0)
{
v___x_2831_ = v___x_2795_;
v_isShared_2832_ = v_isSharedCheck_2836_;
goto v_resetjp_2830_;
}
else
{
lean_inc(v_a_2829_);
lean_dec(v___x_2795_);
v___x_2831_ = lean_box(0);
v_isShared_2832_ = v_isSharedCheck_2836_;
goto v_resetjp_2830_;
}
v_resetjp_2830_:
{
lean_object* v___x_2834_; 
if (v_isShared_2832_ == 0)
{
v___x_2834_ = v___x_2831_;
goto v_reusejp_2833_;
}
else
{
lean_object* v_reuseFailAlloc_2835_; 
v_reuseFailAlloc_2835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2835_, 0, v_a_2829_);
v___x_2834_ = v_reuseFailAlloc_2835_;
goto v_reusejp_2833_;
}
v_reusejp_2833_:
{
return v___x_2834_;
}
}
}
}
else
{
lean_object* v___x_2837_; 
v___x_2837_ = l_Lean_Meta_Grind_isEqv___redArg(v_a_2788_, v_a_2790_, v_a_2706_);
lean_dec(v_a_2790_);
lean_dec(v_a_2788_);
if (lean_obj_tag(v___x_2837_) == 0)
{
lean_object* v_a_2838_; lean_object* v___x_2840_; uint8_t v_isShared_2841_; uint8_t v_isSharedCheck_2849_; 
v_a_2838_ = lean_ctor_get(v___x_2837_, 0);
v_isSharedCheck_2849_ = !lean_is_exclusive(v___x_2837_);
if (v_isSharedCheck_2849_ == 0)
{
v___x_2840_ = v___x_2837_;
v_isShared_2841_ = v_isSharedCheck_2849_;
goto v_resetjp_2839_;
}
else
{
lean_inc(v_a_2838_);
lean_dec(v___x_2837_);
v___x_2840_ = lean_box(0);
v_isShared_2841_ = v_isSharedCheck_2849_;
goto v_resetjp_2839_;
}
v_resetjp_2839_:
{
uint8_t v___x_2842_; 
v___x_2842_ = lean_unbox(v_a_2838_);
lean_dec(v_a_2838_);
if (v___x_2842_ == 0)
{
lean_object* v___x_2843_; lean_object* v___x_2844_; 
lean_del_object(v___x_2840_);
v___x_2843_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2843_, 0, v_u_2702_);
lean_ctor_set(v___x_2843_, 1, v_v_2703_);
v___x_2844_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate(v___x_2843_, v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_, v_a_2715_);
return v___x_2844_;
}
else
{
lean_object* v___x_2845_; lean_object* v___x_2847_; 
lean_dec(v_v_2703_);
lean_dec(v_u_2702_);
v___x_2845_ = lean_box(0);
if (v_isShared_2841_ == 0)
{
lean_ctor_set(v___x_2840_, 0, v___x_2845_);
v___x_2847_ = v___x_2840_;
goto v_reusejp_2846_;
}
else
{
lean_object* v_reuseFailAlloc_2848_; 
v_reuseFailAlloc_2848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2848_, 0, v___x_2845_);
v___x_2847_ = v_reuseFailAlloc_2848_;
goto v_reusejp_2846_;
}
v_reusejp_2846_:
{
return v___x_2847_;
}
}
}
}
else
{
lean_object* v_a_2850_; lean_object* v___x_2852_; uint8_t v_isShared_2853_; uint8_t v_isSharedCheck_2857_; 
lean_dec(v_v_2703_);
lean_dec(v_u_2702_);
v_a_2850_ = lean_ctor_get(v___x_2837_, 0);
v_isSharedCheck_2857_ = !lean_is_exclusive(v___x_2837_);
if (v_isSharedCheck_2857_ == 0)
{
v___x_2852_ = v___x_2837_;
v_isShared_2853_ = v_isSharedCheck_2857_;
goto v_resetjp_2851_;
}
else
{
lean_inc(v_a_2850_);
lean_dec(v___x_2837_);
v___x_2852_ = lean_box(0);
v_isShared_2853_ = v_isSharedCheck_2857_;
goto v_resetjp_2851_;
}
v_resetjp_2851_:
{
lean_object* v___x_2855_; 
if (v_isShared_2853_ == 0)
{
v___x_2855_ = v___x_2852_;
goto v_reusejp_2854_;
}
else
{
lean_object* v_reuseFailAlloc_2856_; 
v_reuseFailAlloc_2856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2856_, 0, v_a_2850_);
v___x_2855_ = v_reuseFailAlloc_2856_;
goto v_reusejp_2854_;
}
v_reusejp_2854_:
{
return v___x_2855_;
}
}
}
}
}
else
{
lean_object* v_a_2858_; lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_2865_; 
lean_dec(v_a_2790_);
lean_dec(v_a_2788_);
lean_dec(v_v_2703_);
lean_dec(v_u_2702_);
v_a_2858_ = lean_ctor_get(v___y_2792_, 0);
v_isSharedCheck_2865_ = !lean_is_exclusive(v___y_2792_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2860_ = v___y_2792_;
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
else
{
lean_inc(v_a_2858_);
lean_dec(v___y_2792_);
v___x_2860_ = lean_box(0);
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
v_resetjp_2859_:
{
lean_object* v___x_2863_; 
if (v_isShared_2861_ == 0)
{
v___x_2863_ = v___x_2860_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2864_; 
v_reuseFailAlloc_2864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2864_, 0, v_a_2858_);
v___x_2863_ = v_reuseFailAlloc_2864_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
return v___x_2863_;
}
}
}
}
}
else
{
lean_object* v_a_2870_; lean_object* v___x_2872_; uint8_t v_isShared_2873_; uint8_t v_isSharedCheck_2877_; 
lean_dec(v_a_2788_);
lean_dec(v_v_2703_);
lean_dec(v_u_2702_);
v_a_2870_ = lean_ctor_get(v___x_2789_, 0);
v_isSharedCheck_2877_ = !lean_is_exclusive(v___x_2789_);
if (v_isSharedCheck_2877_ == 0)
{
v___x_2872_ = v___x_2789_;
v_isShared_2873_ = v_isSharedCheck_2877_;
goto v_resetjp_2871_;
}
else
{
lean_inc(v_a_2870_);
lean_dec(v___x_2789_);
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
else
{
lean_object* v_a_2878_; lean_object* v___x_2880_; uint8_t v_isShared_2881_; uint8_t v_isSharedCheck_2885_; 
lean_dec(v_v_2703_);
lean_dec(v_u_2702_);
v_a_2878_ = lean_ctor_get(v___x_2787_, 0);
v_isSharedCheck_2885_ = !lean_is_exclusive(v___x_2787_);
if (v_isSharedCheck_2885_ == 0)
{
v___x_2880_ = v___x_2787_;
v_isShared_2881_ = v_isSharedCheck_2885_;
goto v_resetjp_2879_;
}
else
{
lean_inc(v_a_2878_);
lean_dec(v___x_2787_);
v___x_2880_ = lean_box(0);
v_isShared_2881_ = v_isSharedCheck_2885_;
goto v_resetjp_2879_;
}
v_resetjp_2879_:
{
lean_object* v___x_2883_; 
if (v_isShared_2881_ == 0)
{
v___x_2883_ = v___x_2880_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v_a_2878_);
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
}
else
{
lean_object* v___x_2886_; lean_object* v___x_2888_; 
lean_dec(v_a_2777_);
lean_dec(v_v_2703_);
lean_dec(v_u_2702_);
v___x_2886_ = lean_box(0);
if (v_isShared_2780_ == 0)
{
lean_ctor_set(v___x_2779_, 0, v___x_2886_);
v___x_2888_ = v___x_2779_;
goto v_reusejp_2887_;
}
else
{
lean_object* v_reuseFailAlloc_2889_; 
v_reuseFailAlloc_2889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2889_, 0, v___x_2886_);
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
else
{
lean_object* v_a_2891_; lean_object* v___x_2893_; uint8_t v_isShared_2894_; uint8_t v_isSharedCheck_2898_; 
lean_dec(v_v_2703_);
lean_dec(v_u_2702_);
v_a_2891_ = lean_ctor_get(v___x_2776_, 0);
v_isSharedCheck_2898_ = !lean_is_exclusive(v___x_2776_);
if (v_isSharedCheck_2898_ == 0)
{
v___x_2893_ = v___x_2776_;
v_isShared_2894_ = v_isSharedCheck_2898_;
goto v_resetjp_2892_;
}
else
{
lean_inc(v_a_2891_);
lean_dec(v___x_2776_);
v___x_2893_ = lean_box(0);
v_isShared_2894_ = v_isSharedCheck_2898_;
goto v_resetjp_2892_;
}
v_resetjp_2892_:
{
lean_object* v___x_2896_; 
if (v_isShared_2894_ == 0)
{
v___x_2896_ = v___x_2893_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2897_; 
v_reuseFailAlloc_2897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2897_, 0, v_a_2891_);
v___x_2896_ = v_reuseFailAlloc_2897_;
goto v_reusejp_2895_;
}
v_reusejp_2895_:
{
return v___x_2896_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2900_; lean_object* v___x_2902_; uint8_t v_isShared_2903_; uint8_t v_isSharedCheck_2907_; 
lean_dec(v_v_2703_);
lean_dec(v_u_2702_);
v_a_2900_ = lean_ctor_get(v___x_2761_, 0);
v_isSharedCheck_2907_ = !lean_is_exclusive(v___x_2761_);
if (v_isSharedCheck_2907_ == 0)
{
v___x_2902_ = v___x_2761_;
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
else
{
lean_inc(v_a_2900_);
lean_dec(v___x_2761_);
v___x_2902_ = lean_box(0);
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
v_resetjp_2901_:
{
lean_object* v___x_2905_; 
if (v_isShared_2903_ == 0)
{
v___x_2905_ = v___x_2902_;
goto v_reusejp_2904_;
}
else
{
lean_object* v_reuseFailAlloc_2906_; 
v_reuseFailAlloc_2906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2906_, 0, v_a_2900_);
v___x_2905_ = v_reuseFailAlloc_2906_;
goto v_reusejp_2904_;
}
v_reusejp_2904_:
{
return v___x_2905_;
}
}
}
}
else
{
lean_object* v___x_2908_; lean_object* v___x_2909_; 
lean_dec(v_v_2703_);
lean_dec(v_u_2702_);
v___x_2908_ = lean_box(0);
v___x_2909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2909_, 0, v___x_2908_);
return v___x_2909_;
}
v___jp_2717_:
{
if (lean_obj_tag(v___y_2720_) == 0)
{
lean_object* v_a_2721_; lean_object* v___x_2723_; uint8_t v_isShared_2724_; uint8_t v_isSharedCheck_2751_; 
v_a_2721_ = lean_ctor_get(v___y_2720_, 0);
v_isSharedCheck_2751_ = !lean_is_exclusive(v___y_2720_);
if (v_isSharedCheck_2751_ == 0)
{
v___x_2723_ = v___y_2720_;
v_isShared_2724_ = v_isSharedCheck_2751_;
goto v_resetjp_2722_;
}
else
{
lean_inc(v_a_2721_);
lean_dec(v___y_2720_);
v___x_2723_ = lean_box(0);
v_isShared_2724_ = v_isSharedCheck_2751_;
goto v_resetjp_2722_;
}
v_resetjp_2722_:
{
uint8_t v___x_2725_; 
v___x_2725_ = lean_unbox(v_a_2721_);
lean_dec(v_a_2721_);
if (v___x_2725_ == 0)
{
lean_object* v___x_2726_; lean_object* v___x_2728_; 
lean_dec_ref(v___y_2719_);
lean_dec_ref(v___y_2718_);
lean_dec(v_v_2703_);
lean_dec(v_u_2702_);
v___x_2726_ = lean_box(0);
if (v_isShared_2724_ == 0)
{
lean_ctor_set(v___x_2723_, 0, v___x_2726_);
v___x_2728_ = v___x_2723_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2729_; 
v_reuseFailAlloc_2729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2729_, 0, v___x_2726_);
v___x_2728_ = v_reuseFailAlloc_2729_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
return v___x_2728_;
}
}
else
{
lean_object* v___x_2730_; 
lean_del_object(v___x_2723_);
v___x_2730_ = l_Lean_Meta_Grind_isEqv___redArg(v___y_2719_, v___y_2718_, v_a_2706_);
lean_dec_ref(v___y_2718_);
lean_dec_ref(v___y_2719_);
if (lean_obj_tag(v___x_2730_) == 0)
{
lean_object* v_a_2731_; lean_object* v___x_2733_; uint8_t v_isShared_2734_; uint8_t v_isSharedCheck_2742_; 
v_a_2731_ = lean_ctor_get(v___x_2730_, 0);
v_isSharedCheck_2742_ = !lean_is_exclusive(v___x_2730_);
if (v_isSharedCheck_2742_ == 0)
{
v___x_2733_ = v___x_2730_;
v_isShared_2734_ = v_isSharedCheck_2742_;
goto v_resetjp_2732_;
}
else
{
lean_inc(v_a_2731_);
lean_dec(v___x_2730_);
v___x_2733_ = lean_box(0);
v_isShared_2734_ = v_isSharedCheck_2742_;
goto v_resetjp_2732_;
}
v_resetjp_2732_:
{
uint8_t v___x_2735_; 
v___x_2735_ = lean_unbox(v_a_2731_);
lean_dec(v_a_2731_);
if (v___x_2735_ == 0)
{
lean_object* v___x_2736_; lean_object* v___x_2737_; 
lean_del_object(v___x_2733_);
v___x_2736_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2736_, 0, v_u_2702_);
lean_ctor_set(v___x_2736_, 1, v_v_2703_);
v___x_2737_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate(v___x_2736_, v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_, v_a_2715_);
return v___x_2737_;
}
else
{
lean_object* v___x_2738_; lean_object* v___x_2740_; 
lean_dec(v_v_2703_);
lean_dec(v_u_2702_);
v___x_2738_ = lean_box(0);
if (v_isShared_2734_ == 0)
{
lean_ctor_set(v___x_2733_, 0, v___x_2738_);
v___x_2740_ = v___x_2733_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v___x_2738_);
v___x_2740_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
return v___x_2740_;
}
}
}
}
else
{
lean_object* v_a_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2750_; 
lean_dec(v_v_2703_);
lean_dec(v_u_2702_);
v_a_2743_ = lean_ctor_get(v___x_2730_, 0);
v_isSharedCheck_2750_ = !lean_is_exclusive(v___x_2730_);
if (v_isSharedCheck_2750_ == 0)
{
v___x_2745_ = v___x_2730_;
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_a_2743_);
lean_dec(v___x_2730_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
lean_object* v___x_2748_; 
if (v_isShared_2746_ == 0)
{
v___x_2748_ = v___x_2745_;
goto v_reusejp_2747_;
}
else
{
lean_object* v_reuseFailAlloc_2749_; 
v_reuseFailAlloc_2749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2749_, 0, v_a_2743_);
v___x_2748_ = v_reuseFailAlloc_2749_;
goto v_reusejp_2747_;
}
v_reusejp_2747_:
{
return v___x_2748_;
}
}
}
}
}
}
else
{
lean_object* v_a_2752_; lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2759_; 
lean_dec_ref(v___y_2719_);
lean_dec_ref(v___y_2718_);
lean_dec(v_v_2703_);
lean_dec(v_u_2702_);
v_a_2752_ = lean_ctor_get(v___y_2720_, 0);
v_isSharedCheck_2759_ = !lean_is_exclusive(v___y_2720_);
if (v_isSharedCheck_2759_ == 0)
{
v___x_2754_ = v___y_2720_;
v_isShared_2755_ = v_isSharedCheck_2759_;
goto v_resetjp_2753_;
}
else
{
lean_inc(v_a_2752_);
lean_dec(v___y_2720_);
v___x_2754_ = lean_box(0);
v_isShared_2755_ = v_isSharedCheck_2759_;
goto v_resetjp_2753_;
}
v_resetjp_2753_:
{
lean_object* v___x_2757_; 
if (v_isShared_2755_ == 0)
{
v___x_2757_ = v___x_2754_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v_a_2752_);
v___x_2757_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
return v___x_2757_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq___boxed(lean_object* v_u_2910_, lean_object* v_v_2911_, lean_object* v_k_2912_, lean_object* v_a_2913_, lean_object* v_a_2914_, lean_object* v_a_2915_, lean_object* v_a_2916_, lean_object* v_a_2917_, lean_object* v_a_2918_, lean_object* v_a_2919_, lean_object* v_a_2920_, lean_object* v_a_2921_, lean_object* v_a_2922_, lean_object* v_a_2923_, lean_object* v_a_2924_){
_start:
{
lean_object* v_res_2925_; 
v_res_2925_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq(v_u_2910_, v_v_2911_, v_k_2912_, v_a_2913_, v_a_2914_, v_a_2915_, v_a_2916_, v_a_2917_, v_a_2918_, v_a_2919_, v_a_2920_, v_a_2921_, v_a_2922_, v_a_2923_);
lean_dec(v_a_2923_);
lean_dec_ref(v_a_2922_);
lean_dec(v_a_2921_);
lean_dec_ref(v_a_2920_);
lean_dec(v_a_2919_);
lean_dec_ref(v_a_2918_);
lean_dec(v_a_2917_);
lean_dec_ref(v_a_2916_);
lean_dec(v_a_2915_);
lean_dec(v_a_2914_);
lean_dec(v_a_2913_);
lean_dec_ref(v_k_2912_);
return v_res_2925_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_2926_, lean_object* v_vals_2927_, lean_object* v_i_2928_, lean_object* v_k_2929_){
_start:
{
lean_object* v___x_2934_; uint8_t v___x_2935_; 
v___x_2934_ = lean_array_get_size(v_keys_2926_);
v___x_2935_ = lean_nat_dec_lt(v_i_2928_, v___x_2934_);
if (v___x_2935_ == 0)
{
lean_object* v___x_2936_; 
lean_dec(v_i_2928_);
v___x_2936_ = lean_box(0);
return v___x_2936_;
}
else
{
lean_object* v_fst_2937_; lean_object* v_snd_2938_; lean_object* v_k_x27_2939_; lean_object* v_fst_2940_; lean_object* v_snd_2941_; uint8_t v___x_2942_; 
v_fst_2937_ = lean_ctor_get(v_k_2929_, 0);
v_snd_2938_ = lean_ctor_get(v_k_2929_, 1);
v_k_x27_2939_ = lean_array_fget_borrowed(v_keys_2926_, v_i_2928_);
v_fst_2940_ = lean_ctor_get(v_k_x27_2939_, 0);
v_snd_2941_ = lean_ctor_get(v_k_x27_2939_, 1);
v___x_2942_ = lean_nat_dec_eq(v_fst_2937_, v_fst_2940_);
if (v___x_2942_ == 0)
{
goto v___jp_2930_;
}
else
{
uint8_t v___x_2943_; 
v___x_2943_ = lean_nat_dec_eq(v_snd_2938_, v_snd_2941_);
if (v___x_2943_ == 0)
{
goto v___jp_2930_;
}
else
{
lean_object* v___x_2944_; lean_object* v___x_2945_; 
v___x_2944_ = lean_array_fget_borrowed(v_vals_2927_, v_i_2928_);
lean_dec(v_i_2928_);
lean_inc(v___x_2944_);
v___x_2945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2945_, 0, v___x_2944_);
return v___x_2945_;
}
}
}
v___jp_2930_:
{
lean_object* v___x_2931_; lean_object* v___x_2932_; 
v___x_2931_ = lean_unsigned_to_nat(1u);
v___x_2932_ = lean_nat_add(v_i_2928_, v___x_2931_);
lean_dec(v_i_2928_);
v_i_2928_ = v___x_2932_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_2946_, lean_object* v_vals_2947_, lean_object* v_i_2948_, lean_object* v_k_2949_){
_start:
{
lean_object* v_res_2950_; 
v_res_2950_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1___redArg(v_keys_2946_, v_vals_2947_, v_i_2948_, v_k_2949_);
lean_dec_ref(v_k_2949_);
lean_dec_ref(v_vals_2947_);
lean_dec_ref(v_keys_2946_);
return v_res_2950_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0___redArg(lean_object* v_x_2951_, size_t v_x_2952_, lean_object* v_x_2953_){
_start:
{
if (lean_obj_tag(v_x_2951_) == 0)
{
lean_object* v_es_2954_; lean_object* v___x_2955_; size_t v___x_2956_; size_t v___x_2957_; lean_object* v_j_2958_; lean_object* v___x_2959_; 
v_es_2954_ = lean_ctor_get(v_x_2951_, 0);
v___x_2955_ = lean_box(2);
v___x_2956_ = ((size_t)31ULL);
v___x_2957_ = lean_usize_land(v_x_2952_, v___x_2956_);
v_j_2958_ = lean_usize_to_nat(v___x_2957_);
v___x_2959_ = lean_array_get_borrowed(v___x_2955_, v_es_2954_, v_j_2958_);
lean_dec(v_j_2958_);
switch(lean_obj_tag(v___x_2959_))
{
case 0:
{
lean_object* v_key_2960_; lean_object* v_val_2961_; lean_object* v_fst_2962_; lean_object* v_snd_2963_; lean_object* v_fst_2964_; lean_object* v_snd_2965_; uint8_t v___x_2966_; 
v_key_2960_ = lean_ctor_get(v___x_2959_, 0);
v_val_2961_ = lean_ctor_get(v___x_2959_, 1);
v_fst_2962_ = lean_ctor_get(v_x_2953_, 0);
v_snd_2963_ = lean_ctor_get(v_x_2953_, 1);
v_fst_2964_ = lean_ctor_get(v_key_2960_, 0);
v_snd_2965_ = lean_ctor_get(v_key_2960_, 1);
v___x_2966_ = lean_nat_dec_eq(v_fst_2962_, v_fst_2964_);
if (v___x_2966_ == 0)
{
lean_object* v___x_2967_; 
v___x_2967_ = lean_box(0);
return v___x_2967_;
}
else
{
uint8_t v___x_2968_; 
v___x_2968_ = lean_nat_dec_eq(v_snd_2963_, v_snd_2965_);
if (v___x_2968_ == 0)
{
lean_object* v___x_2969_; 
v___x_2969_ = lean_box(0);
return v___x_2969_;
}
else
{
lean_object* v___x_2970_; 
lean_inc(v_val_2961_);
v___x_2970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2970_, 0, v_val_2961_);
return v___x_2970_;
}
}
}
case 1:
{
lean_object* v_node_2971_; size_t v___x_2972_; size_t v___x_2973_; 
v_node_2971_ = lean_ctor_get(v___x_2959_, 0);
v___x_2972_ = ((size_t)5ULL);
v___x_2973_ = lean_usize_shift_right(v_x_2952_, v___x_2972_);
v_x_2951_ = v_node_2971_;
v_x_2952_ = v___x_2973_;
goto _start;
}
default: 
{
lean_object* v___x_2975_; 
v___x_2975_ = lean_box(0);
return v___x_2975_;
}
}
}
else
{
lean_object* v_ks_2976_; lean_object* v_vs_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; 
v_ks_2976_ = lean_ctor_get(v_x_2951_, 0);
v_vs_2977_ = lean_ctor_get(v_x_2951_, 1);
v___x_2978_ = lean_unsigned_to_nat(0u);
v___x_2979_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1___redArg(v_ks_2976_, v_vs_2977_, v___x_2978_, v_x_2953_);
return v___x_2979_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0___redArg___boxed(lean_object* v_x_2980_, lean_object* v_x_2981_, lean_object* v_x_2982_){
_start:
{
size_t v_x_3989__boxed_2983_; lean_object* v_res_2984_; 
v_x_3989__boxed_2983_ = lean_unbox_usize(v_x_2981_);
lean_dec(v_x_2981_);
v_res_2984_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0___redArg(v_x_2980_, v_x_3989__boxed_2983_, v_x_2982_);
lean_dec_ref(v_x_2982_);
lean_dec_ref(v_x_2980_);
return v_res_2984_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0___redArg(lean_object* v_x_2985_, lean_object* v_x_2986_){
_start:
{
lean_object* v_fst_2987_; lean_object* v_snd_2988_; uint64_t v___x_2989_; uint64_t v___x_2990_; uint64_t v___x_2991_; size_t v___x_2992_; lean_object* v___x_2993_; 
v_fst_2987_ = lean_ctor_get(v_x_2986_, 0);
v_snd_2988_ = lean_ctor_get(v_x_2986_, 1);
v___x_2989_ = lean_uint64_of_nat(v_fst_2987_);
v___x_2990_ = lean_uint64_of_nat(v_snd_2988_);
v___x_2991_ = lean_uint64_mix_hash(v___x_2989_, v___x_2990_);
v___x_2992_ = lean_uint64_to_usize(v___x_2991_);
v___x_2993_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0___redArg(v_x_2985_, v___x_2992_, v_x_2986_);
return v___x_2993_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0___redArg___boxed(lean_object* v_x_2994_, lean_object* v_x_2995_){
_start:
{
lean_object* v_res_2996_; 
v_res_2996_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0___redArg(v_x_2994_, v_x_2995_);
lean_dec_ref(v_x_2995_);
lean_dec_ref(v_x_2994_);
return v_res_2996_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__1(lean_object* v_u_2997_, lean_object* v_v_2998_, lean_object* v_k_2999_, lean_object* v_as_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_){
_start:
{
if (lean_obj_tag(v_as_3000_) == 0)
{
lean_object* v___x_3013_; lean_object* v___x_3014_; 
lean_dec_ref(v_k_2999_);
lean_dec(v_v_2998_);
lean_dec(v_u_2997_);
v___x_3013_ = lean_box(0);
v___x_3014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3014_, 0, v___x_3013_);
return v___x_3014_;
}
else
{
lean_object* v_head_3015_; lean_object* v_tail_3016_; lean_object* v_fst_3017_; lean_object* v_snd_3018_; lean_object* v___x_3019_; 
v_head_3015_ = lean_ctor_get(v_as_3000_, 0);
lean_inc(v_head_3015_);
v_tail_3016_ = lean_ctor_get(v_as_3000_, 1);
lean_inc(v_tail_3016_);
lean_dec_ref_known(v_as_3000_, 2);
v_fst_3017_ = lean_ctor_get(v_head_3015_, 0);
lean_inc(v_fst_3017_);
v_snd_3018_ = lean_ctor_get(v_head_3015_, 1);
lean_inc(v_snd_3018_);
lean_dec(v_head_3015_);
lean_inc_ref(v_k_2999_);
lean_inc(v_v_2998_);
lean_inc(v_u_2997_);
v___x_3019_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse(v_u_2997_, v_v_2998_, v_k_2999_, v_fst_3017_, v_snd_3018_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_, v___y_3011_);
if (lean_obj_tag(v___x_3019_) == 0)
{
lean_dec_ref_known(v___x_3019_, 1);
v_as_3000_ = v_tail_3016_;
goto _start;
}
else
{
lean_dec(v_tail_3016_);
lean_dec_ref(v_k_2999_);
lean_dec(v_v_2998_);
lean_dec(v_u_2997_);
return v___x_3019_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__1___boxed(lean_object* v_u_3021_, lean_object* v_v_3022_, lean_object* v_k_3023_, lean_object* v_as_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_){
_start:
{
lean_object* v_res_3037_; 
v_res_3037_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__1(v_u_3021_, v_v_3022_, v_k_3023_, v_as_3024_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_, v___y_3032_, v___y_3033_, v___y_3034_, v___y_3035_);
lean_dec(v___y_3035_);
lean_dec_ref(v___y_3034_);
lean_dec(v___y_3033_);
lean_dec_ref(v___y_3032_);
lean_dec(v___y_3031_);
lean_dec_ref(v___y_3030_);
lean_dec(v___y_3029_);
lean_dec_ref(v___y_3028_);
lean_dec(v___y_3027_);
lean_dec(v___y_3026_);
lean_dec(v___y_3025_);
return v_res_3037_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__2(lean_object* v_u_3038_, lean_object* v_v_3039_, lean_object* v_k_3040_, lean_object* v_as_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_){
_start:
{
if (lean_obj_tag(v_as_3041_) == 0)
{
lean_object* v___x_3054_; lean_object* v___x_3055_; 
lean_dec_ref(v_k_3040_);
lean_dec(v_v_3039_);
lean_dec(v_u_3038_);
v___x_3054_ = lean_box(0);
v___x_3055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3055_, 0, v___x_3054_);
return v___x_3055_;
}
else
{
lean_object* v_head_3056_; lean_object* v_tail_3057_; lean_object* v_fst_3058_; lean_object* v_snd_3059_; lean_object* v___x_3060_; 
v_head_3056_ = lean_ctor_get(v_as_3041_, 0);
lean_inc(v_head_3056_);
v_tail_3057_ = lean_ctor_get(v_as_3041_, 1);
lean_inc(v_tail_3057_);
lean_dec_ref_known(v_as_3041_, 2);
v_fst_3058_ = lean_ctor_get(v_head_3056_, 0);
lean_inc(v_fst_3058_);
v_snd_3059_ = lean_ctor_get(v_head_3056_, 1);
lean_inc(v_snd_3059_);
lean_dec(v_head_3056_);
lean_inc_ref(v_k_3040_);
lean_inc(v_v_3039_);
lean_inc(v_u_3038_);
v___x_3060_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue(v_u_3038_, v_v_3039_, v_k_3040_, v_fst_3058_, v_snd_3059_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_);
if (lean_obj_tag(v___x_3060_) == 0)
{
lean_dec_ref_known(v___x_3060_, 1);
v_as_3041_ = v_tail_3057_;
goto _start;
}
else
{
lean_dec(v_tail_3057_);
lean_dec_ref(v_k_3040_);
lean_dec(v_v_3039_);
lean_dec(v_u_3038_);
return v___x_3060_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__2___boxed(lean_object* v_u_3062_, lean_object* v_v_3063_, lean_object* v_k_3064_, lean_object* v_as_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_){
_start:
{
lean_object* v_res_3078_; 
v_res_3078_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__2(v_u_3062_, v_v_3063_, v_k_3064_, v_as_3065_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_);
lean_dec(v___y_3076_);
lean_dec_ref(v___y_3075_);
lean_dec(v___y_3074_);
lean_dec_ref(v___y_3073_);
lean_dec(v___y_3072_);
lean_dec_ref(v___y_3071_);
lean_dec(v___y_3070_);
lean_dec_ref(v___y_3069_);
lean_dec(v___y_3068_);
lean_dec(v___y_3067_);
lean_dec(v___y_3066_);
return v_res_3078_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate(lean_object* v_u_3079_, lean_object* v_v_3080_, lean_object* v_k_3081_, lean_object* v_a_3082_, lean_object* v_a_3083_, lean_object* v_a_3084_, lean_object* v_a_3085_, lean_object* v_a_3086_, lean_object* v_a_3087_, lean_object* v_a_3088_, lean_object* v_a_3089_, lean_object* v_a_3090_, lean_object* v_a_3091_, lean_object* v_a_3092_){
_start:
{
lean_object* v___x_3112_; 
v___x_3112_ = l_Lean_Meta_Grind_Order_getStruct___redArg(v_a_3082_, v_a_3083_, v_a_3091_);
if (lean_obj_tag(v___x_3112_) == 0)
{
lean_object* v_a_3113_; lean_object* v_cnstrsOf_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; 
v_a_3113_ = lean_ctor_get(v___x_3112_, 0);
lean_inc(v_a_3113_);
lean_dec_ref_known(v___x_3112_, 1);
v_cnstrsOf_3114_ = lean_ctor_get(v_a_3113_, 4);
lean_inc_ref(v_cnstrsOf_3114_);
lean_dec(v_a_3113_);
lean_inc(v_v_3080_);
lean_inc(v_u_3079_);
v___x_3115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3115_, 0, v_u_3079_);
lean_ctor_set(v___x_3115_, 1, v_v_3080_);
v___x_3116_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0___redArg(v_cnstrsOf_3114_, v___x_3115_);
lean_dec_ref_known(v___x_3115_, 2);
lean_dec_ref(v_cnstrsOf_3114_);
if (lean_obj_tag(v___x_3116_) == 1)
{
lean_object* v_val_3117_; lean_object* v___x_3118_; 
v_val_3117_ = lean_ctor_get(v___x_3116_, 0);
lean_inc(v_val_3117_);
lean_dec_ref_known(v___x_3116_, 1);
lean_inc_ref(v_k_3081_);
lean_inc(v_v_3080_);
lean_inc(v_u_3079_);
v___x_3118_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__2(v_u_3079_, v_v_3080_, v_k_3081_, v_val_3117_, v_a_3082_, v_a_3083_, v_a_3084_, v_a_3085_, v_a_3086_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_, v_a_3091_, v_a_3092_);
if (lean_obj_tag(v___x_3118_) == 0)
{
lean_dec_ref_known(v___x_3118_, 1);
goto v___jp_3094_;
}
else
{
lean_dec_ref(v_k_3081_);
lean_dec(v_v_3080_);
lean_dec(v_u_3079_);
return v___x_3118_;
}
}
else
{
lean_dec(v___x_3116_);
goto v___jp_3094_;
}
}
else
{
lean_object* v_a_3119_; lean_object* v___x_3121_; uint8_t v_isShared_3122_; uint8_t v_isSharedCheck_3126_; 
lean_dec_ref(v_k_3081_);
lean_dec(v_v_3080_);
lean_dec(v_u_3079_);
v_a_3119_ = lean_ctor_get(v___x_3112_, 0);
v_isSharedCheck_3126_ = !lean_is_exclusive(v___x_3112_);
if (v_isSharedCheck_3126_ == 0)
{
v___x_3121_ = v___x_3112_;
v_isShared_3122_ = v_isSharedCheck_3126_;
goto v_resetjp_3120_;
}
else
{
lean_inc(v_a_3119_);
lean_dec(v___x_3112_);
v___x_3121_ = lean_box(0);
v_isShared_3122_ = v_isSharedCheck_3126_;
goto v_resetjp_3120_;
}
v_resetjp_3120_:
{
lean_object* v___x_3124_; 
if (v_isShared_3122_ == 0)
{
v___x_3124_ = v___x_3121_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3125_; 
v_reuseFailAlloc_3125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3125_, 0, v_a_3119_);
v___x_3124_ = v_reuseFailAlloc_3125_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
return v___x_3124_;
}
}
}
v___jp_3094_:
{
lean_object* v___x_3095_; 
v___x_3095_ = l_Lean_Meta_Grind_Order_getStruct___redArg(v_a_3082_, v_a_3083_, v_a_3091_);
if (lean_obj_tag(v___x_3095_) == 0)
{
lean_object* v_a_3096_; lean_object* v_cnstrsOf_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; 
v_a_3096_ = lean_ctor_get(v___x_3095_, 0);
lean_inc(v_a_3096_);
lean_dec_ref_known(v___x_3095_, 1);
v_cnstrsOf_3097_ = lean_ctor_get(v_a_3096_, 4);
lean_inc_ref(v_cnstrsOf_3097_);
lean_dec(v_a_3096_);
lean_inc(v_u_3079_);
lean_inc(v_v_3080_);
v___x_3098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3098_, 0, v_v_3080_);
lean_ctor_set(v___x_3098_, 1, v_u_3079_);
v___x_3099_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0___redArg(v_cnstrsOf_3097_, v___x_3098_);
lean_dec_ref_known(v___x_3098_, 2);
lean_dec_ref(v_cnstrsOf_3097_);
if (lean_obj_tag(v___x_3099_) == 1)
{
lean_object* v_val_3100_; lean_object* v___x_3101_; 
v_val_3100_ = lean_ctor_get(v___x_3099_, 0);
lean_inc(v_val_3100_);
lean_dec_ref_known(v___x_3099_, 1);
lean_inc_ref(v_k_3081_);
lean_inc(v_v_3080_);
lean_inc(v_u_3079_);
v___x_3101_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__1(v_u_3079_, v_v_3080_, v_k_3081_, v_val_3100_, v_a_3082_, v_a_3083_, v_a_3084_, v_a_3085_, v_a_3086_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_, v_a_3091_, v_a_3092_);
if (lean_obj_tag(v___x_3101_) == 0)
{
lean_object* v___x_3102_; 
lean_dec_ref_known(v___x_3101_, 1);
v___x_3102_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq(v_u_3079_, v_v_3080_, v_k_3081_, v_a_3082_, v_a_3083_, v_a_3084_, v_a_3085_, v_a_3086_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_, v_a_3091_, v_a_3092_);
lean_dec_ref(v_k_3081_);
return v___x_3102_;
}
else
{
lean_dec_ref(v_k_3081_);
lean_dec(v_v_3080_);
lean_dec(v_u_3079_);
return v___x_3101_;
}
}
else
{
lean_object* v___x_3103_; 
lean_dec(v___x_3099_);
v___x_3103_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq(v_u_3079_, v_v_3080_, v_k_3081_, v_a_3082_, v_a_3083_, v_a_3084_, v_a_3085_, v_a_3086_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_, v_a_3091_, v_a_3092_);
lean_dec_ref(v_k_3081_);
return v___x_3103_;
}
}
else
{
lean_object* v_a_3104_; lean_object* v___x_3106_; uint8_t v_isShared_3107_; uint8_t v_isSharedCheck_3111_; 
lean_dec_ref(v_k_3081_);
lean_dec(v_v_3080_);
lean_dec(v_u_3079_);
v_a_3104_ = lean_ctor_get(v___x_3095_, 0);
v_isSharedCheck_3111_ = !lean_is_exclusive(v___x_3095_);
if (v_isSharedCheck_3111_ == 0)
{
v___x_3106_ = v___x_3095_;
v_isShared_3107_ = v_isSharedCheck_3111_;
goto v_resetjp_3105_;
}
else
{
lean_inc(v_a_3104_);
lean_dec(v___x_3095_);
v___x_3106_ = lean_box(0);
v_isShared_3107_ = v_isSharedCheck_3111_;
goto v_resetjp_3105_;
}
v_resetjp_3105_:
{
lean_object* v___x_3109_; 
if (v_isShared_3107_ == 0)
{
v___x_3109_ = v___x_3106_;
goto v_reusejp_3108_;
}
else
{
lean_object* v_reuseFailAlloc_3110_; 
v_reuseFailAlloc_3110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3110_, 0, v_a_3104_);
v___x_3109_ = v_reuseFailAlloc_3110_;
goto v_reusejp_3108_;
}
v_reusejp_3108_:
{
return v___x_3109_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate___boxed(lean_object* v_u_3127_, lean_object* v_v_3128_, lean_object* v_k_3129_, lean_object* v_a_3130_, lean_object* v_a_3131_, lean_object* v_a_3132_, lean_object* v_a_3133_, lean_object* v_a_3134_, lean_object* v_a_3135_, lean_object* v_a_3136_, lean_object* v_a_3137_, lean_object* v_a_3138_, lean_object* v_a_3139_, lean_object* v_a_3140_, lean_object* v_a_3141_){
_start:
{
lean_object* v_res_3142_; 
v_res_3142_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate(v_u_3127_, v_v_3128_, v_k_3129_, v_a_3130_, v_a_3131_, v_a_3132_, v_a_3133_, v_a_3134_, v_a_3135_, v_a_3136_, v_a_3137_, v_a_3138_, v_a_3139_, v_a_3140_);
lean_dec(v_a_3140_);
lean_dec_ref(v_a_3139_);
lean_dec(v_a_3138_);
lean_dec_ref(v_a_3137_);
lean_dec(v_a_3136_);
lean_dec_ref(v_a_3135_);
lean_dec(v_a_3134_);
lean_dec_ref(v_a_3133_);
lean_dec(v_a_3132_);
lean_dec(v_a_3131_);
lean_dec(v_a_3130_);
return v_res_3142_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0(lean_object* v_00_u03b2_3143_, lean_object* v_x_3144_, lean_object* v_x_3145_){
_start:
{
lean_object* v___x_3146_; 
v___x_3146_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0___redArg(v_x_3144_, v_x_3145_);
return v___x_3146_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0___boxed(lean_object* v_00_u03b2_3147_, lean_object* v_x_3148_, lean_object* v_x_3149_){
_start:
{
lean_object* v_res_3150_; 
v_res_3150_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0(v_00_u03b2_3147_, v_x_3148_, v_x_3149_);
lean_dec_ref(v_x_3149_);
lean_dec_ref(v_x_3148_);
return v_res_3150_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0(lean_object* v_00_u03b2_3151_, lean_object* v_x_3152_, size_t v_x_3153_, lean_object* v_x_3154_){
_start:
{
lean_object* v___x_3155_; 
v___x_3155_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0___redArg(v_x_3152_, v_x_3153_, v_x_3154_);
return v___x_3155_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3156_, lean_object* v_x_3157_, lean_object* v_x_3158_, lean_object* v_x_3159_){
_start:
{
size_t v_x_4253__boxed_3160_; lean_object* v_res_3161_; 
v_x_4253__boxed_3160_ = lean_unbox_usize(v_x_3158_);
lean_dec(v_x_3158_);
v_res_3161_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0(v_00_u03b2_3156_, v_x_3157_, v_x_4253__boxed_3160_, v_x_3159_);
lean_dec_ref(v_x_3159_);
lean_dec_ref(v_x_3157_);
return v_res_3161_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3162_, lean_object* v_keys_3163_, lean_object* v_vals_3164_, lean_object* v_heq_3165_, lean_object* v_i_3166_, lean_object* v_k_3167_){
_start:
{
lean_object* v___x_3168_; 
v___x_3168_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1___redArg(v_keys_3163_, v_vals_3164_, v_i_3166_, v_k_3167_);
return v___x_3168_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_3169_, lean_object* v_keys_3170_, lean_object* v_vals_3171_, lean_object* v_heq_3172_, lean_object* v_i_3173_, lean_object* v_k_3174_){
_start:
{
lean_object* v_res_3175_; 
v_res_3175_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1(v_00_u03b2_3169_, v_keys_3170_, v_vals_3171_, v_heq_3172_, v_i_3173_, v_k_3174_);
lean_dec_ref(v_k_3174_);
lean_dec_ref(v_vals_3171_);
lean_dec_ref(v_keys_3170_);
return v_res_3175_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_updateIfShorter(lean_object* v_u_3176_, lean_object* v_v_3177_, lean_object* v_k_3178_, lean_object* v_w_3179_, lean_object* v_a_3180_, lean_object* v_a_3181_, lean_object* v_a_3182_, lean_object* v_a_3183_, lean_object* v_a_3184_, lean_object* v_a_3185_, lean_object* v_a_3186_, lean_object* v_a_3187_, lean_object* v_a_3188_, lean_object* v_a_3189_, lean_object* v_a_3190_){
_start:
{
lean_object* v___x_3192_; 
v___x_3192_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isShorter___redArg(v_u_3176_, v_v_3177_, v_k_3178_, v_a_3180_, v_a_3181_, v_a_3189_);
if (lean_obj_tag(v___x_3192_) == 0)
{
lean_object* v_a_3193_; lean_object* v___x_3195_; uint8_t v_isShared_3196_; uint8_t v_isSharedCheck_3215_; 
v_a_3193_ = lean_ctor_get(v___x_3192_, 0);
v_isSharedCheck_3215_ = !lean_is_exclusive(v___x_3192_);
if (v_isSharedCheck_3215_ == 0)
{
v___x_3195_ = v___x_3192_;
v_isShared_3196_ = v_isSharedCheck_3215_;
goto v_resetjp_3194_;
}
else
{
lean_inc(v_a_3193_);
lean_dec(v___x_3192_);
v___x_3195_ = lean_box(0);
v_isShared_3196_ = v_isSharedCheck_3215_;
goto v_resetjp_3194_;
}
v_resetjp_3194_:
{
uint8_t v___x_3197_; 
v___x_3197_ = lean_unbox(v_a_3193_);
lean_dec(v_a_3193_);
if (v___x_3197_ == 0)
{
lean_object* v___x_3198_; lean_object* v___x_3200_; 
lean_dec_ref(v_k_3178_);
lean_dec(v_v_3177_);
lean_dec(v_u_3176_);
v___x_3198_ = lean_box(0);
if (v_isShared_3196_ == 0)
{
lean_ctor_set(v___x_3195_, 0, v___x_3198_);
v___x_3200_ = v___x_3195_;
goto v_reusejp_3199_;
}
else
{
lean_object* v_reuseFailAlloc_3201_; 
v_reuseFailAlloc_3201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3201_, 0, v___x_3198_);
v___x_3200_ = v_reuseFailAlloc_3201_;
goto v_reusejp_3199_;
}
v_reusejp_3199_:
{
return v___x_3200_;
}
}
else
{
lean_object* v___x_3202_; 
lean_del_object(v___x_3195_);
lean_inc_ref(v_k_3178_);
lean_inc(v_v_3177_);
lean_inc(v_u_3176_);
v___x_3202_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist___redArg(v_u_3176_, v_v_3177_, v_k_3178_, v_a_3180_, v_a_3181_);
if (lean_obj_tag(v___x_3202_) == 0)
{
lean_object* v___x_3203_; 
lean_dec_ref_known(v___x_3202_, 1);
v___x_3203_ = l_Lean_Meta_Grind_Order_getProof___redArg(v_w_3179_, v_v_3177_, v_a_3180_, v_a_3181_, v_a_3187_, v_a_3188_, v_a_3189_, v_a_3190_);
if (lean_obj_tag(v___x_3203_) == 0)
{
lean_object* v_a_3204_; lean_object* v___x_3205_; 
v_a_3204_ = lean_ctor_get(v___x_3203_, 0);
lean_inc(v_a_3204_);
lean_dec_ref_known(v___x_3203_, 1);
lean_inc(v_v_3177_);
lean_inc(v_u_3176_);
v___x_3205_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___redArg(v_u_3176_, v_v_3177_, v_a_3204_, v_a_3180_, v_a_3181_);
if (lean_obj_tag(v___x_3205_) == 0)
{
lean_object* v___x_3206_; 
lean_dec_ref_known(v___x_3205_, 1);
v___x_3206_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate(v_u_3176_, v_v_3177_, v_k_3178_, v_a_3180_, v_a_3181_, v_a_3182_, v_a_3183_, v_a_3184_, v_a_3185_, v_a_3186_, v_a_3187_, v_a_3188_, v_a_3189_, v_a_3190_);
return v___x_3206_;
}
else
{
lean_dec_ref(v_k_3178_);
lean_dec(v_v_3177_);
lean_dec(v_u_3176_);
return v___x_3205_;
}
}
else
{
lean_object* v_a_3207_; lean_object* v___x_3209_; uint8_t v_isShared_3210_; uint8_t v_isSharedCheck_3214_; 
lean_dec_ref(v_k_3178_);
lean_dec(v_v_3177_);
lean_dec(v_u_3176_);
v_a_3207_ = lean_ctor_get(v___x_3203_, 0);
v_isSharedCheck_3214_ = !lean_is_exclusive(v___x_3203_);
if (v_isSharedCheck_3214_ == 0)
{
v___x_3209_ = v___x_3203_;
v_isShared_3210_ = v_isSharedCheck_3214_;
goto v_resetjp_3208_;
}
else
{
lean_inc(v_a_3207_);
lean_dec(v___x_3203_);
v___x_3209_ = lean_box(0);
v_isShared_3210_ = v_isSharedCheck_3214_;
goto v_resetjp_3208_;
}
v_resetjp_3208_:
{
lean_object* v___x_3212_; 
if (v_isShared_3210_ == 0)
{
v___x_3212_ = v___x_3209_;
goto v_reusejp_3211_;
}
else
{
lean_object* v_reuseFailAlloc_3213_; 
v_reuseFailAlloc_3213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3213_, 0, v_a_3207_);
v___x_3212_ = v_reuseFailAlloc_3213_;
goto v_reusejp_3211_;
}
v_reusejp_3211_:
{
return v___x_3212_;
}
}
}
}
else
{
lean_dec_ref(v_k_3178_);
lean_dec(v_v_3177_);
lean_dec(v_u_3176_);
return v___x_3202_;
}
}
}
}
else
{
lean_object* v_a_3216_; lean_object* v___x_3218_; uint8_t v_isShared_3219_; uint8_t v_isSharedCheck_3223_; 
lean_dec_ref(v_k_3178_);
lean_dec(v_v_3177_);
lean_dec(v_u_3176_);
v_a_3216_ = lean_ctor_get(v___x_3192_, 0);
v_isSharedCheck_3223_ = !lean_is_exclusive(v___x_3192_);
if (v_isSharedCheck_3223_ == 0)
{
v___x_3218_ = v___x_3192_;
v_isShared_3219_ = v_isSharedCheck_3223_;
goto v_resetjp_3217_;
}
else
{
lean_inc(v_a_3216_);
lean_dec(v___x_3192_);
v___x_3218_ = lean_box(0);
v_isShared_3219_ = v_isSharedCheck_3223_;
goto v_resetjp_3217_;
}
v_resetjp_3217_:
{
lean_object* v___x_3221_; 
if (v_isShared_3219_ == 0)
{
v___x_3221_ = v___x_3218_;
goto v_reusejp_3220_;
}
else
{
lean_object* v_reuseFailAlloc_3222_; 
v_reuseFailAlloc_3222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3222_, 0, v_a_3216_);
v___x_3221_ = v_reuseFailAlloc_3222_;
goto v_reusejp_3220_;
}
v_reusejp_3220_:
{
return v___x_3221_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_updateIfShorter___boxed(lean_object* v_u_3224_, lean_object* v_v_3225_, lean_object* v_k_3226_, lean_object* v_w_3227_, lean_object* v_a_3228_, lean_object* v_a_3229_, lean_object* v_a_3230_, lean_object* v_a_3231_, lean_object* v_a_3232_, lean_object* v_a_3233_, lean_object* v_a_3234_, lean_object* v_a_3235_, lean_object* v_a_3236_, lean_object* v_a_3237_, lean_object* v_a_3238_, lean_object* v_a_3239_){
_start:
{
lean_object* v_res_3240_; 
v_res_3240_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_updateIfShorter(v_u_3224_, v_v_3225_, v_k_3226_, v_w_3227_, v_a_3228_, v_a_3229_, v_a_3230_, v_a_3231_, v_a_3232_, v_a_3233_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_, v_a_3238_);
lean_dec(v_a_3238_);
lean_dec_ref(v_a_3237_);
lean_dec(v_a_3236_);
lean_dec_ref(v_a_3235_);
lean_dec(v_a_3234_);
lean_dec_ref(v_a_3233_);
lean_dec(v_a_3232_);
lean_dec_ref(v_a_3231_);
lean_dec(v_a_3230_);
lean_dec(v_a_3229_);
lean_dec(v_a_3228_);
lean_dec(v_w_3227_);
return v_res_3240_;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0(lean_object* v___x_3241_, lean_object* v_i_3242_, lean_object* v_v_3243_, lean_object* v_x_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_){
_start:
{
if (lean_obj_tag(v_x_3244_) == 0)
{
lean_object* v___x_3257_; lean_object* v___x_3258_; 
lean_dec(v_i_3242_);
v___x_3257_ = lean_box(0);
v___x_3258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3258_, 0, v___x_3257_);
return v___x_3258_;
}
else
{
lean_object* v_key_3259_; lean_object* v_value_3260_; lean_object* v_tail_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; 
v_key_3259_ = lean_ctor_get(v_x_3244_, 0);
lean_inc(v_key_3259_);
v_value_3260_ = lean_ctor_get(v_x_3244_, 1);
lean_inc(v_value_3260_);
v_tail_3261_ = lean_ctor_get(v_x_3244_, 2);
lean_inc(v_tail_3261_);
lean_dec_ref_known(v_x_3244_, 3);
v___x_3262_ = l_Lean_Meta_Grind_Order_Weight_add(v___x_3241_, v_value_3260_);
lean_inc(v_i_3242_);
v___x_3263_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_updateIfShorter(v_i_3242_, v_key_3259_, v___x_3262_, v_v_3243_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_);
if (lean_obj_tag(v___x_3263_) == 0)
{
lean_dec_ref_known(v___x_3263_, 1);
v_x_3244_ = v_tail_3261_;
goto _start;
}
else
{
lean_dec(v_tail_3261_);
lean_dec(v_i_3242_);
return v___x_3263_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0___boxed(lean_object* v___x_3265_, lean_object* v_i_3266_, lean_object* v_v_3267_, lean_object* v_x_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_){
_start:
{
lean_object* v_res_3281_; 
v_res_3281_ = l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0(v___x_3265_, v_i_3266_, v_v_3267_, v_x_3268_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_);
lean_dec(v___y_3279_);
lean_dec_ref(v___y_3278_);
lean_dec(v___y_3277_);
lean_dec_ref(v___y_3276_);
lean_dec(v___y_3275_);
lean_dec_ref(v___y_3274_);
lean_dec(v___y_3273_);
lean_dec_ref(v___y_3272_);
lean_dec(v___y_3271_);
lean_dec(v___y_3270_);
lean_dec(v___y_3269_);
lean_dec(v_v_3267_);
lean_dec_ref(v___x_3265_);
return v_res_3281_;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__1(lean_object* v_k_3282_, lean_object* v_v_3283_, lean_object* v_u_3284_, lean_object* v_x_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_){
_start:
{
if (lean_obj_tag(v_x_3285_) == 0)
{
lean_object* v___x_3298_; lean_object* v___x_3299_; 
lean_dec(v_v_3283_);
lean_dec_ref(v_k_3282_);
v___x_3298_ = lean_box(0);
v___x_3299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3299_, 0, v___x_3298_);
return v___x_3299_;
}
else
{
lean_object* v_key_3300_; lean_object* v_value_3301_; lean_object* v_tail_3302_; lean_object* v___y_3304_; lean_object* v___x_3306_; lean_object* v___x_3307_; 
v_key_3300_ = lean_ctor_get(v_x_3285_, 0);
lean_inc_n(v_key_3300_, 2);
v_value_3301_ = lean_ctor_get(v_x_3285_, 1);
lean_inc(v_value_3301_);
v_tail_3302_ = lean_ctor_get(v_x_3285_, 2);
lean_inc(v_tail_3302_);
lean_dec_ref_known(v_x_3285_, 3);
lean_inc_ref(v_k_3282_);
v___x_3306_ = l_Lean_Meta_Grind_Order_Weight_add(v_value_3301_, v_k_3282_);
lean_dec(v_value_3301_);
lean_inc_ref(v___x_3306_);
lean_inc(v_v_3283_);
v___x_3307_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_updateIfShorter(v_key_3300_, v_v_3283_, v___x_3306_, v_u_3284_, v___y_3286_, v___y_3287_, v___y_3288_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_);
if (lean_obj_tag(v___x_3307_) == 0)
{
lean_object* v___x_3308_; lean_object* v___x_3309_; 
lean_dec_ref_known(v___x_3307_, 1);
v___x_3308_ = lean_box(0);
v___x_3309_ = l_Lean_Meta_Grind_Order_getStruct___redArg(v___y_3286_, v___y_3287_, v___y_3295_);
if (lean_obj_tag(v___x_3309_) == 0)
{
lean_object* v_a_3310_; lean_object* v_targets_3311_; lean_object* v_size_3312_; uint8_t v___x_3313_; 
v_a_3310_ = lean_ctor_get(v___x_3309_, 0);
lean_inc(v_a_3310_);
lean_dec_ref_known(v___x_3309_, 1);
v_targets_3311_ = lean_ctor_get(v_a_3310_, 6);
lean_inc_ref(v_targets_3311_);
lean_dec(v_a_3310_);
v_size_3312_ = lean_ctor_get(v_targets_3311_, 2);
v___x_3313_ = lean_nat_dec_lt(v_v_3283_, v_size_3312_);
if (v___x_3313_ == 0)
{
lean_object* v___x_3314_; lean_object* v___x_3315_; 
lean_dec_ref(v_targets_3311_);
v___x_3314_ = l_outOfBounds___redArg(v___x_3308_);
v___x_3315_ = l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0(v___x_3306_, v_key_3300_, v_v_3283_, v___x_3314_, v___y_3286_, v___y_3287_, v___y_3288_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_);
lean_dec_ref(v___x_3306_);
v___y_3304_ = v___x_3315_;
goto v___jp_3303_;
}
else
{
lean_object* v___x_3316_; lean_object* v___x_3317_; 
v___x_3316_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3308_, v_targets_3311_, v_v_3283_);
lean_dec_ref(v_targets_3311_);
v___x_3317_ = l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0(v___x_3306_, v_key_3300_, v_v_3283_, v___x_3316_, v___y_3286_, v___y_3287_, v___y_3288_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_);
lean_dec_ref(v___x_3306_);
v___y_3304_ = v___x_3317_;
goto v___jp_3303_;
}
}
else
{
lean_object* v_a_3318_; lean_object* v___x_3320_; uint8_t v_isShared_3321_; uint8_t v_isSharedCheck_3325_; 
lean_dec_ref(v___x_3306_);
lean_dec(v_tail_3302_);
lean_dec(v_key_3300_);
lean_dec(v_v_3283_);
lean_dec_ref(v_k_3282_);
v_a_3318_ = lean_ctor_get(v___x_3309_, 0);
v_isSharedCheck_3325_ = !lean_is_exclusive(v___x_3309_);
if (v_isSharedCheck_3325_ == 0)
{
v___x_3320_ = v___x_3309_;
v_isShared_3321_ = v_isSharedCheck_3325_;
goto v_resetjp_3319_;
}
else
{
lean_inc(v_a_3318_);
lean_dec(v___x_3309_);
v___x_3320_ = lean_box(0);
v_isShared_3321_ = v_isSharedCheck_3325_;
goto v_resetjp_3319_;
}
v_resetjp_3319_:
{
lean_object* v___x_3323_; 
if (v_isShared_3321_ == 0)
{
v___x_3323_ = v___x_3320_;
goto v_reusejp_3322_;
}
else
{
lean_object* v_reuseFailAlloc_3324_; 
v_reuseFailAlloc_3324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3324_, 0, v_a_3318_);
v___x_3323_ = v_reuseFailAlloc_3324_;
goto v_reusejp_3322_;
}
v_reusejp_3322_:
{
return v___x_3323_;
}
}
}
}
else
{
lean_dec_ref(v___x_3306_);
lean_dec(v_key_3300_);
v___y_3304_ = v___x_3307_;
goto v___jp_3303_;
}
v___jp_3303_:
{
if (lean_obj_tag(v___y_3304_) == 0)
{
lean_dec_ref_known(v___y_3304_, 1);
v_x_3285_ = v_tail_3302_;
goto _start;
}
else
{
lean_dec(v_tail_3302_);
lean_dec(v_v_3283_);
lean_dec_ref(v_k_3282_);
return v___y_3304_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__1___boxed(lean_object* v_k_3326_, lean_object* v_v_3327_, lean_object* v_u_3328_, lean_object* v_x_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_){
_start:
{
lean_object* v_res_3342_; 
v_res_3342_ = l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__1(v_k_3326_, v_v_3327_, v_u_3328_, v_x_3329_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_);
lean_dec(v___y_3340_);
lean_dec_ref(v___y_3339_);
lean_dec(v___y_3338_);
lean_dec_ref(v___y_3337_);
lean_dec(v___y_3336_);
lean_dec_ref(v___y_3335_);
lean_dec(v___y_3334_);
lean_dec_ref(v___y_3333_);
lean_dec(v___y_3332_);
lean_dec(v___y_3331_);
lean_dec(v___y_3330_);
lean_dec(v_u_3328_);
return v_res_3342_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update(lean_object* v_u_3343_, lean_object* v_v_3344_, lean_object* v_k_3345_, lean_object* v_a_3346_, lean_object* v_a_3347_, lean_object* v_a_3348_, lean_object* v_a_3349_, lean_object* v_a_3350_, lean_object* v_a_3351_, lean_object* v_a_3352_, lean_object* v_a_3353_, lean_object* v_a_3354_, lean_object* v_a_3355_, lean_object* v_a_3356_){
_start:
{
lean_object* v___y_3359_; lean_object* v___x_3378_; lean_object* v___x_3379_; 
v___x_3378_ = lean_box(0);
v___x_3379_ = l_Lean_Meta_Grind_Order_getStruct___redArg(v_a_3346_, v_a_3347_, v_a_3355_);
if (lean_obj_tag(v___x_3379_) == 0)
{
lean_object* v_a_3380_; lean_object* v_targets_3381_; lean_object* v_size_3382_; uint8_t v___x_3383_; 
v_a_3380_ = lean_ctor_get(v___x_3379_, 0);
lean_inc(v_a_3380_);
lean_dec_ref_known(v___x_3379_, 1);
v_targets_3381_ = lean_ctor_get(v_a_3380_, 6);
lean_inc_ref(v_targets_3381_);
lean_dec(v_a_3380_);
v_size_3382_ = lean_ctor_get(v_targets_3381_, 2);
v___x_3383_ = lean_nat_dec_lt(v_v_3344_, v_size_3382_);
if (v___x_3383_ == 0)
{
lean_object* v___x_3384_; lean_object* v___x_3385_; 
lean_dec_ref(v_targets_3381_);
v___x_3384_ = l_outOfBounds___redArg(v___x_3378_);
lean_inc(v_u_3343_);
v___x_3385_ = l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0(v_k_3345_, v_u_3343_, v_v_3344_, v___x_3384_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_, v_a_3353_, v_a_3354_, v_a_3355_, v_a_3356_);
v___y_3359_ = v___x_3385_;
goto v___jp_3358_;
}
else
{
lean_object* v___x_3386_; lean_object* v___x_3387_; 
v___x_3386_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3378_, v_targets_3381_, v_v_3344_);
lean_dec_ref(v_targets_3381_);
lean_inc(v_u_3343_);
v___x_3387_ = l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0(v_k_3345_, v_u_3343_, v_v_3344_, v___x_3386_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_, v_a_3353_, v_a_3354_, v_a_3355_, v_a_3356_);
v___y_3359_ = v___x_3387_;
goto v___jp_3358_;
}
}
else
{
lean_object* v_a_3388_; lean_object* v___x_3390_; uint8_t v_isShared_3391_; uint8_t v_isSharedCheck_3395_; 
lean_dec_ref(v_k_3345_);
lean_dec(v_v_3344_);
lean_dec(v_u_3343_);
v_a_3388_ = lean_ctor_get(v___x_3379_, 0);
v_isSharedCheck_3395_ = !lean_is_exclusive(v___x_3379_);
if (v_isSharedCheck_3395_ == 0)
{
v___x_3390_ = v___x_3379_;
v_isShared_3391_ = v_isSharedCheck_3395_;
goto v_resetjp_3389_;
}
else
{
lean_inc(v_a_3388_);
lean_dec(v___x_3379_);
v___x_3390_ = lean_box(0);
v_isShared_3391_ = v_isSharedCheck_3395_;
goto v_resetjp_3389_;
}
v_resetjp_3389_:
{
lean_object* v___x_3393_; 
if (v_isShared_3391_ == 0)
{
v___x_3393_ = v___x_3390_;
goto v_reusejp_3392_;
}
else
{
lean_object* v_reuseFailAlloc_3394_; 
v_reuseFailAlloc_3394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3394_, 0, v_a_3388_);
v___x_3393_ = v_reuseFailAlloc_3394_;
goto v_reusejp_3392_;
}
v_reusejp_3392_:
{
return v___x_3393_;
}
}
}
v___jp_3358_:
{
if (lean_obj_tag(v___y_3359_) == 0)
{
lean_object* v___x_3360_; lean_object* v___x_3361_; 
lean_dec_ref_known(v___y_3359_, 1);
v___x_3360_ = lean_box(0);
v___x_3361_ = l_Lean_Meta_Grind_Order_getStruct___redArg(v_a_3346_, v_a_3347_, v_a_3355_);
if (lean_obj_tag(v___x_3361_) == 0)
{
lean_object* v_a_3362_; lean_object* v_sources_3363_; lean_object* v_size_3364_; uint8_t v___x_3365_; 
v_a_3362_ = lean_ctor_get(v___x_3361_, 0);
lean_inc(v_a_3362_);
lean_dec_ref_known(v___x_3361_, 1);
v_sources_3363_ = lean_ctor_get(v_a_3362_, 5);
lean_inc_ref(v_sources_3363_);
lean_dec(v_a_3362_);
v_size_3364_ = lean_ctor_get(v_sources_3363_, 2);
v___x_3365_ = lean_nat_dec_lt(v_u_3343_, v_size_3364_);
if (v___x_3365_ == 0)
{
lean_object* v___x_3366_; lean_object* v___x_3367_; 
lean_dec_ref(v_sources_3363_);
v___x_3366_ = l_outOfBounds___redArg(v___x_3360_);
v___x_3367_ = l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__1(v_k_3345_, v_v_3344_, v_u_3343_, v___x_3366_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_, v_a_3353_, v_a_3354_, v_a_3355_, v_a_3356_);
lean_dec(v_u_3343_);
return v___x_3367_;
}
else
{
lean_object* v___x_3368_; lean_object* v___x_3369_; 
v___x_3368_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3360_, v_sources_3363_, v_u_3343_);
lean_dec_ref(v_sources_3363_);
v___x_3369_ = l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__1(v_k_3345_, v_v_3344_, v_u_3343_, v___x_3368_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_, v_a_3353_, v_a_3354_, v_a_3355_, v_a_3356_);
lean_dec(v_u_3343_);
return v___x_3369_;
}
}
else
{
lean_object* v_a_3370_; lean_object* v___x_3372_; uint8_t v_isShared_3373_; uint8_t v_isSharedCheck_3377_; 
lean_dec_ref(v_k_3345_);
lean_dec(v_v_3344_);
lean_dec(v_u_3343_);
v_a_3370_ = lean_ctor_get(v___x_3361_, 0);
v_isSharedCheck_3377_ = !lean_is_exclusive(v___x_3361_);
if (v_isSharedCheck_3377_ == 0)
{
v___x_3372_ = v___x_3361_;
v_isShared_3373_ = v_isSharedCheck_3377_;
goto v_resetjp_3371_;
}
else
{
lean_inc(v_a_3370_);
lean_dec(v___x_3361_);
v___x_3372_ = lean_box(0);
v_isShared_3373_ = v_isSharedCheck_3377_;
goto v_resetjp_3371_;
}
v_resetjp_3371_:
{
lean_object* v___x_3375_; 
if (v_isShared_3373_ == 0)
{
v___x_3375_ = v___x_3372_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3376_; 
v_reuseFailAlloc_3376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3376_, 0, v_a_3370_);
v___x_3375_ = v_reuseFailAlloc_3376_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
return v___x_3375_;
}
}
}
}
else
{
lean_dec_ref(v_k_3345_);
lean_dec(v_v_3344_);
lean_dec(v_u_3343_);
return v___y_3359_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update___boxed(lean_object* v_u_3396_, lean_object* v_v_3397_, lean_object* v_k_3398_, lean_object* v_a_3399_, lean_object* v_a_3400_, lean_object* v_a_3401_, lean_object* v_a_3402_, lean_object* v_a_3403_, lean_object* v_a_3404_, lean_object* v_a_3405_, lean_object* v_a_3406_, lean_object* v_a_3407_, lean_object* v_a_3408_, lean_object* v_a_3409_, lean_object* v_a_3410_){
_start:
{
lean_object* v_res_3411_; 
v_res_3411_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update(v_u_3396_, v_v_3397_, v_k_3398_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_, v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_, v_a_3409_);
lean_dec(v_a_3409_);
lean_dec_ref(v_a_3408_);
lean_dec(v_a_3407_);
lean_dec_ref(v_a_3406_);
lean_dec(v_a_3405_);
lean_dec_ref(v_a_3404_);
lean_dec(v_a_3403_);
lean_dec_ref(v_a_3402_);
lean_dec(v_a_3401_);
lean_dec(v_a_3400_);
lean_dec(v_a_3399_);
return v_res_3411_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_addEdge___closed__2(void){
_start:
{
lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; 
v___x_3418_ = ((lean_object*)(l_Lean_Meta_Grind_Order_addEdge___closed__1));
v___x_3419_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__6));
v___x_3420_ = l_Lean_Name_append(v___x_3419_, v___x_3418_);
return v___x_3420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_addEdge(lean_object* v_u_3421_, lean_object* v_v_3422_, lean_object* v_k_3423_, lean_object* v_h_3424_, lean_object* v_a_3425_, lean_object* v_a_3426_, lean_object* v_a_3427_, lean_object* v_a_3428_, lean_object* v_a_3429_, lean_object* v_a_3430_, lean_object* v_a_3431_, lean_object* v_a_3432_, lean_object* v_a_3433_, lean_object* v_a_3434_, lean_object* v_a_3435_){
_start:
{
lean_object* v___y_3438_; lean_object* v___y_3439_; lean_object* v___y_3440_; lean_object* v___y_3441_; lean_object* v___y_3442_; lean_object* v___y_3443_; lean_object* v___y_3444_; lean_object* v___y_3445_; lean_object* v___y_3446_; lean_object* v___y_3447_; lean_object* v___y_3448_; lean_object* v___y_3475_; lean_object* v___y_3476_; lean_object* v___y_3477_; lean_object* v___y_3478_; lean_object* v___y_3479_; lean_object* v___y_3480_; lean_object* v___y_3481_; lean_object* v___y_3482_; lean_object* v___y_3483_; lean_object* v___y_3484_; lean_object* v___y_3485_; lean_object* v___x_3512_; 
v___x_3512_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_3426_);
if (lean_obj_tag(v___x_3512_) == 0)
{
lean_object* v_a_3513_; lean_object* v___x_3515_; uint8_t v_isShared_3516_; uint8_t v_isSharedCheck_3590_; 
v_a_3513_ = lean_ctor_get(v___x_3512_, 0);
v_isSharedCheck_3590_ = !lean_is_exclusive(v___x_3512_);
if (v_isSharedCheck_3590_ == 0)
{
v___x_3515_ = v___x_3512_;
v_isShared_3516_ = v_isSharedCheck_3590_;
goto v_resetjp_3514_;
}
else
{
lean_inc(v_a_3513_);
lean_dec(v___x_3512_);
v___x_3515_ = lean_box(0);
v_isShared_3516_ = v_isSharedCheck_3590_;
goto v_resetjp_3514_;
}
v_resetjp_3514_:
{
uint8_t v___x_3517_; 
v___x_3517_ = lean_unbox(v_a_3513_);
lean_dec(v_a_3513_);
if (v___x_3517_ == 0)
{
uint8_t v___x_3518_; 
lean_del_object(v___x_3515_);
v___x_3518_ = lean_nat_dec_eq(v_u_3421_, v_v_3422_);
if (v___x_3518_ == 0)
{
lean_object* v_toCold_3519_; lean_object* v_options_3520_; uint8_t v_hasTrace_3521_; 
v_toCold_3519_ = lean_ctor_get(v_a_3434_, 0);
v_options_3520_ = lean_ctor_get(v_toCold_3519_, 2);
v_hasTrace_3521_ = lean_ctor_get_uint8(v_options_3520_, sizeof(void*)*1);
if (v_hasTrace_3521_ == 0)
{
v___y_3475_ = v_a_3425_;
v___y_3476_ = v_a_3426_;
v___y_3477_ = v_a_3427_;
v___y_3478_ = v_a_3428_;
v___y_3479_ = v_a_3429_;
v___y_3480_ = v_a_3430_;
v___y_3481_ = v_a_3431_;
v___y_3482_ = v_a_3432_;
v___y_3483_ = v_a_3433_;
v___y_3484_ = v_a_3434_;
v___y_3485_ = v_a_3435_;
goto v___jp_3474_;
}
else
{
lean_object* v_inheritedTraceOptions_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; uint8_t v___x_3525_; 
v_inheritedTraceOptions_3522_ = lean_ctor_get(v_toCold_3519_, 11);
v___x_3523_ = ((lean_object*)(l_Lean_Meta_Grind_Order_addEdge___closed__1));
v___x_3524_ = lean_obj_once(&l_Lean_Meta_Grind_Order_addEdge___closed__2, &l_Lean_Meta_Grind_Order_addEdge___closed__2_once, _init_l_Lean_Meta_Grind_Order_addEdge___closed__2);
v___x_3525_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3522_, v_options_3520_, v___x_3524_);
if (v___x_3525_ == 0)
{
v___y_3475_ = v_a_3425_;
v___y_3476_ = v_a_3426_;
v___y_3477_ = v_a_3427_;
v___y_3478_ = v_a_3428_;
v___y_3479_ = v_a_3429_;
v___y_3480_ = v_a_3430_;
v___y_3481_ = v_a_3431_;
v___y_3482_ = v_a_3432_;
v___y_3483_ = v_a_3433_;
v___y_3484_ = v_a_3434_;
v___y_3485_ = v_a_3435_;
goto v___jp_3474_;
}
else
{
lean_object* v___x_3526_; 
v___x_3526_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_u_3421_, v_a_3425_, v_a_3426_, v_a_3434_);
if (lean_obj_tag(v___x_3526_) == 0)
{
lean_object* v_a_3527_; lean_object* v___x_3528_; 
v_a_3527_ = lean_ctor_get(v___x_3526_, 0);
lean_inc(v_a_3527_);
lean_dec_ref_known(v___x_3526_, 1);
v___x_3528_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_v_3422_, v_a_3425_, v_a_3426_, v_a_3434_);
if (lean_obj_tag(v___x_3528_) == 0)
{
lean_object* v_a_3529_; lean_object* v_k_3530_; uint8_t v_strict_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___y_3539_; 
v_a_3529_ = lean_ctor_get(v___x_3528_, 0);
lean_inc(v_a_3529_);
lean_dec_ref_known(v___x_3528_, 1);
v_k_3530_ = lean_ctor_get(v_k_3423_, 0);
v_strict_3531_ = lean_ctor_get_uint8(v_k_3423_, sizeof(void*)*1);
v___x_3532_ = l_Lean_MessageData_ofExpr(v_a_3527_);
v___x_3533_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4);
v___x_3534_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3534_, 0, v___x_3532_);
lean_ctor_set(v___x_3534_, 1, v___x_3533_);
v___x_3535_ = l_Lean_MessageData_ofExpr(v_a_3529_);
v___x_3536_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3536_, 0, v___x_3534_);
lean_ctor_set(v___x_3536_, 1, v___x_3535_);
v___x_3537_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3537_, 0, v___x_3536_);
lean_ctor_set(v___x_3537_, 1, v___x_3533_);
if (v_strict_3531_ == 0)
{
lean_object* v___x_3544_; 
v___x_3544_ = l_Int_repr(v_k_3530_);
v___y_3539_ = v___x_3544_;
goto v___jp_3538_;
}
else
{
lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; 
v___x_3545_ = l_Int_repr(v_k_3530_);
v___x_3546_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5));
v___x_3547_ = lean_string_append(v___x_3545_, v___x_3546_);
v___y_3539_ = v___x_3547_;
goto v___jp_3538_;
}
v___jp_3538_:
{
lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; 
v___x_3540_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3540_, 0, v___y_3539_);
v___x_3541_ = l_Lean_MessageData_ofFormat(v___x_3540_);
v___x_3542_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3542_, 0, v___x_3537_);
lean_ctor_set(v___x_3542_, 1, v___x_3541_);
v___x_3543_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(v___x_3523_, v___x_3542_, v_a_3432_, v_a_3433_, v_a_3434_, v_a_3435_);
if (lean_obj_tag(v___x_3543_) == 0)
{
lean_dec_ref_known(v___x_3543_, 1);
v___y_3475_ = v_a_3425_;
v___y_3476_ = v_a_3426_;
v___y_3477_ = v_a_3427_;
v___y_3478_ = v_a_3428_;
v___y_3479_ = v_a_3429_;
v___y_3480_ = v_a_3430_;
v___y_3481_ = v_a_3431_;
v___y_3482_ = v_a_3432_;
v___y_3483_ = v_a_3433_;
v___y_3484_ = v_a_3434_;
v___y_3485_ = v_a_3435_;
goto v___jp_3474_;
}
else
{
lean_dec_ref(v_h_3424_);
lean_dec_ref(v_k_3423_);
lean_dec(v_v_3422_);
lean_dec(v_u_3421_);
return v___x_3543_;
}
}
}
else
{
lean_object* v_a_3548_; lean_object* v___x_3550_; uint8_t v_isShared_3551_; uint8_t v_isSharedCheck_3555_; 
lean_dec(v_a_3527_);
lean_dec_ref(v_h_3424_);
lean_dec_ref(v_k_3423_);
lean_dec(v_v_3422_);
lean_dec(v_u_3421_);
v_a_3548_ = lean_ctor_get(v___x_3528_, 0);
v_isSharedCheck_3555_ = !lean_is_exclusive(v___x_3528_);
if (v_isSharedCheck_3555_ == 0)
{
v___x_3550_ = v___x_3528_;
v_isShared_3551_ = v_isSharedCheck_3555_;
goto v_resetjp_3549_;
}
else
{
lean_inc(v_a_3548_);
lean_dec(v___x_3528_);
v___x_3550_ = lean_box(0);
v_isShared_3551_ = v_isSharedCheck_3555_;
goto v_resetjp_3549_;
}
v_resetjp_3549_:
{
lean_object* v___x_3553_; 
if (v_isShared_3551_ == 0)
{
v___x_3553_ = v___x_3550_;
goto v_reusejp_3552_;
}
else
{
lean_object* v_reuseFailAlloc_3554_; 
v_reuseFailAlloc_3554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3554_, 0, v_a_3548_);
v___x_3553_ = v_reuseFailAlloc_3554_;
goto v_reusejp_3552_;
}
v_reusejp_3552_:
{
return v___x_3553_;
}
}
}
}
else
{
lean_object* v_a_3556_; lean_object* v___x_3558_; uint8_t v_isShared_3559_; uint8_t v_isSharedCheck_3563_; 
lean_dec_ref(v_h_3424_);
lean_dec_ref(v_k_3423_);
lean_dec(v_v_3422_);
lean_dec(v_u_3421_);
v_a_3556_ = lean_ctor_get(v___x_3526_, 0);
v_isSharedCheck_3563_ = !lean_is_exclusive(v___x_3526_);
if (v_isSharedCheck_3563_ == 0)
{
v___x_3558_ = v___x_3526_;
v_isShared_3559_ = v_isSharedCheck_3563_;
goto v_resetjp_3557_;
}
else
{
lean_inc(v_a_3556_);
lean_dec(v___x_3526_);
v___x_3558_ = lean_box(0);
v_isShared_3559_ = v_isSharedCheck_3563_;
goto v_resetjp_3557_;
}
v_resetjp_3557_:
{
lean_object* v___x_3561_; 
if (v_isShared_3559_ == 0)
{
v___x_3561_ = v___x_3558_;
goto v_reusejp_3560_;
}
else
{
lean_object* v_reuseFailAlloc_3562_; 
v_reuseFailAlloc_3562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3562_, 0, v_a_3556_);
v___x_3561_ = v_reuseFailAlloc_3562_;
goto v_reusejp_3560_;
}
v_reusejp_3560_:
{
return v___x_3561_;
}
}
}
}
}
}
else
{
uint8_t v___x_3564_; 
lean_dec(v_v_3422_);
v___x_3564_ = l_Lean_Meta_Grind_Order_Weight_isNeg(v_k_3423_);
if (v___x_3564_ == 0)
{
lean_dec_ref(v_h_3424_);
lean_dec_ref(v_k_3423_);
lean_dec(v_u_3421_);
goto v___jp_3509_;
}
else
{
lean_object* v___x_3565_; 
v___x_3565_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_u_3421_, v_a_3425_, v_a_3426_, v_a_3434_);
lean_dec(v_u_3421_);
if (lean_obj_tag(v___x_3565_) == 0)
{
lean_object* v_a_3566_; lean_object* v___x_3567_; 
v_a_3566_ = lean_ctor_get(v___x_3565_, 0);
lean_inc(v_a_3566_);
lean_dec_ref_known(v___x_3565_, 1);
v___x_3567_ = l_Lean_Meta_Grind_Order_mkSelfUnsatProof(v_a_3566_, v_k_3423_, v_h_3424_, v_a_3425_, v_a_3426_, v_a_3427_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_, v_a_3435_);
lean_dec_ref(v_k_3423_);
if (lean_obj_tag(v___x_3567_) == 0)
{
lean_object* v_a_3568_; lean_object* v___x_3569_; 
v_a_3568_ = lean_ctor_get(v___x_3567_, 0);
lean_inc(v_a_3568_);
lean_dec_ref_known(v___x_3567_, 1);
v___x_3569_ = l_Lean_Meta_Grind_closeGoal(v_a_3568_, v_a_3426_, v_a_3427_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_, v_a_3435_);
if (lean_obj_tag(v___x_3569_) == 0)
{
lean_dec_ref_known(v___x_3569_, 1);
goto v___jp_3509_;
}
else
{
return v___x_3569_;
}
}
else
{
lean_object* v_a_3570_; lean_object* v___x_3572_; uint8_t v_isShared_3573_; uint8_t v_isSharedCheck_3577_; 
v_a_3570_ = lean_ctor_get(v___x_3567_, 0);
v_isSharedCheck_3577_ = !lean_is_exclusive(v___x_3567_);
if (v_isSharedCheck_3577_ == 0)
{
v___x_3572_ = v___x_3567_;
v_isShared_3573_ = v_isSharedCheck_3577_;
goto v_resetjp_3571_;
}
else
{
lean_inc(v_a_3570_);
lean_dec(v___x_3567_);
v___x_3572_ = lean_box(0);
v_isShared_3573_ = v_isSharedCheck_3577_;
goto v_resetjp_3571_;
}
v_resetjp_3571_:
{
lean_object* v___x_3575_; 
if (v_isShared_3573_ == 0)
{
v___x_3575_ = v___x_3572_;
goto v_reusejp_3574_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v_a_3570_);
v___x_3575_ = v_reuseFailAlloc_3576_;
goto v_reusejp_3574_;
}
v_reusejp_3574_:
{
return v___x_3575_;
}
}
}
}
else
{
lean_object* v_a_3578_; lean_object* v___x_3580_; uint8_t v_isShared_3581_; uint8_t v_isSharedCheck_3585_; 
lean_dec_ref(v_h_3424_);
lean_dec_ref(v_k_3423_);
v_a_3578_ = lean_ctor_get(v___x_3565_, 0);
v_isSharedCheck_3585_ = !lean_is_exclusive(v___x_3565_);
if (v_isSharedCheck_3585_ == 0)
{
v___x_3580_ = v___x_3565_;
v_isShared_3581_ = v_isSharedCheck_3585_;
goto v_resetjp_3579_;
}
else
{
lean_inc(v_a_3578_);
lean_dec(v___x_3565_);
v___x_3580_ = lean_box(0);
v_isShared_3581_ = v_isSharedCheck_3585_;
goto v_resetjp_3579_;
}
v_resetjp_3579_:
{
lean_object* v___x_3583_; 
if (v_isShared_3581_ == 0)
{
v___x_3583_ = v___x_3580_;
goto v_reusejp_3582_;
}
else
{
lean_object* v_reuseFailAlloc_3584_; 
v_reuseFailAlloc_3584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3584_, 0, v_a_3578_);
v___x_3583_ = v_reuseFailAlloc_3584_;
goto v_reusejp_3582_;
}
v_reusejp_3582_:
{
return v___x_3583_;
}
}
}
}
}
}
else
{
lean_object* v___x_3586_; lean_object* v___x_3588_; 
lean_dec_ref(v_h_3424_);
lean_dec_ref(v_k_3423_);
lean_dec(v_v_3422_);
lean_dec(v_u_3421_);
v___x_3586_ = lean_box(0);
if (v_isShared_3516_ == 0)
{
lean_ctor_set(v___x_3515_, 0, v___x_3586_);
v___x_3588_ = v___x_3515_;
goto v_reusejp_3587_;
}
else
{
lean_object* v_reuseFailAlloc_3589_; 
v_reuseFailAlloc_3589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3589_, 0, v___x_3586_);
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
lean_dec_ref(v_h_3424_);
lean_dec_ref(v_k_3423_);
lean_dec(v_v_3422_);
lean_dec(v_u_3421_);
v_a_3591_ = lean_ctor_get(v___x_3512_, 0);
v_isSharedCheck_3598_ = !lean_is_exclusive(v___x_3512_);
if (v_isSharedCheck_3598_ == 0)
{
v___x_3593_ = v___x_3512_;
v_isShared_3594_ = v_isSharedCheck_3598_;
goto v_resetjp_3592_;
}
else
{
lean_inc(v_a_3591_);
lean_dec(v___x_3512_);
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
v___jp_3437_:
{
lean_object* v___x_3449_; 
v___x_3449_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isShorter___redArg(v_u_3421_, v_v_3422_, v_k_3423_, v___y_3438_, v___y_3439_, v___y_3447_);
if (lean_obj_tag(v___x_3449_) == 0)
{
lean_object* v_a_3450_; lean_object* v___x_3452_; uint8_t v_isShared_3453_; uint8_t v_isSharedCheck_3465_; 
v_a_3450_ = lean_ctor_get(v___x_3449_, 0);
v_isSharedCheck_3465_ = !lean_is_exclusive(v___x_3449_);
if (v_isSharedCheck_3465_ == 0)
{
v___x_3452_ = v___x_3449_;
v_isShared_3453_ = v_isSharedCheck_3465_;
goto v_resetjp_3451_;
}
else
{
lean_inc(v_a_3450_);
lean_dec(v___x_3449_);
v___x_3452_ = lean_box(0);
v_isShared_3453_ = v_isSharedCheck_3465_;
goto v_resetjp_3451_;
}
v_resetjp_3451_:
{
uint8_t v___x_3454_; 
v___x_3454_ = lean_unbox(v_a_3450_);
lean_dec(v_a_3450_);
if (v___x_3454_ == 0)
{
lean_object* v___x_3455_; lean_object* v___x_3457_; 
lean_dec_ref(v_h_3424_);
lean_dec_ref(v_k_3423_);
lean_dec(v_v_3422_);
lean_dec(v_u_3421_);
v___x_3455_ = lean_box(0);
if (v_isShared_3453_ == 0)
{
lean_ctor_set(v___x_3452_, 0, v___x_3455_);
v___x_3457_ = v___x_3452_;
goto v_reusejp_3456_;
}
else
{
lean_object* v_reuseFailAlloc_3458_; 
v_reuseFailAlloc_3458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3458_, 0, v___x_3455_);
v___x_3457_ = v_reuseFailAlloc_3458_;
goto v_reusejp_3456_;
}
v_reusejp_3456_:
{
return v___x_3457_;
}
}
else
{
lean_object* v___x_3459_; 
lean_del_object(v___x_3452_);
lean_inc_ref(v_k_3423_);
lean_inc(v_v_3422_);
lean_inc(v_u_3421_);
v___x_3459_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist___redArg(v_u_3421_, v_v_3422_, v_k_3423_, v___y_3438_, v___y_3439_);
if (lean_obj_tag(v___x_3459_) == 0)
{
lean_object* v___x_3460_; lean_object* v___x_3461_; 
lean_dec_ref_known(v___x_3459_, 1);
lean_inc_ref(v_k_3423_);
lean_inc_n(v_u_3421_, 2);
v___x_3460_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3460_, 0, v_u_3421_);
lean_ctor_set(v___x_3460_, 1, v_k_3423_);
lean_ctor_set(v___x_3460_, 2, v_h_3424_);
lean_inc(v_v_3422_);
v___x_3461_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___redArg(v_u_3421_, v_v_3422_, v___x_3460_, v___y_3438_, v___y_3439_);
if (lean_obj_tag(v___x_3461_) == 0)
{
lean_object* v___x_3462_; 
lean_dec_ref_known(v___x_3461_, 1);
lean_inc_ref(v_k_3423_);
lean_inc(v_v_3422_);
lean_inc(v_u_3421_);
v___x_3462_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate(v_u_3421_, v_v_3422_, v_k_3423_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_);
if (lean_obj_tag(v___x_3462_) == 0)
{
lean_object* v___x_3463_; 
lean_dec_ref_known(v___x_3462_, 1);
v___x_3463_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update(v_u_3421_, v_v_3422_, v_k_3423_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_);
if (lean_obj_tag(v___x_3463_) == 0)
{
lean_object* v___x_3464_; 
lean_dec_ref_known(v___x_3463_, 1);
v___x_3464_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending(v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_);
return v___x_3464_;
}
else
{
return v___x_3463_;
}
}
else
{
lean_dec_ref(v_k_3423_);
lean_dec(v_v_3422_);
lean_dec(v_u_3421_);
return v___x_3462_;
}
}
else
{
lean_dec_ref(v_k_3423_);
lean_dec(v_v_3422_);
lean_dec(v_u_3421_);
return v___x_3461_;
}
}
else
{
lean_dec_ref(v_h_3424_);
lean_dec_ref(v_k_3423_);
lean_dec(v_v_3422_);
lean_dec(v_u_3421_);
return v___x_3459_;
}
}
}
}
else
{
lean_object* v_a_3466_; lean_object* v___x_3468_; uint8_t v_isShared_3469_; uint8_t v_isSharedCheck_3473_; 
lean_dec_ref(v_h_3424_);
lean_dec_ref(v_k_3423_);
lean_dec(v_v_3422_);
lean_dec(v_u_3421_);
v_a_3466_ = lean_ctor_get(v___x_3449_, 0);
v_isSharedCheck_3473_ = !lean_is_exclusive(v___x_3449_);
if (v_isSharedCheck_3473_ == 0)
{
v___x_3468_ = v___x_3449_;
v_isShared_3469_ = v_isSharedCheck_3473_;
goto v_resetjp_3467_;
}
else
{
lean_inc(v_a_3466_);
lean_dec(v___x_3449_);
v___x_3468_ = lean_box(0);
v_isShared_3469_ = v_isSharedCheck_3473_;
goto v_resetjp_3467_;
}
v_resetjp_3467_:
{
lean_object* v___x_3471_; 
if (v_isShared_3469_ == 0)
{
v___x_3471_ = v___x_3468_;
goto v_reusejp_3470_;
}
else
{
lean_object* v_reuseFailAlloc_3472_; 
v_reuseFailAlloc_3472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3472_, 0, v_a_3466_);
v___x_3471_ = v_reuseFailAlloc_3472_;
goto v_reusejp_3470_;
}
v_reusejp_3470_:
{
return v___x_3471_;
}
}
}
}
v___jp_3474_:
{
lean_object* v___x_3486_; 
v___x_3486_ = l_Lean_Meta_Grind_Order_getDist_x3f___redArg(v_v_3422_, v_u_3421_, v___y_3475_, v___y_3476_, v___y_3484_);
if (lean_obj_tag(v___x_3486_) == 0)
{
lean_object* v_a_3487_; 
v_a_3487_ = lean_ctor_get(v___x_3486_, 0);
lean_inc(v_a_3487_);
lean_dec_ref_known(v___x_3486_, 1);
if (lean_obj_tag(v_a_3487_) == 1)
{
lean_object* v_val_3488_; lean_object* v___x_3489_; uint8_t v___x_3490_; 
v_val_3488_ = lean_ctor_get(v_a_3487_, 0);
lean_inc_n(v_val_3488_, 2);
lean_dec_ref_known(v_a_3487_, 1);
v___x_3489_ = l_Lean_Meta_Grind_Order_Weight_add(v_k_3423_, v_val_3488_);
v___x_3490_ = l_Lean_Meta_Grind_Order_Weight_isNeg(v___x_3489_);
lean_dec_ref(v___x_3489_);
if (v___x_3490_ == 0)
{
lean_dec(v_val_3488_);
v___y_3438_ = v___y_3475_;
v___y_3439_ = v___y_3476_;
v___y_3440_ = v___y_3477_;
v___y_3441_ = v___y_3478_;
v___y_3442_ = v___y_3479_;
v___y_3443_ = v___y_3480_;
v___y_3444_ = v___y_3481_;
v___y_3445_ = v___y_3482_;
v___y_3446_ = v___y_3483_;
v___y_3447_ = v___y_3484_;
v___y_3448_ = v___y_3485_;
goto v___jp_3437_;
}
else
{
lean_object* v___x_3491_; 
v___x_3491_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setUnsat(v_u_3421_, v_v_3422_, v_k_3423_, v_h_3424_, v_val_3488_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_, v___y_3485_);
lean_dec(v_val_3488_);
lean_dec_ref(v_k_3423_);
lean_dec(v_v_3422_);
lean_dec(v_u_3421_);
if (lean_obj_tag(v___x_3491_) == 0)
{
lean_object* v___x_3493_; uint8_t v_isShared_3494_; uint8_t v_isSharedCheck_3499_; 
v_isSharedCheck_3499_ = !lean_is_exclusive(v___x_3491_);
if (v_isSharedCheck_3499_ == 0)
{
lean_object* v_unused_3500_; 
v_unused_3500_ = lean_ctor_get(v___x_3491_, 0);
lean_dec(v_unused_3500_);
v___x_3493_ = v___x_3491_;
v_isShared_3494_ = v_isSharedCheck_3499_;
goto v_resetjp_3492_;
}
else
{
lean_dec(v___x_3491_);
v___x_3493_ = lean_box(0);
v_isShared_3494_ = v_isSharedCheck_3499_;
goto v_resetjp_3492_;
}
v_resetjp_3492_:
{
lean_object* v___x_3495_; lean_object* v___x_3497_; 
v___x_3495_ = lean_box(0);
if (v_isShared_3494_ == 0)
{
lean_ctor_set(v___x_3493_, 0, v___x_3495_);
v___x_3497_ = v___x_3493_;
goto v_reusejp_3496_;
}
else
{
lean_object* v_reuseFailAlloc_3498_; 
v_reuseFailAlloc_3498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3498_, 0, v___x_3495_);
v___x_3497_ = v_reuseFailAlloc_3498_;
goto v_reusejp_3496_;
}
v_reusejp_3496_:
{
return v___x_3497_;
}
}
}
else
{
return v___x_3491_;
}
}
}
else
{
lean_dec(v_a_3487_);
v___y_3438_ = v___y_3475_;
v___y_3439_ = v___y_3476_;
v___y_3440_ = v___y_3477_;
v___y_3441_ = v___y_3478_;
v___y_3442_ = v___y_3479_;
v___y_3443_ = v___y_3480_;
v___y_3444_ = v___y_3481_;
v___y_3445_ = v___y_3482_;
v___y_3446_ = v___y_3483_;
v___y_3447_ = v___y_3484_;
v___y_3448_ = v___y_3485_;
goto v___jp_3437_;
}
}
else
{
lean_object* v_a_3501_; lean_object* v___x_3503_; uint8_t v_isShared_3504_; uint8_t v_isSharedCheck_3508_; 
lean_dec_ref(v_h_3424_);
lean_dec_ref(v_k_3423_);
lean_dec(v_v_3422_);
lean_dec(v_u_3421_);
v_a_3501_ = lean_ctor_get(v___x_3486_, 0);
v_isSharedCheck_3508_ = !lean_is_exclusive(v___x_3486_);
if (v_isSharedCheck_3508_ == 0)
{
v___x_3503_ = v___x_3486_;
v_isShared_3504_ = v_isSharedCheck_3508_;
goto v_resetjp_3502_;
}
else
{
lean_inc(v_a_3501_);
lean_dec(v___x_3486_);
v___x_3503_ = lean_box(0);
v_isShared_3504_ = v_isSharedCheck_3508_;
goto v_resetjp_3502_;
}
v_resetjp_3502_:
{
lean_object* v___x_3506_; 
if (v_isShared_3504_ == 0)
{
v___x_3506_ = v___x_3503_;
goto v_reusejp_3505_;
}
else
{
lean_object* v_reuseFailAlloc_3507_; 
v_reuseFailAlloc_3507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3507_, 0, v_a_3501_);
v___x_3506_ = v_reuseFailAlloc_3507_;
goto v_reusejp_3505_;
}
v_reusejp_3505_:
{
return v___x_3506_;
}
}
}
}
v___jp_3509_:
{
lean_object* v___x_3510_; lean_object* v___x_3511_; 
v___x_3510_ = lean_box(0);
v___x_3511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3511_, 0, v___x_3510_);
return v___x_3511_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_addEdge___boxed(lean_object* v_u_3599_, lean_object* v_v_3600_, lean_object* v_k_3601_, lean_object* v_h_3602_, lean_object* v_a_3603_, lean_object* v_a_3604_, lean_object* v_a_3605_, lean_object* v_a_3606_, lean_object* v_a_3607_, lean_object* v_a_3608_, lean_object* v_a_3609_, lean_object* v_a_3610_, lean_object* v_a_3611_, lean_object* v_a_3612_, lean_object* v_a_3613_, lean_object* v_a_3614_){
_start:
{
lean_object* v_res_3615_; 
v_res_3615_ = l_Lean_Meta_Grind_Order_addEdge(v_u_3599_, v_v_3600_, v_k_3601_, v_h_3602_, v_a_3603_, v_a_3604_, v_a_3605_, v_a_3606_, v_a_3607_, v_a_3608_, v_a_3609_, v_a_3610_, v_a_3611_, v_a_3612_, v_a_3613_);
lean_dec(v_a_3613_);
lean_dec_ref(v_a_3612_);
lean_dec(v_a_3611_);
lean_dec_ref(v_a_3610_);
lean_dec(v_a_3609_);
lean_dec_ref(v_a_3608_);
lean_dec(v_a_3607_);
lean_dec_ref(v_a_3606_);
lean_dec(v_a_3605_);
lean_dec(v_a_3604_);
lean_dec(v_a_3603_);
return v_res_3615_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__2(void){
_start:
{
lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; 
v___x_3622_ = lean_box(0);
v___x_3623_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__1));
v___x_3624_ = l_Lean_mkConst(v___x_3623_, v___x_3622_);
return v___x_3624_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5(void){
_start:
{
lean_object* v_cls_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; 
v_cls_3630_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__4));
v___x_3631_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__6));
v___x_3632_ = l_Lean_Name_append(v___x_3631_, v_cls_3630_);
return v___x_3632_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue(lean_object* v_c_3633_, lean_object* v_e_3634_, lean_object* v_he_3635_, lean_object* v_a_3636_, lean_object* v_a_3637_, lean_object* v_a_3638_, lean_object* v_a_3639_, lean_object* v_a_3640_, lean_object* v_a_3641_, lean_object* v_a_3642_, lean_object* v_a_3643_, lean_object* v_a_3644_, lean_object* v_a_3645_, lean_object* v_a_3646_){
_start:
{
lean_object* v___y_3649_; lean_object* v___y_3650_; lean_object* v___y_3651_; lean_object* v___y_3652_; lean_object* v___y_3653_; lean_object* v___y_3654_; lean_object* v___y_3655_; lean_object* v___y_3656_; lean_object* v___y_3657_; lean_object* v___y_3658_; lean_object* v___y_3659_; lean_object* v___y_3660_; lean_object* v___y_3661_; lean_object* v___y_3662_; lean_object* v___y_3663_; uint8_t v___y_3664_; lean_object* v_h_3668_; lean_object* v___y_3669_; lean_object* v___y_3670_; lean_object* v___y_3671_; lean_object* v___y_3672_; lean_object* v___y_3673_; lean_object* v___y_3674_; lean_object* v___y_3675_; lean_object* v___y_3676_; lean_object* v___y_3677_; lean_object* v___y_3678_; lean_object* v___y_3679_; lean_object* v___y_3690_; lean_object* v___y_3691_; lean_object* v___y_3692_; lean_object* v___y_3693_; lean_object* v___y_3694_; lean_object* v___y_3695_; lean_object* v___y_3696_; lean_object* v___y_3697_; lean_object* v___y_3698_; lean_object* v___y_3699_; lean_object* v___y_3700_; lean_object* v_toCold_3708_; lean_object* v_options_3709_; uint8_t v_hasTrace_3710_; 
v_toCold_3708_ = lean_ctor_get(v_a_3645_, 0);
v_options_3709_ = lean_ctor_get(v_toCold_3708_, 2);
v_hasTrace_3710_ = lean_ctor_get_uint8(v_options_3709_, sizeof(void*)*1);
if (v_hasTrace_3710_ == 0)
{
v___y_3690_ = v_a_3636_;
v___y_3691_ = v_a_3637_;
v___y_3692_ = v_a_3638_;
v___y_3693_ = v_a_3639_;
v___y_3694_ = v_a_3640_;
v___y_3695_ = v_a_3641_;
v___y_3696_ = v_a_3642_;
v___y_3697_ = v_a_3643_;
v___y_3698_ = v_a_3644_;
v___y_3699_ = v_a_3645_;
v___y_3700_ = v_a_3646_;
goto v___jp_3689_;
}
else
{
lean_object* v_inheritedTraceOptions_3711_; lean_object* v_cls_3712_; lean_object* v___x_3713_; uint8_t v___x_3714_; 
v_inheritedTraceOptions_3711_ = lean_ctor_get(v_toCold_3708_, 11);
v_cls_3712_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__4));
v___x_3713_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5);
v___x_3714_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3711_, v_options_3709_, v___x_3713_);
if (v___x_3714_ == 0)
{
v___y_3690_ = v_a_3636_;
v___y_3691_ = v_a_3637_;
v___y_3692_ = v_a_3638_;
v___y_3693_ = v_a_3639_;
v___y_3694_ = v_a_3640_;
v___y_3695_ = v_a_3641_;
v___y_3696_ = v_a_3642_;
v___y_3697_ = v_a_3643_;
v___y_3698_ = v_a_3644_;
v___y_3699_ = v_a_3645_;
v___y_3700_ = v_a_3646_;
goto v___jp_3689_;
}
else
{
lean_object* v___x_3715_; 
v___x_3715_ = l_Lean_Meta_Grind_Order_Cnstr_pp___redArg(v_c_3633_, v_a_3636_, v_a_3637_, v_a_3645_);
if (lean_obj_tag(v___x_3715_) == 0)
{
lean_object* v_a_3716_; lean_object* v___x_3717_; 
v_a_3716_ = lean_ctor_get(v___x_3715_, 0);
lean_inc(v_a_3716_);
lean_dec_ref_known(v___x_3715_, 1);
v___x_3717_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(v_cls_3712_, v_a_3716_, v_a_3643_, v_a_3644_, v_a_3645_, v_a_3646_);
if (lean_obj_tag(v___x_3717_) == 0)
{
lean_dec_ref_known(v___x_3717_, 1);
v___y_3690_ = v_a_3636_;
v___y_3691_ = v_a_3637_;
v___y_3692_ = v_a_3638_;
v___y_3693_ = v_a_3639_;
v___y_3694_ = v_a_3640_;
v___y_3695_ = v_a_3641_;
v___y_3696_ = v_a_3642_;
v___y_3697_ = v_a_3643_;
v___y_3698_ = v_a_3644_;
v___y_3699_ = v_a_3645_;
v___y_3700_ = v_a_3646_;
goto v___jp_3689_;
}
else
{
lean_dec_ref(v_he_3635_);
lean_dec_ref(v_e_3634_);
lean_dec_ref(v_c_3633_);
return v___x_3717_;
}
}
else
{
lean_object* v_a_3718_; lean_object* v___x_3720_; uint8_t v_isShared_3721_; uint8_t v_isSharedCheck_3725_; 
lean_dec_ref(v_he_3635_);
lean_dec_ref(v_e_3634_);
lean_dec_ref(v_c_3633_);
v_a_3718_ = lean_ctor_get(v___x_3715_, 0);
v_isSharedCheck_3725_ = !lean_is_exclusive(v___x_3715_);
if (v_isSharedCheck_3725_ == 0)
{
v___x_3720_ = v___x_3715_;
v_isShared_3721_ = v_isSharedCheck_3725_;
goto v_resetjp_3719_;
}
else
{
lean_inc(v_a_3718_);
lean_dec(v___x_3715_);
v___x_3720_ = lean_box(0);
v_isShared_3721_ = v_isSharedCheck_3725_;
goto v_resetjp_3719_;
}
v_resetjp_3719_:
{
lean_object* v___x_3723_; 
if (v_isShared_3721_ == 0)
{
v___x_3723_ = v___x_3720_;
goto v_reusejp_3722_;
}
else
{
lean_object* v_reuseFailAlloc_3724_; 
v_reuseFailAlloc_3724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3724_, 0, v_a_3718_);
v___x_3723_ = v_reuseFailAlloc_3724_;
goto v_reusejp_3722_;
}
v_reusejp_3722_:
{
return v___x_3723_;
}
}
}
}
}
v___jp_3648_:
{
lean_object* v___x_3665_; lean_object* v___x_3666_; 
v___x_3665_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3665_, 0, v___y_3651_);
lean_ctor_set_uint8(v___x_3665_, sizeof(void*)*1, v___y_3664_);
v___x_3666_ = l_Lean_Meta_Grind_Order_addEdge(v___y_3657_, v___y_3660_, v___x_3665_, v___y_3654_, v___y_3656_, v___y_3659_, v___y_3653_, v___y_3663_, v___y_3650_, v___y_3662_, v___y_3652_, v___y_3658_, v___y_3655_, v___y_3649_, v___y_3661_);
return v___x_3666_;
}
v___jp_3667_:
{
uint8_t v_kind_3680_; 
v_kind_3680_ = lean_ctor_get_uint8(v_c_3633_, sizeof(void*)*5);
if (v_kind_3680_ == 1)
{
lean_object* v_u_3681_; lean_object* v_v_3682_; lean_object* v_k_3683_; uint8_t v___x_3684_; 
v_u_3681_ = lean_ctor_get(v_c_3633_, 0);
lean_inc(v_u_3681_);
v_v_3682_ = lean_ctor_get(v_c_3633_, 1);
lean_inc(v_v_3682_);
v_k_3683_ = lean_ctor_get(v_c_3633_, 2);
lean_inc(v_k_3683_);
lean_dec_ref(v_c_3633_);
v___x_3684_ = 1;
v___y_3649_ = v___y_3678_;
v___y_3650_ = v___y_3673_;
v___y_3651_ = v_k_3683_;
v___y_3652_ = v___y_3675_;
v___y_3653_ = v___y_3671_;
v___y_3654_ = v_h_3668_;
v___y_3655_ = v___y_3677_;
v___y_3656_ = v___y_3669_;
v___y_3657_ = v_u_3681_;
v___y_3658_ = v___y_3676_;
v___y_3659_ = v___y_3670_;
v___y_3660_ = v_v_3682_;
v___y_3661_ = v___y_3679_;
v___y_3662_ = v___y_3674_;
v___y_3663_ = v___y_3672_;
v___y_3664_ = v___x_3684_;
goto v___jp_3648_;
}
else
{
lean_object* v_u_3685_; lean_object* v_v_3686_; lean_object* v_k_3687_; uint8_t v___x_3688_; 
v_u_3685_ = lean_ctor_get(v_c_3633_, 0);
lean_inc(v_u_3685_);
v_v_3686_ = lean_ctor_get(v_c_3633_, 1);
lean_inc(v_v_3686_);
v_k_3687_ = lean_ctor_get(v_c_3633_, 2);
lean_inc(v_k_3687_);
lean_dec_ref(v_c_3633_);
v___x_3688_ = 0;
v___y_3649_ = v___y_3678_;
v___y_3650_ = v___y_3673_;
v___y_3651_ = v_k_3687_;
v___y_3652_ = v___y_3675_;
v___y_3653_ = v___y_3671_;
v___y_3654_ = v_h_3668_;
v___y_3655_ = v___y_3677_;
v___y_3656_ = v___y_3669_;
v___y_3657_ = v_u_3685_;
v___y_3658_ = v___y_3676_;
v___y_3659_ = v___y_3670_;
v___y_3660_ = v_v_3686_;
v___y_3661_ = v___y_3679_;
v___y_3662_ = v___y_3674_;
v___y_3663_ = v___y_3672_;
v___y_3664_ = v___x_3688_;
goto v___jp_3648_;
}
}
v___jp_3689_:
{
lean_object* v_h_x3f_3701_; 
v_h_x3f_3701_ = lean_ctor_get(v_c_3633_, 4);
if (lean_obj_tag(v_h_x3f_3701_) == 1)
{
lean_object* v_e_3702_; lean_object* v_val_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; 
v_e_3702_ = lean_ctor_get(v_c_3633_, 3);
v_val_3703_ = lean_ctor_get(v_h_x3f_3701_, 0);
v___x_3704_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__2, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__2);
lean_inc_ref(v_e_3634_);
v___x_3705_ = l_Lean_Meta_mkOfEqTrueCore(v_e_3634_, v_he_3635_);
lean_inc(v_val_3703_);
lean_inc_ref(v_e_3702_);
v___x_3706_ = l_Lean_mkApp4(v___x_3704_, v_e_3634_, v_e_3702_, v_val_3703_, v___x_3705_);
v_h_3668_ = v___x_3706_;
v___y_3669_ = v___y_3690_;
v___y_3670_ = v___y_3691_;
v___y_3671_ = v___y_3692_;
v___y_3672_ = v___y_3693_;
v___y_3673_ = v___y_3694_;
v___y_3674_ = v___y_3695_;
v___y_3675_ = v___y_3696_;
v___y_3676_ = v___y_3697_;
v___y_3677_ = v___y_3698_;
v___y_3678_ = v___y_3699_;
v___y_3679_ = v___y_3700_;
goto v___jp_3667_;
}
else
{
lean_object* v___x_3707_; 
v___x_3707_ = l_Lean_Meta_mkOfEqTrueCore(v_e_3634_, v_he_3635_);
v_h_3668_ = v___x_3707_;
v___y_3669_ = v___y_3690_;
v___y_3670_ = v___y_3691_;
v___y_3671_ = v___y_3692_;
v___y_3672_ = v___y_3693_;
v___y_3673_ = v___y_3694_;
v___y_3674_ = v___y_3695_;
v___y_3675_ = v___y_3696_;
v___y_3676_ = v___y_3697_;
v___y_3677_ = v___y_3698_;
v___y_3678_ = v___y_3699_;
v___y_3679_ = v___y_3700_;
goto v___jp_3667_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___boxed(lean_object* v_c_3726_, lean_object* v_e_3727_, lean_object* v_he_3728_, lean_object* v_a_3729_, lean_object* v_a_3730_, lean_object* v_a_3731_, lean_object* v_a_3732_, lean_object* v_a_3733_, lean_object* v_a_3734_, lean_object* v_a_3735_, lean_object* v_a_3736_, lean_object* v_a_3737_, lean_object* v_a_3738_, lean_object* v_a_3739_, lean_object* v_a_3740_){
_start:
{
lean_object* v_res_3741_; 
v_res_3741_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue(v_c_3726_, v_e_3727_, v_he_3728_, v_a_3729_, v_a_3730_, v_a_3731_, v_a_3732_, v_a_3733_, v_a_3734_, v_a_3735_, v_a_3736_, v_a_3737_, v_a_3738_, v_a_3739_);
lean_dec(v_a_3739_);
lean_dec_ref(v_a_3738_);
lean_dec(v_a_3737_);
lean_dec_ref(v_a_3736_);
lean_dec(v_a_3735_);
lean_dec_ref(v_a_3734_);
lean_dec(v_a_3733_);
lean_dec_ref(v_a_3732_);
lean_dec(v_a_3731_);
lean_dec(v_a_3730_);
lean_dec(v_a_3729_);
return v_res_3741_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__2(void){
_start:
{
lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; 
v___x_3748_ = lean_box(0);
v___x_3749_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__1));
v___x_3750_ = l_Lean_mkConst(v___x_3749_, v___x_3748_);
return v___x_3750_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__3(void){
_start:
{
lean_object* v___x_3751_; lean_object* v___x_3752_; 
v___x_3751_ = lean_unsigned_to_nat(1u);
v___x_3752_ = lean_nat_to_int(v___x_3751_);
return v___x_3752_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4(void){
_start:
{
lean_object* v___x_3753_; lean_object* v___x_3754_; 
v___x_3753_ = lean_unsigned_to_nat(0u);
v___x_3754_ = lean_nat_to_int(v___x_3753_);
return v___x_3754_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__8(void){
_start:
{
lean_object* v___x_3760_; lean_object* v___x_3761_; 
v___x_3760_ = lean_unsigned_to_nat(0u);
v___x_3761_ = l_Lean_Level_ofNat(v___x_3760_);
return v___x_3761_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__9(void){
_start:
{
lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; 
v___x_3762_ = lean_box(0);
v___x_3763_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__8, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__8);
v___x_3764_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3764_, 0, v___x_3763_);
lean_ctor_set(v___x_3764_, 1, v___x_3762_);
return v___x_3764_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10(void){
_start:
{
lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; 
v___x_3765_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__9, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__9);
v___x_3766_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__7));
v___x_3767_ = l_Lean_Expr_const___override(v___x_3766_, v___x_3765_);
return v___x_3767_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13(void){
_start:
{
lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; 
v___x_3771_ = lean_box(0);
v___x_3772_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__12));
v___x_3773_ = l_Lean_Expr_const___override(v___x_3772_, v___x_3771_);
return v___x_3773_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16(void){
_start:
{
lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; 
v___x_3778_ = lean_box(0);
v___x_3779_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__15));
v___x_3780_ = l_Lean_Expr_const___override(v___x_3779_, v___x_3778_);
return v___x_3780_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__29(void){
_start:
{
lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; 
v___x_3817_ = lean_box(0);
v___x_3818_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__28));
v___x_3819_ = l_Lean_mkConst(v___x_3818_, v___x_3817_);
return v___x_3819_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__31(void){
_start:
{
lean_object* v___x_3821_; lean_object* v___x_3822_; 
v___x_3821_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__30));
v___x_3822_ = l_Lean_stringToMessageData(v___x_3821_);
return v___x_3822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse(lean_object* v_c_3823_, lean_object* v_e_3824_, lean_object* v_he_3825_, lean_object* v_a_3826_, lean_object* v_a_3827_, lean_object* v_a_3828_, lean_object* v_a_3829_, lean_object* v_a_3830_, lean_object* v_a_3831_, lean_object* v_a_3832_, lean_object* v_a_3833_, lean_object* v_a_3834_, lean_object* v_a_3835_, lean_object* v_a_3836_){
_start:
{
lean_object* v___y_3839_; lean_object* v___y_3840_; lean_object* v_k_x27_3841_; lean_object* v_h_3842_; uint8_t v_strict_3843_; lean_object* v___y_3844_; lean_object* v___y_3845_; lean_object* v___y_3846_; lean_object* v___y_3847_; lean_object* v___y_3848_; lean_object* v___y_3849_; lean_object* v___y_3850_; lean_object* v___y_3851_; lean_object* v___y_3852_; lean_object* v___y_3853_; lean_object* v___y_3854_; lean_object* v___y_3858_; lean_object* v___y_3859_; lean_object* v___y_3860_; lean_object* v___y_3861_; lean_object* v___y_3862_; lean_object* v___y_3863_; lean_object* v___y_3864_; lean_object* v___y_3865_; lean_object* v___y_3866_; lean_object* v___y_3867_; lean_object* v___y_3868_; lean_object* v___y_3869_; lean_object* v___y_3870_; lean_object* v___y_3871_; lean_object* v___y_3872_; lean_object* v___y_3873_; lean_object* v___y_3874_; lean_object* v___y_3875_; lean_object* v___y_3876_; lean_object* v___y_3877_; lean_object* v___y_3878_; lean_object* v___y_3882_; lean_object* v___y_3883_; lean_object* v___y_3884_; lean_object* v___y_3885_; lean_object* v___y_3886_; lean_object* v___y_3887_; lean_object* v___y_3888_; lean_object* v___y_3889_; lean_object* v___y_3890_; lean_object* v___y_3891_; lean_object* v___y_3892_; lean_object* v___y_3893_; lean_object* v___y_3894_; lean_object* v___y_3895_; lean_object* v___y_3896_; lean_object* v___y_3897_; lean_object* v___y_3898_; uint8_t v___y_3899_; lean_object* v___x_3945_; 
v___x_3945_ = l_Lean_Meta_Grind_Order_isLinearPreorder(v_a_3826_, v_a_3827_, v_a_3828_, v_a_3829_, v_a_3830_, v_a_3831_, v_a_3832_, v_a_3833_, v_a_3834_, v_a_3835_, v_a_3836_);
if (lean_obj_tag(v___x_3945_) == 0)
{
lean_object* v_a_3946_; lean_object* v___x_3948_; uint8_t v_isShared_3949_; uint8_t v_isSharedCheck_4268_; 
v_a_3946_ = lean_ctor_get(v___x_3945_, 0);
v_isSharedCheck_4268_ = !lean_is_exclusive(v___x_3945_);
if (v_isSharedCheck_4268_ == 0)
{
v___x_3948_ = v___x_3945_;
v_isShared_3949_ = v_isSharedCheck_4268_;
goto v_resetjp_3947_;
}
else
{
lean_inc(v_a_3946_);
lean_dec(v___x_3945_);
v___x_3948_ = lean_box(0);
v_isShared_3949_ = v_isSharedCheck_4268_;
goto v_resetjp_3947_;
}
v_resetjp_3947_:
{
lean_object* v___y_3951_; lean_object* v___y_3952_; lean_object* v___y_3953_; lean_object* v___y_3954_; lean_object* v___y_3955_; lean_object* v___y_3956_; lean_object* v___y_3957_; lean_object* v___y_3958_; lean_object* v___y_3959_; lean_object* v___y_3960_; lean_object* v___y_3961_; uint8_t v___y_3962_; lean_object* v___y_3963_; lean_object* v___y_3964_; lean_object* v___y_3965_; lean_object* v___y_3966_; lean_object* v___y_3967_; lean_object* v___y_3968_; lean_object* v___y_3969_; lean_object* v___y_3970_; lean_object* v___y_3971_; lean_object* v___y_3977_; lean_object* v___y_3978_; lean_object* v___y_3979_; lean_object* v___y_3980_; lean_object* v___y_3981_; lean_object* v___y_3982_; lean_object* v___y_3983_; lean_object* v___y_3984_; lean_object* v___y_3985_; lean_object* v___y_3986_; lean_object* v___y_3987_; lean_object* v___y_3988_; uint8_t v___y_3989_; lean_object* v___y_3990_; lean_object* v___y_3991_; lean_object* v___y_3992_; lean_object* v___y_3993_; lean_object* v___y_3994_; lean_object* v___y_3995_; lean_object* v___y_3996_; lean_object* v___y_4009_; lean_object* v___y_4010_; lean_object* v___y_4011_; lean_object* v___y_4012_; lean_object* v___y_4013_; lean_object* v___y_4014_; lean_object* v___y_4015_; uint8_t v___y_4016_; lean_object* v___y_4017_; lean_object* v___y_4018_; lean_object* v___y_4019_; lean_object* v___y_4020_; lean_object* v___y_4021_; lean_object* v___y_4022_; lean_object* v___y_4023_; lean_object* v___y_4024_; lean_object* v___y_4025_; lean_object* v_h_4068_; lean_object* v___y_4069_; lean_object* v___y_4070_; lean_object* v___y_4071_; lean_object* v___y_4072_; lean_object* v___y_4073_; lean_object* v___y_4074_; lean_object* v___y_4075_; lean_object* v___y_4076_; lean_object* v___y_4077_; lean_object* v___y_4078_; lean_object* v___y_4079_; lean_object* v___y_4225_; lean_object* v___y_4226_; lean_object* v___y_4227_; lean_object* v___y_4228_; lean_object* v___y_4229_; lean_object* v___y_4230_; lean_object* v___y_4231_; lean_object* v___y_4232_; lean_object* v___y_4233_; lean_object* v___y_4234_; lean_object* v___y_4235_; uint8_t v___x_4243_; 
v___x_4243_ = lean_unbox(v_a_3946_);
if (v___x_4243_ == 0)
{
lean_object* v___x_4244_; lean_object* v___x_4246_; 
lean_dec(v_a_3946_);
lean_dec_ref(v_he_3825_);
lean_dec_ref(v_e_3824_);
lean_dec_ref(v_c_3823_);
v___x_4244_ = lean_box(0);
if (v_isShared_3949_ == 0)
{
lean_ctor_set(v___x_3948_, 0, v___x_4244_);
v___x_4246_ = v___x_3948_;
goto v_reusejp_4245_;
}
else
{
lean_object* v_reuseFailAlloc_4247_; 
v_reuseFailAlloc_4247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4247_, 0, v___x_4244_);
v___x_4246_ = v_reuseFailAlloc_4247_;
goto v_reusejp_4245_;
}
v_reusejp_4245_:
{
return v___x_4246_;
}
}
else
{
lean_object* v_toCold_4248_; lean_object* v_options_4249_; uint8_t v_hasTrace_4250_; 
lean_del_object(v___x_3948_);
v_toCold_4248_ = lean_ctor_get(v_a_3835_, 0);
v_options_4249_ = lean_ctor_get(v_toCold_4248_, 2);
v_hasTrace_4250_ = lean_ctor_get_uint8(v_options_4249_, sizeof(void*)*1);
if (v_hasTrace_4250_ == 0)
{
v___y_4225_ = v_a_3826_;
v___y_4226_ = v_a_3827_;
v___y_4227_ = v_a_3828_;
v___y_4228_ = v_a_3829_;
v___y_4229_ = v_a_3830_;
v___y_4230_ = v_a_3831_;
v___y_4231_ = v_a_3832_;
v___y_4232_ = v_a_3833_;
v___y_4233_ = v_a_3834_;
v___y_4234_ = v_a_3835_;
v___y_4235_ = v_a_3836_;
goto v___jp_4224_;
}
else
{
lean_object* v_inheritedTraceOptions_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; uint8_t v___x_4254_; 
v_inheritedTraceOptions_4251_ = lean_ctor_get(v_toCold_4248_, 11);
v___x_4252_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__4));
v___x_4253_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5);
v___x_4254_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4251_, v_options_4249_, v___x_4253_);
if (v___x_4254_ == 0)
{
v___y_4225_ = v_a_3826_;
v___y_4226_ = v_a_3827_;
v___y_4227_ = v_a_3828_;
v___y_4228_ = v_a_3829_;
v___y_4229_ = v_a_3830_;
v___y_4230_ = v_a_3831_;
v___y_4231_ = v_a_3832_;
v___y_4232_ = v_a_3833_;
v___y_4233_ = v_a_3834_;
v___y_4234_ = v_a_3835_;
v___y_4235_ = v_a_3836_;
goto v___jp_4224_;
}
else
{
lean_object* v___x_4255_; 
v___x_4255_ = l_Lean_Meta_Grind_Order_Cnstr_pp___redArg(v_c_3823_, v_a_3826_, v_a_3827_, v_a_3835_);
if (lean_obj_tag(v___x_4255_) == 0)
{
lean_object* v_a_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; 
v_a_4256_ = lean_ctor_get(v___x_4255_, 0);
lean_inc(v_a_4256_);
lean_dec_ref_known(v___x_4255_, 1);
v___x_4257_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__31, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__31_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__31);
v___x_4258_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4258_, 0, v___x_4257_);
lean_ctor_set(v___x_4258_, 1, v_a_4256_);
v___x_4259_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(v___x_4252_, v___x_4258_, v_a_3833_, v_a_3834_, v_a_3835_, v_a_3836_);
if (lean_obj_tag(v___x_4259_) == 0)
{
lean_dec_ref_known(v___x_4259_, 1);
v___y_4225_ = v_a_3826_;
v___y_4226_ = v_a_3827_;
v___y_4227_ = v_a_3828_;
v___y_4228_ = v_a_3829_;
v___y_4229_ = v_a_3830_;
v___y_4230_ = v_a_3831_;
v___y_4231_ = v_a_3832_;
v___y_4232_ = v_a_3833_;
v___y_4233_ = v_a_3834_;
v___y_4234_ = v_a_3835_;
v___y_4235_ = v_a_3836_;
goto v___jp_4224_;
}
else
{
lean_dec(v_a_3946_);
lean_dec_ref(v_he_3825_);
lean_dec_ref(v_e_3824_);
lean_dec_ref(v_c_3823_);
return v___x_4259_;
}
}
else
{
lean_object* v_a_4260_; lean_object* v___x_4262_; uint8_t v_isShared_4263_; uint8_t v_isSharedCheck_4267_; 
lean_dec(v_a_3946_);
lean_dec_ref(v_he_3825_);
lean_dec_ref(v_e_3824_);
lean_dec_ref(v_c_3823_);
v_a_4260_ = lean_ctor_get(v___x_4255_, 0);
v_isSharedCheck_4267_ = !lean_is_exclusive(v___x_4255_);
if (v_isSharedCheck_4267_ == 0)
{
v___x_4262_ = v___x_4255_;
v_isShared_4263_ = v_isSharedCheck_4267_;
goto v_resetjp_4261_;
}
else
{
lean_inc(v_a_4260_);
lean_dec(v___x_4255_);
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
}
}
v___jp_3950_:
{
lean_object* v___x_3972_; lean_object* v___x_3973_; 
v___x_3972_ = l_Lean_eagerReflBoolTrue;
lean_inc_ref(v___y_3971_);
v___x_3973_ = l_Lean_mkApp6(v___y_3960_, v___y_3954_, v___y_3952_, v___y_3965_, v___y_3971_, v___x_3972_, v___y_3961_);
if (v___y_3962_ == 0)
{
uint8_t v___x_3974_; 
v___x_3974_ = lean_unbox(v_a_3946_);
lean_dec(v_a_3946_);
v___y_3882_ = v___y_3951_;
v___y_3883_ = v___y_3971_;
v___y_3884_ = v___y_3953_;
v___y_3885_ = v___y_3955_;
v___y_3886_ = v___y_3956_;
v___y_3887_ = v___y_3957_;
v___y_3888_ = v___y_3958_;
v___y_3889_ = v___y_3959_;
v___y_3890_ = v___x_3972_;
v___y_3891_ = v___x_3973_;
v___y_3892_ = v___y_3963_;
v___y_3893_ = v___y_3964_;
v___y_3894_ = v___y_3966_;
v___y_3895_ = v___y_3967_;
v___y_3896_ = v___y_3970_;
v___y_3897_ = v___y_3969_;
v___y_3898_ = v___y_3968_;
v___y_3899_ = v___x_3974_;
goto v___jp_3881_;
}
else
{
uint8_t v___x_3975_; 
lean_dec(v_a_3946_);
v___x_3975_ = 0;
v___y_3882_ = v___y_3951_;
v___y_3883_ = v___y_3971_;
v___y_3884_ = v___y_3953_;
v___y_3885_ = v___y_3955_;
v___y_3886_ = v___y_3956_;
v___y_3887_ = v___y_3957_;
v___y_3888_ = v___y_3958_;
v___y_3889_ = v___y_3959_;
v___y_3890_ = v___x_3972_;
v___y_3891_ = v___x_3973_;
v___y_3892_ = v___y_3963_;
v___y_3893_ = v___y_3964_;
v___y_3894_ = v___y_3966_;
v___y_3895_ = v___y_3967_;
v___y_3896_ = v___y_3970_;
v___y_3897_ = v___y_3969_;
v___y_3898_ = v___y_3968_;
v___y_3899_ = v___x_3975_;
goto v___jp_3881_;
}
}
v___jp_3976_:
{
lean_object* v___x_3997_; uint8_t v___x_3998_; 
v___x_3997_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4);
v___x_3998_ = lean_int_dec_le(v___x_3997_, v___y_3977_);
if (v___x_3998_ == 0)
{
lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; 
v___x_3999_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10);
v___x_4000_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13);
v___x_4001_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16);
v___x_4002_ = lean_int_neg(v___y_3977_);
v___x_4003_ = l_Int_toNat(v___x_4002_);
lean_dec(v___x_4002_);
v___x_4004_ = l_Lean_instToExprInt_mkNat(v___x_4003_);
v___x_4005_ = l_Lean_mkApp3(v___x_3999_, v___x_4000_, v___x_4001_, v___x_4004_);
v___y_3951_ = v___y_3977_;
v___y_3952_ = v___y_3978_;
v___y_3953_ = v___y_3979_;
v___y_3954_ = v___y_3980_;
v___y_3955_ = v___y_3981_;
v___y_3956_ = v___y_3982_;
v___y_3957_ = v___y_3983_;
v___y_3958_ = v___y_3984_;
v___y_3959_ = v___y_3985_;
v___y_3960_ = v___y_3986_;
v___y_3961_ = v___y_3987_;
v___y_3962_ = v___y_3989_;
v___y_3963_ = v___y_3988_;
v___y_3964_ = v___y_3990_;
v___y_3965_ = v___y_3996_;
v___y_3966_ = v___y_3991_;
v___y_3967_ = v___y_3992_;
v___y_3968_ = v___y_3995_;
v___y_3969_ = v___y_3994_;
v___y_3970_ = v___y_3993_;
v___y_3971_ = v___x_4005_;
goto v___jp_3950_;
}
else
{
lean_object* v___x_4006_; lean_object* v___x_4007_; 
v___x_4006_ = l_Int_toNat(v___y_3977_);
v___x_4007_ = l_Lean_instToExprInt_mkNat(v___x_4006_);
v___y_3951_ = v___y_3977_;
v___y_3952_ = v___y_3978_;
v___y_3953_ = v___y_3979_;
v___y_3954_ = v___y_3980_;
v___y_3955_ = v___y_3981_;
v___y_3956_ = v___y_3982_;
v___y_3957_ = v___y_3983_;
v___y_3958_ = v___y_3984_;
v___y_3959_ = v___y_3985_;
v___y_3960_ = v___y_3986_;
v___y_3961_ = v___y_3987_;
v___y_3962_ = v___y_3989_;
v___y_3963_ = v___y_3988_;
v___y_3964_ = v___y_3990_;
v___y_3965_ = v___y_3996_;
v___y_3966_ = v___y_3991_;
v___y_3967_ = v___y_3992_;
v___y_3968_ = v___y_3995_;
v___y_3969_ = v___y_3994_;
v___y_3970_ = v___y_3993_;
v___y_3971_ = v___x_4007_;
goto v___jp_3950_;
}
}
v___jp_4008_:
{
lean_object* v___x_4026_; 
lean_inc(v___y_4025_);
v___x_4026_ = l_Lean_Meta_Grind_Order_mkLinearOrdRingPrefix(v___y_4025_, v___y_4022_, v___y_4012_, v___y_4018_, v___y_4023_, v___y_4014_, v___y_4010_, v___y_4009_, v___y_4011_, v___y_4017_, v___y_4013_, v___y_4024_);
if (lean_obj_tag(v___x_4026_) == 0)
{
lean_object* v_a_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; 
v_a_4027_ = lean_ctor_get(v___x_4026_, 0);
lean_inc(v_a_4027_);
lean_dec_ref_known(v___x_4026_, 1);
v___x_4028_ = lean_int_neg(v___y_4020_);
v___x_4029_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v___y_4021_, v___y_4022_, v___y_4012_, v___y_4013_);
if (lean_obj_tag(v___x_4029_) == 0)
{
lean_object* v_a_4030_; lean_object* v___x_4031_; 
v_a_4030_ = lean_ctor_get(v___x_4029_, 0);
lean_inc(v_a_4030_);
lean_dec_ref_known(v___x_4029_, 1);
v___x_4031_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v___y_4019_, v___y_4022_, v___y_4012_, v___y_4013_);
if (lean_obj_tag(v___x_4031_) == 0)
{
lean_object* v_a_4032_; lean_object* v___x_4033_; uint8_t v___x_4034_; 
v_a_4032_ = lean_ctor_get(v___x_4031_, 0);
lean_inc(v_a_4032_);
lean_dec_ref_known(v___x_4031_, 1);
v___x_4033_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4);
v___x_4034_ = lean_int_dec_le(v___x_4033_, v___y_4020_);
if (v___x_4034_ == 0)
{
lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; 
lean_dec(v___y_4020_);
v___x_4035_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10);
v___x_4036_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13);
v___x_4037_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16);
v___x_4038_ = l_Int_toNat(v___x_4028_);
v___x_4039_ = l_Lean_instToExprInt_mkNat(v___x_4038_);
v___x_4040_ = l_Lean_mkApp3(v___x_4035_, v___x_4036_, v___x_4037_, v___x_4039_);
v___y_3977_ = v___x_4028_;
v___y_3978_ = v_a_4032_;
v___y_3979_ = v___y_4009_;
v___y_3980_ = v_a_4030_;
v___y_3981_ = v___y_4010_;
v___y_3982_ = v___y_4011_;
v___y_3983_ = v___y_4012_;
v___y_3984_ = v___y_4013_;
v___y_3985_ = v___y_4014_;
v___y_3986_ = v_a_4027_;
v___y_3987_ = v___y_4015_;
v___y_3988_ = v___y_4017_;
v___y_3989_ = v___y_4016_;
v___y_3990_ = v___y_4018_;
v___y_3991_ = v___y_4019_;
v___y_3992_ = v___y_4021_;
v___y_3993_ = v___y_4022_;
v___y_3994_ = v___y_4023_;
v___y_3995_ = v___y_4024_;
v___y_3996_ = v___x_4040_;
goto v___jp_3976_;
}
else
{
lean_object* v___x_4041_; lean_object* v___x_4042_; 
v___x_4041_ = l_Int_toNat(v___y_4020_);
lean_dec(v___y_4020_);
v___x_4042_ = l_Lean_instToExprInt_mkNat(v___x_4041_);
v___y_3977_ = v___x_4028_;
v___y_3978_ = v_a_4032_;
v___y_3979_ = v___y_4009_;
v___y_3980_ = v_a_4030_;
v___y_3981_ = v___y_4010_;
v___y_3982_ = v___y_4011_;
v___y_3983_ = v___y_4012_;
v___y_3984_ = v___y_4013_;
v___y_3985_ = v___y_4014_;
v___y_3986_ = v_a_4027_;
v___y_3987_ = v___y_4015_;
v___y_3988_ = v___y_4017_;
v___y_3989_ = v___y_4016_;
v___y_3990_ = v___y_4018_;
v___y_3991_ = v___y_4019_;
v___y_3992_ = v___y_4021_;
v___y_3993_ = v___y_4022_;
v___y_3994_ = v___y_4023_;
v___y_3995_ = v___y_4024_;
v___y_3996_ = v___x_4042_;
goto v___jp_3976_;
}
}
else
{
lean_object* v_a_4043_; lean_object* v___x_4045_; uint8_t v_isShared_4046_; uint8_t v_isSharedCheck_4050_; 
lean_dec(v_a_4030_);
lean_dec(v___x_4028_);
lean_dec(v_a_4027_);
lean_dec(v___y_4021_);
lean_dec(v___y_4020_);
lean_dec(v___y_4019_);
lean_dec_ref(v___y_4015_);
lean_dec(v_a_3946_);
v_a_4043_ = lean_ctor_get(v___x_4031_, 0);
v_isSharedCheck_4050_ = !lean_is_exclusive(v___x_4031_);
if (v_isSharedCheck_4050_ == 0)
{
v___x_4045_ = v___x_4031_;
v_isShared_4046_ = v_isSharedCheck_4050_;
goto v_resetjp_4044_;
}
else
{
lean_inc(v_a_4043_);
lean_dec(v___x_4031_);
v___x_4045_ = lean_box(0);
v_isShared_4046_ = v_isSharedCheck_4050_;
goto v_resetjp_4044_;
}
v_resetjp_4044_:
{
lean_object* v___x_4048_; 
if (v_isShared_4046_ == 0)
{
v___x_4048_ = v___x_4045_;
goto v_reusejp_4047_;
}
else
{
lean_object* v_reuseFailAlloc_4049_; 
v_reuseFailAlloc_4049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4049_, 0, v_a_4043_);
v___x_4048_ = v_reuseFailAlloc_4049_;
goto v_reusejp_4047_;
}
v_reusejp_4047_:
{
return v___x_4048_;
}
}
}
}
else
{
lean_object* v_a_4051_; lean_object* v___x_4053_; uint8_t v_isShared_4054_; uint8_t v_isSharedCheck_4058_; 
lean_dec(v___x_4028_);
lean_dec(v_a_4027_);
lean_dec(v___y_4021_);
lean_dec(v___y_4020_);
lean_dec(v___y_4019_);
lean_dec_ref(v___y_4015_);
lean_dec(v_a_3946_);
v_a_4051_ = lean_ctor_get(v___x_4029_, 0);
v_isSharedCheck_4058_ = !lean_is_exclusive(v___x_4029_);
if (v_isSharedCheck_4058_ == 0)
{
v___x_4053_ = v___x_4029_;
v_isShared_4054_ = v_isSharedCheck_4058_;
goto v_resetjp_4052_;
}
else
{
lean_inc(v_a_4051_);
lean_dec(v___x_4029_);
v___x_4053_ = lean_box(0);
v_isShared_4054_ = v_isSharedCheck_4058_;
goto v_resetjp_4052_;
}
v_resetjp_4052_:
{
lean_object* v___x_4056_; 
if (v_isShared_4054_ == 0)
{
v___x_4056_ = v___x_4053_;
goto v_reusejp_4055_;
}
else
{
lean_object* v_reuseFailAlloc_4057_; 
v_reuseFailAlloc_4057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4057_, 0, v_a_4051_);
v___x_4056_ = v_reuseFailAlloc_4057_;
goto v_reusejp_4055_;
}
v_reusejp_4055_:
{
return v___x_4056_;
}
}
}
}
else
{
lean_object* v_a_4059_; lean_object* v___x_4061_; uint8_t v_isShared_4062_; uint8_t v_isSharedCheck_4066_; 
lean_dec(v___y_4021_);
lean_dec(v___y_4020_);
lean_dec(v___y_4019_);
lean_dec_ref(v___y_4015_);
lean_dec(v_a_3946_);
v_a_4059_ = lean_ctor_get(v___x_4026_, 0);
v_isSharedCheck_4066_ = !lean_is_exclusive(v___x_4026_);
if (v_isSharedCheck_4066_ == 0)
{
v___x_4061_ = v___x_4026_;
v_isShared_4062_ = v_isSharedCheck_4066_;
goto v_resetjp_4060_;
}
else
{
lean_inc(v_a_4059_);
lean_dec(v___x_4026_);
v___x_4061_ = lean_box(0);
v_isShared_4062_ = v_isSharedCheck_4066_;
goto v_resetjp_4060_;
}
v_resetjp_4060_:
{
lean_object* v___x_4064_; 
if (v_isShared_4062_ == 0)
{
v___x_4064_ = v___x_4061_;
goto v_reusejp_4063_;
}
else
{
lean_object* v_reuseFailAlloc_4065_; 
v_reuseFailAlloc_4065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4065_, 0, v_a_4059_);
v___x_4064_ = v_reuseFailAlloc_4065_;
goto v_reusejp_4063_;
}
v_reusejp_4063_:
{
return v___x_4064_;
}
}
}
}
v___jp_4067_:
{
lean_object* v___x_4080_; 
v___x_4080_ = l_Lean_Meta_Grind_Order_isRing(v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_);
if (lean_obj_tag(v___x_4080_) == 0)
{
lean_object* v_a_4081_; uint8_t v___x_4082_; 
v_a_4081_ = lean_ctor_get(v___x_4080_, 0);
lean_inc(v_a_4081_);
lean_dec_ref_known(v___x_4080_, 1);
v___x_4082_ = lean_unbox(v_a_4081_);
if (v___x_4082_ == 0)
{
uint8_t v_kind_4083_; 
v_kind_4083_ = lean_ctor_get_uint8(v_c_3823_, sizeof(void*)*5);
if (v_kind_4083_ == 1)
{
lean_object* v_u_4084_; lean_object* v_v_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; 
lean_dec(v_a_3946_);
v_u_4084_ = lean_ctor_get(v_c_3823_, 0);
lean_inc(v_u_4084_);
v_v_4085_ = lean_ctor_get(v_c_3823_, 1);
lean_inc(v_v_4085_);
lean_dec_ref(v_c_3823_);
v___x_4086_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__18));
v___x_4087_ = l_Lean_Meta_Grind_Order_mkLeLtLinearPrefix(v___x_4086_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_);
if (lean_obj_tag(v___x_4087_) == 0)
{
lean_object* v_a_4088_; lean_object* v___x_4089_; 
v_a_4088_ = lean_ctor_get(v___x_4087_, 0);
lean_inc(v_a_4088_);
lean_dec_ref_known(v___x_4087_, 1);
v___x_4089_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_u_4084_, v___y_4069_, v___y_4070_, v___y_4078_);
if (lean_obj_tag(v___x_4089_) == 0)
{
lean_object* v_a_4090_; lean_object* v___x_4091_; 
v_a_4090_ = lean_ctor_get(v___x_4089_, 0);
lean_inc(v_a_4090_);
lean_dec_ref_known(v___x_4089_, 1);
v___x_4091_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_v_4085_, v___y_4069_, v___y_4070_, v___y_4078_);
if (lean_obj_tag(v___x_4091_) == 0)
{
lean_object* v_a_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; uint8_t v___x_4096_; lean_object* v___x_4097_; 
v_a_4092_ = lean_ctor_get(v___x_4091_, 0);
lean_inc(v_a_4092_);
lean_dec_ref_known(v___x_4091_, 1);
v___x_4093_ = l_Lean_mkApp3(v_a_4088_, v_a_4090_, v_a_4092_, v_h_4068_);
v___x_4094_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4);
v___x_4095_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4095_, 0, v___x_4094_);
v___x_4096_ = lean_unbox(v_a_4081_);
lean_dec(v_a_4081_);
lean_ctor_set_uint8(v___x_4095_, sizeof(void*)*1, v___x_4096_);
v___x_4097_ = l_Lean_Meta_Grind_Order_addEdge(v_v_4085_, v_u_4084_, v___x_4095_, v___x_4093_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_);
return v___x_4097_;
}
else
{
lean_object* v_a_4098_; lean_object* v___x_4100_; uint8_t v_isShared_4101_; uint8_t v_isSharedCheck_4105_; 
lean_dec(v_a_4090_);
lean_dec(v_a_4088_);
lean_dec(v_v_4085_);
lean_dec(v_u_4084_);
lean_dec(v_a_4081_);
lean_dec_ref(v_h_4068_);
v_a_4098_ = lean_ctor_get(v___x_4091_, 0);
v_isSharedCheck_4105_ = !lean_is_exclusive(v___x_4091_);
if (v_isSharedCheck_4105_ == 0)
{
v___x_4100_ = v___x_4091_;
v_isShared_4101_ = v_isSharedCheck_4105_;
goto v_resetjp_4099_;
}
else
{
lean_inc(v_a_4098_);
lean_dec(v___x_4091_);
v___x_4100_ = lean_box(0);
v_isShared_4101_ = v_isSharedCheck_4105_;
goto v_resetjp_4099_;
}
v_resetjp_4099_:
{
lean_object* v___x_4103_; 
if (v_isShared_4101_ == 0)
{
v___x_4103_ = v___x_4100_;
goto v_reusejp_4102_;
}
else
{
lean_object* v_reuseFailAlloc_4104_; 
v_reuseFailAlloc_4104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4104_, 0, v_a_4098_);
v___x_4103_ = v_reuseFailAlloc_4104_;
goto v_reusejp_4102_;
}
v_reusejp_4102_:
{
return v___x_4103_;
}
}
}
}
else
{
lean_object* v_a_4106_; lean_object* v___x_4108_; uint8_t v_isShared_4109_; uint8_t v_isSharedCheck_4113_; 
lean_dec(v_a_4088_);
lean_dec(v_v_4085_);
lean_dec(v_u_4084_);
lean_dec(v_a_4081_);
lean_dec_ref(v_h_4068_);
v_a_4106_ = lean_ctor_get(v___x_4089_, 0);
v_isSharedCheck_4113_ = !lean_is_exclusive(v___x_4089_);
if (v_isSharedCheck_4113_ == 0)
{
v___x_4108_ = v___x_4089_;
v_isShared_4109_ = v_isSharedCheck_4113_;
goto v_resetjp_4107_;
}
else
{
lean_inc(v_a_4106_);
lean_dec(v___x_4089_);
v___x_4108_ = lean_box(0);
v_isShared_4109_ = v_isSharedCheck_4113_;
goto v_resetjp_4107_;
}
v_resetjp_4107_:
{
lean_object* v___x_4111_; 
if (v_isShared_4109_ == 0)
{
v___x_4111_ = v___x_4108_;
goto v_reusejp_4110_;
}
else
{
lean_object* v_reuseFailAlloc_4112_; 
v_reuseFailAlloc_4112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4112_, 0, v_a_4106_);
v___x_4111_ = v_reuseFailAlloc_4112_;
goto v_reusejp_4110_;
}
v_reusejp_4110_:
{
return v___x_4111_;
}
}
}
}
else
{
lean_object* v_a_4114_; lean_object* v___x_4116_; uint8_t v_isShared_4117_; uint8_t v_isSharedCheck_4121_; 
lean_dec(v_v_4085_);
lean_dec(v_u_4084_);
lean_dec(v_a_4081_);
lean_dec_ref(v_h_4068_);
v_a_4114_ = lean_ctor_get(v___x_4087_, 0);
v_isSharedCheck_4121_ = !lean_is_exclusive(v___x_4087_);
if (v_isSharedCheck_4121_ == 0)
{
v___x_4116_ = v___x_4087_;
v_isShared_4117_ = v_isSharedCheck_4121_;
goto v_resetjp_4115_;
}
else
{
lean_inc(v_a_4114_);
lean_dec(v___x_4087_);
v___x_4116_ = lean_box(0);
v_isShared_4117_ = v_isSharedCheck_4121_;
goto v_resetjp_4115_;
}
v_resetjp_4115_:
{
lean_object* v___x_4119_; 
if (v_isShared_4117_ == 0)
{
v___x_4119_ = v___x_4116_;
goto v_reusejp_4118_;
}
else
{
lean_object* v_reuseFailAlloc_4120_; 
v_reuseFailAlloc_4120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4120_, 0, v_a_4114_);
v___x_4119_ = v_reuseFailAlloc_4120_;
goto v_reusejp_4118_;
}
v_reusejp_4118_:
{
return v___x_4119_;
}
}
}
}
else
{
lean_object* v_u_4122_; lean_object* v_v_4123_; lean_object* v___x_4124_; 
lean_dec(v_a_4081_);
v_u_4122_ = lean_ctor_get(v_c_3823_, 0);
lean_inc(v_u_4122_);
v_v_4123_ = lean_ctor_get(v_c_3823_, 1);
lean_inc(v_v_4123_);
lean_dec_ref(v_c_3823_);
v___x_4124_ = l_Lean_Meta_Grind_Order_hasLt(v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_);
if (lean_obj_tag(v___x_4124_) == 0)
{
lean_object* v_a_4125_; uint8_t v___x_4126_; 
v_a_4125_ = lean_ctor_get(v___x_4124_, 0);
lean_inc(v_a_4125_);
lean_dec_ref_known(v___x_4124_, 1);
v___x_4126_ = lean_unbox(v_a_4125_);
if (v___x_4126_ == 0)
{
lean_object* v___x_4127_; lean_object* v___x_4128_; 
lean_dec(v_a_3946_);
v___x_4127_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__20));
v___x_4128_ = l_Lean_Meta_Grind_Order_mkLeLinearPrefix(v___x_4127_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_);
if (lean_obj_tag(v___x_4128_) == 0)
{
lean_object* v_a_4129_; lean_object* v___x_4130_; 
v_a_4129_ = lean_ctor_get(v___x_4128_, 0);
lean_inc(v_a_4129_);
lean_dec_ref_known(v___x_4128_, 1);
v___x_4130_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_u_4122_, v___y_4069_, v___y_4070_, v___y_4078_);
if (lean_obj_tag(v___x_4130_) == 0)
{
lean_object* v_a_4131_; lean_object* v___x_4132_; 
v_a_4131_ = lean_ctor_get(v___x_4130_, 0);
lean_inc(v_a_4131_);
lean_dec_ref_known(v___x_4130_, 1);
v___x_4132_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_v_4123_, v___y_4069_, v___y_4070_, v___y_4078_);
if (lean_obj_tag(v___x_4132_) == 0)
{
lean_object* v_a_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; uint8_t v___x_4137_; lean_object* v___x_4138_; 
v_a_4133_ = lean_ctor_get(v___x_4132_, 0);
lean_inc(v_a_4133_);
lean_dec_ref_known(v___x_4132_, 1);
v___x_4134_ = l_Lean_mkApp3(v_a_4129_, v_a_4131_, v_a_4133_, v_h_4068_);
v___x_4135_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4);
v___x_4136_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4136_, 0, v___x_4135_);
v___x_4137_ = lean_unbox(v_a_4125_);
lean_dec(v_a_4125_);
lean_ctor_set_uint8(v___x_4136_, sizeof(void*)*1, v___x_4137_);
v___x_4138_ = l_Lean_Meta_Grind_Order_addEdge(v_v_4123_, v_u_4122_, v___x_4136_, v___x_4134_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_);
return v___x_4138_;
}
else
{
lean_object* v_a_4139_; lean_object* v___x_4141_; uint8_t v_isShared_4142_; uint8_t v_isSharedCheck_4146_; 
lean_dec(v_a_4131_);
lean_dec(v_a_4129_);
lean_dec(v_a_4125_);
lean_dec(v_v_4123_);
lean_dec(v_u_4122_);
lean_dec_ref(v_h_4068_);
v_a_4139_ = lean_ctor_get(v___x_4132_, 0);
v_isSharedCheck_4146_ = !lean_is_exclusive(v___x_4132_);
if (v_isSharedCheck_4146_ == 0)
{
v___x_4141_ = v___x_4132_;
v_isShared_4142_ = v_isSharedCheck_4146_;
goto v_resetjp_4140_;
}
else
{
lean_inc(v_a_4139_);
lean_dec(v___x_4132_);
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
lean_object* v_a_4147_; lean_object* v___x_4149_; uint8_t v_isShared_4150_; uint8_t v_isSharedCheck_4154_; 
lean_dec(v_a_4129_);
lean_dec(v_a_4125_);
lean_dec(v_v_4123_);
lean_dec(v_u_4122_);
lean_dec_ref(v_h_4068_);
v_a_4147_ = lean_ctor_get(v___x_4130_, 0);
v_isSharedCheck_4154_ = !lean_is_exclusive(v___x_4130_);
if (v_isSharedCheck_4154_ == 0)
{
v___x_4149_ = v___x_4130_;
v_isShared_4150_ = v_isSharedCheck_4154_;
goto v_resetjp_4148_;
}
else
{
lean_inc(v_a_4147_);
lean_dec(v___x_4130_);
v___x_4149_ = lean_box(0);
v_isShared_4150_ = v_isSharedCheck_4154_;
goto v_resetjp_4148_;
}
v_resetjp_4148_:
{
lean_object* v___x_4152_; 
if (v_isShared_4150_ == 0)
{
v___x_4152_ = v___x_4149_;
goto v_reusejp_4151_;
}
else
{
lean_object* v_reuseFailAlloc_4153_; 
v_reuseFailAlloc_4153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4153_, 0, v_a_4147_);
v___x_4152_ = v_reuseFailAlloc_4153_;
goto v_reusejp_4151_;
}
v_reusejp_4151_:
{
return v___x_4152_;
}
}
}
}
else
{
lean_object* v_a_4155_; lean_object* v___x_4157_; uint8_t v_isShared_4158_; uint8_t v_isSharedCheck_4162_; 
lean_dec(v_a_4125_);
lean_dec(v_v_4123_);
lean_dec(v_u_4122_);
lean_dec_ref(v_h_4068_);
v_a_4155_ = lean_ctor_get(v___x_4128_, 0);
v_isSharedCheck_4162_ = !lean_is_exclusive(v___x_4128_);
if (v_isSharedCheck_4162_ == 0)
{
v___x_4157_ = v___x_4128_;
v_isShared_4158_ = v_isSharedCheck_4162_;
goto v_resetjp_4156_;
}
else
{
lean_inc(v_a_4155_);
lean_dec(v___x_4128_);
v___x_4157_ = lean_box(0);
v_isShared_4158_ = v_isSharedCheck_4162_;
goto v_resetjp_4156_;
}
v_resetjp_4156_:
{
lean_object* v___x_4160_; 
if (v_isShared_4158_ == 0)
{
v___x_4160_ = v___x_4157_;
goto v_reusejp_4159_;
}
else
{
lean_object* v_reuseFailAlloc_4161_; 
v_reuseFailAlloc_4161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4161_, 0, v_a_4155_);
v___x_4160_ = v_reuseFailAlloc_4161_;
goto v_reusejp_4159_;
}
v_reusejp_4159_:
{
return v___x_4160_;
}
}
}
}
else
{
lean_object* v___x_4163_; lean_object* v___x_4164_; 
lean_dec(v_a_4125_);
v___x_4163_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__22));
v___x_4164_ = l_Lean_Meta_Grind_Order_mkLeLtLinearPrefix(v___x_4163_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_);
if (lean_obj_tag(v___x_4164_) == 0)
{
lean_object* v_a_4165_; lean_object* v___x_4166_; 
v_a_4165_ = lean_ctor_get(v___x_4164_, 0);
lean_inc(v_a_4165_);
lean_dec_ref_known(v___x_4164_, 1);
v___x_4166_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_u_4122_, v___y_4069_, v___y_4070_, v___y_4078_);
if (lean_obj_tag(v___x_4166_) == 0)
{
lean_object* v_a_4167_; lean_object* v___x_4168_; 
v_a_4167_ = lean_ctor_get(v___x_4166_, 0);
lean_inc(v_a_4167_);
lean_dec_ref_known(v___x_4166_, 1);
v___x_4168_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_v_4123_, v___y_4069_, v___y_4070_, v___y_4078_);
if (lean_obj_tag(v___x_4168_) == 0)
{
lean_object* v_a_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; uint8_t v___x_4173_; lean_object* v___x_4174_; 
v_a_4169_ = lean_ctor_get(v___x_4168_, 0);
lean_inc(v_a_4169_);
lean_dec_ref_known(v___x_4168_, 1);
v___x_4170_ = l_Lean_mkApp3(v_a_4165_, v_a_4167_, v_a_4169_, v_h_4068_);
v___x_4171_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4);
v___x_4172_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4172_, 0, v___x_4171_);
v___x_4173_ = lean_unbox(v_a_3946_);
lean_dec(v_a_3946_);
lean_ctor_set_uint8(v___x_4172_, sizeof(void*)*1, v___x_4173_);
v___x_4174_ = l_Lean_Meta_Grind_Order_addEdge(v_v_4123_, v_u_4122_, v___x_4172_, v___x_4170_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_);
return v___x_4174_;
}
else
{
lean_object* v_a_4175_; lean_object* v___x_4177_; uint8_t v_isShared_4178_; uint8_t v_isSharedCheck_4182_; 
lean_dec(v_a_4167_);
lean_dec(v_a_4165_);
lean_dec(v_v_4123_);
lean_dec(v_u_4122_);
lean_dec_ref(v_h_4068_);
lean_dec(v_a_3946_);
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
lean_dec(v_v_4123_);
lean_dec(v_u_4122_);
lean_dec_ref(v_h_4068_);
lean_dec(v_a_3946_);
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
lean_dec(v_v_4123_);
lean_dec(v_u_4122_);
lean_dec_ref(v_h_4068_);
lean_dec(v_a_3946_);
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
}
else
{
lean_object* v_a_4199_; lean_object* v___x_4201_; uint8_t v_isShared_4202_; uint8_t v_isSharedCheck_4206_; 
lean_dec(v_v_4123_);
lean_dec(v_u_4122_);
lean_dec_ref(v_h_4068_);
lean_dec(v_a_3946_);
v_a_4199_ = lean_ctor_get(v___x_4124_, 0);
v_isSharedCheck_4206_ = !lean_is_exclusive(v___x_4124_);
if (v_isSharedCheck_4206_ == 0)
{
v___x_4201_ = v___x_4124_;
v_isShared_4202_ = v_isSharedCheck_4206_;
goto v_resetjp_4200_;
}
else
{
lean_inc(v_a_4199_);
lean_dec(v___x_4124_);
v___x_4201_ = lean_box(0);
v_isShared_4202_ = v_isSharedCheck_4206_;
goto v_resetjp_4200_;
}
v_resetjp_4200_:
{
lean_object* v___x_4204_; 
if (v_isShared_4202_ == 0)
{
v___x_4204_ = v___x_4201_;
goto v_reusejp_4203_;
}
else
{
lean_object* v_reuseFailAlloc_4205_; 
v_reuseFailAlloc_4205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4205_, 0, v_a_4199_);
v___x_4204_ = v_reuseFailAlloc_4205_;
goto v_reusejp_4203_;
}
v_reusejp_4203_:
{
return v___x_4204_;
}
}
}
}
}
else
{
uint8_t v_kind_4207_; 
lean_dec(v_a_4081_);
v_kind_4207_ = lean_ctor_get_uint8(v_c_3823_, sizeof(void*)*5);
if (v_kind_4207_ == 1)
{
lean_object* v_u_4208_; lean_object* v_v_4209_; lean_object* v_k_4210_; lean_object* v___x_4211_; 
v_u_4208_ = lean_ctor_get(v_c_3823_, 0);
lean_inc(v_u_4208_);
v_v_4209_ = lean_ctor_get(v_c_3823_, 1);
lean_inc(v_v_4209_);
v_k_4210_ = lean_ctor_get(v_c_3823_, 2);
lean_inc(v_k_4210_);
lean_dec_ref(v_c_3823_);
v___x_4211_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__24));
v___y_4009_ = v___y_4075_;
v___y_4010_ = v___y_4074_;
v___y_4011_ = v___y_4076_;
v___y_4012_ = v___y_4070_;
v___y_4013_ = v___y_4078_;
v___y_4014_ = v___y_4073_;
v___y_4015_ = v_h_4068_;
v___y_4016_ = v_kind_4207_;
v___y_4017_ = v___y_4077_;
v___y_4018_ = v___y_4071_;
v___y_4019_ = v_v_4209_;
v___y_4020_ = v_k_4210_;
v___y_4021_ = v_u_4208_;
v___y_4022_ = v___y_4069_;
v___y_4023_ = v___y_4072_;
v___y_4024_ = v___y_4079_;
v___y_4025_ = v___x_4211_;
goto v___jp_4008_;
}
else
{
lean_object* v_u_4212_; lean_object* v_v_4213_; lean_object* v_k_4214_; lean_object* v___x_4215_; 
v_u_4212_ = lean_ctor_get(v_c_3823_, 0);
lean_inc(v_u_4212_);
v_v_4213_ = lean_ctor_get(v_c_3823_, 1);
lean_inc(v_v_4213_);
v_k_4214_ = lean_ctor_get(v_c_3823_, 2);
lean_inc(v_k_4214_);
lean_dec_ref(v_c_3823_);
v___x_4215_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__26));
v___y_4009_ = v___y_4075_;
v___y_4010_ = v___y_4074_;
v___y_4011_ = v___y_4076_;
v___y_4012_ = v___y_4070_;
v___y_4013_ = v___y_4078_;
v___y_4014_ = v___y_4073_;
v___y_4015_ = v_h_4068_;
v___y_4016_ = v_kind_4207_;
v___y_4017_ = v___y_4077_;
v___y_4018_ = v___y_4071_;
v___y_4019_ = v_v_4213_;
v___y_4020_ = v_k_4214_;
v___y_4021_ = v_u_4212_;
v___y_4022_ = v___y_4069_;
v___y_4023_ = v___y_4072_;
v___y_4024_ = v___y_4079_;
v___y_4025_ = v___x_4215_;
goto v___jp_4008_;
}
}
}
else
{
lean_object* v_a_4216_; lean_object* v___x_4218_; uint8_t v_isShared_4219_; uint8_t v_isSharedCheck_4223_; 
lean_dec_ref(v_h_4068_);
lean_dec(v_a_3946_);
lean_dec_ref(v_c_3823_);
v_a_4216_ = lean_ctor_get(v___x_4080_, 0);
v_isSharedCheck_4223_ = !lean_is_exclusive(v___x_4080_);
if (v_isSharedCheck_4223_ == 0)
{
v___x_4218_ = v___x_4080_;
v_isShared_4219_ = v_isSharedCheck_4223_;
goto v_resetjp_4217_;
}
else
{
lean_inc(v_a_4216_);
lean_dec(v___x_4080_);
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
v___jp_4224_:
{
lean_object* v_h_x3f_4236_; 
v_h_x3f_4236_ = lean_ctor_get(v_c_3823_, 4);
if (lean_obj_tag(v_h_x3f_4236_) == 1)
{
lean_object* v_e_4237_; lean_object* v_val_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; 
v_e_4237_ = lean_ctor_get(v_c_3823_, 3);
v_val_4238_ = lean_ctor_get(v_h_x3f_4236_, 0);
v___x_4239_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__29, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__29_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__29);
lean_inc_ref(v_e_3824_);
v___x_4240_ = l_Lean_Meta_mkOfEqFalseCore(v_e_3824_, v_he_3825_);
lean_inc(v_val_4238_);
lean_inc_ref(v_e_4237_);
v___x_4241_ = l_Lean_mkApp4(v___x_4239_, v_e_3824_, v_e_4237_, v_val_4238_, v___x_4240_);
v_h_4068_ = v___x_4241_;
v___y_4069_ = v___y_4225_;
v___y_4070_ = v___y_4226_;
v___y_4071_ = v___y_4227_;
v___y_4072_ = v___y_4228_;
v___y_4073_ = v___y_4229_;
v___y_4074_ = v___y_4230_;
v___y_4075_ = v___y_4231_;
v___y_4076_ = v___y_4232_;
v___y_4077_ = v___y_4233_;
v___y_4078_ = v___y_4234_;
v___y_4079_ = v___y_4235_;
goto v___jp_4067_;
}
else
{
lean_object* v___x_4242_; 
v___x_4242_ = l_Lean_Meta_mkOfEqFalseCore(v_e_3824_, v_he_3825_);
v_h_4068_ = v___x_4242_;
v___y_4069_ = v___y_4225_;
v___y_4070_ = v___y_4226_;
v___y_4071_ = v___y_4227_;
v___y_4072_ = v___y_4228_;
v___y_4073_ = v___y_4229_;
v___y_4074_ = v___y_4230_;
v___y_4075_ = v___y_4231_;
v___y_4076_ = v___y_4232_;
v___y_4077_ = v___y_4233_;
v___y_4078_ = v___y_4234_;
v___y_4079_ = v___y_4235_;
goto v___jp_4067_;
}
}
}
}
else
{
lean_object* v_a_4269_; lean_object* v___x_4271_; uint8_t v_isShared_4272_; uint8_t v_isSharedCheck_4276_; 
lean_dec_ref(v_he_3825_);
lean_dec_ref(v_e_3824_);
lean_dec_ref(v_c_3823_);
v_a_4269_ = lean_ctor_get(v___x_3945_, 0);
v_isSharedCheck_4276_ = !lean_is_exclusive(v___x_3945_);
if (v_isSharedCheck_4276_ == 0)
{
v___x_4271_ = v___x_3945_;
v_isShared_4272_ = v_isSharedCheck_4276_;
goto v_resetjp_4270_;
}
else
{
lean_inc(v_a_4269_);
lean_dec(v___x_3945_);
v___x_4271_ = lean_box(0);
v_isShared_4272_ = v_isSharedCheck_4276_;
goto v_resetjp_4270_;
}
v_resetjp_4270_:
{
lean_object* v___x_4274_; 
if (v_isShared_4272_ == 0)
{
v___x_4274_ = v___x_4271_;
goto v_reusejp_4273_;
}
else
{
lean_object* v_reuseFailAlloc_4275_; 
v_reuseFailAlloc_4275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4275_, 0, v_a_4269_);
v___x_4274_ = v_reuseFailAlloc_4275_;
goto v_reusejp_4273_;
}
v_reusejp_4273_:
{
return v___x_4274_;
}
}
}
v___jp_3838_:
{
lean_object* v___x_3855_; lean_object* v___x_3856_; 
v___x_3855_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3855_, 0, v_k_x27_3841_);
lean_ctor_set_uint8(v___x_3855_, sizeof(void*)*1, v_strict_3843_);
v___x_3856_ = l_Lean_Meta_Grind_Order_addEdge(v___y_3839_, v___y_3840_, v___x_3855_, v_h_3842_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_, v___y_3850_, v___y_3851_, v___y_3852_, v___y_3853_, v___y_3854_);
return v___x_3856_;
}
v___jp_3857_:
{
lean_object* v___x_3879_; uint8_t v___x_3880_; 
lean_inc_ref(v___y_3866_);
v___x_3879_ = l_Lean_mkApp6(v___y_3866_, v___y_3861_, v___y_3870_, v___y_3858_, v___y_3878_, v___y_3867_, v___y_3868_);
v___x_3880_ = 0;
v___y_3839_ = v___y_3873_;
v___y_3840_ = v___y_3874_;
v_k_x27_3841_ = v___y_3871_;
v_h_3842_ = v___x_3879_;
v_strict_3843_ = v___x_3880_;
v___y_3844_ = v___y_3876_;
v___y_3845_ = v___y_3863_;
v___y_3846_ = v___y_3872_;
v___y_3847_ = v___y_3877_;
v___y_3848_ = v___y_3865_;
v___y_3849_ = v___y_3862_;
v___y_3850_ = v___y_3859_;
v___y_3851_ = v___y_3860_;
v___y_3852_ = v___y_3869_;
v___y_3853_ = v___y_3864_;
v___y_3854_ = v___y_3875_;
goto v___jp_3838_;
}
v___jp_3881_:
{
lean_object* v___x_3900_; 
v___x_3900_ = l_Lean_Meta_Grind_Order_isInt(v___y_3896_, v___y_3887_, v___y_3893_, v___y_3897_, v___y_3889_, v___y_3885_, v___y_3884_, v___y_3886_, v___y_3892_, v___y_3888_, v___y_3898_);
if (lean_obj_tag(v___x_3900_) == 0)
{
lean_object* v_a_3901_; uint8_t v___x_3902_; 
v_a_3901_ = lean_ctor_get(v___x_3900_, 0);
lean_inc(v_a_3901_);
lean_dec_ref_known(v___x_3900_, 1);
v___x_3902_ = lean_unbox(v_a_3901_);
lean_dec(v_a_3901_);
if (v___x_3902_ == 0)
{
lean_dec_ref(v___y_3890_);
lean_dec_ref(v___y_3883_);
v___y_3839_ = v___y_3894_;
v___y_3840_ = v___y_3895_;
v_k_x27_3841_ = v___y_3882_;
v_h_3842_ = v___y_3891_;
v_strict_3843_ = v___y_3899_;
v___y_3844_ = v___y_3896_;
v___y_3845_ = v___y_3887_;
v___y_3846_ = v___y_3893_;
v___y_3847_ = v___y_3897_;
v___y_3848_ = v___y_3889_;
v___y_3849_ = v___y_3885_;
v___y_3850_ = v___y_3884_;
v___y_3851_ = v___y_3886_;
v___y_3852_ = v___y_3892_;
v___y_3853_ = v___y_3888_;
v___y_3854_ = v___y_3898_;
goto v___jp_3838_;
}
else
{
if (v___y_3899_ == 0)
{
lean_dec_ref(v___y_3890_);
lean_dec_ref(v___y_3883_);
v___y_3839_ = v___y_3894_;
v___y_3840_ = v___y_3895_;
v_k_x27_3841_ = v___y_3882_;
v_h_3842_ = v___y_3891_;
v_strict_3843_ = v___y_3899_;
v___y_3844_ = v___y_3896_;
v___y_3845_ = v___y_3887_;
v___y_3846_ = v___y_3893_;
v___y_3847_ = v___y_3897_;
v___y_3848_ = v___y_3889_;
v___y_3849_ = v___y_3885_;
v___y_3850_ = v___y_3884_;
v___y_3851_ = v___y_3886_;
v___y_3852_ = v___y_3892_;
v___y_3853_ = v___y_3888_;
v___y_3854_ = v___y_3898_;
goto v___jp_3838_;
}
else
{
lean_object* v___x_3903_; 
v___x_3903_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v___y_3894_, v___y_3896_, v___y_3887_, v___y_3888_);
if (lean_obj_tag(v___x_3903_) == 0)
{
lean_object* v_a_3904_; lean_object* v___x_3905_; 
v_a_3904_ = lean_ctor_get(v___x_3903_, 0);
lean_inc(v_a_3904_);
lean_dec_ref_known(v___x_3903_, 1);
v___x_3905_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v___y_3895_, v___y_3896_, v___y_3887_, v___y_3888_);
if (lean_obj_tag(v___x_3905_) == 0)
{
lean_object* v_a_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; uint8_t v___x_3911_; 
v_a_3906_ = lean_ctor_get(v___x_3905_, 0);
lean_inc(v_a_3906_);
lean_dec_ref_known(v___x_3905_, 1);
v___x_3907_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__2, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__2);
v___x_3908_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__3);
v___x_3909_ = lean_int_sub(v___y_3882_, v___x_3908_);
lean_dec(v___y_3882_);
v___x_3910_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4);
v___x_3911_ = lean_int_dec_le(v___x_3910_, v___x_3909_);
if (v___x_3911_ == 0)
{
lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; 
v___x_3912_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10);
v___x_3913_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13);
v___x_3914_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16);
v___x_3915_ = lean_int_neg(v___x_3909_);
v___x_3916_ = l_Int_toNat(v___x_3915_);
lean_dec(v___x_3915_);
v___x_3917_ = l_Lean_instToExprInt_mkNat(v___x_3916_);
v___x_3918_ = l_Lean_mkApp3(v___x_3912_, v___x_3913_, v___x_3914_, v___x_3917_);
v___y_3858_ = v___y_3883_;
v___y_3859_ = v___y_3884_;
v___y_3860_ = v___y_3886_;
v___y_3861_ = v_a_3904_;
v___y_3862_ = v___y_3885_;
v___y_3863_ = v___y_3887_;
v___y_3864_ = v___y_3888_;
v___y_3865_ = v___y_3889_;
v___y_3866_ = v___x_3907_;
v___y_3867_ = v___y_3890_;
v___y_3868_ = v___y_3891_;
v___y_3869_ = v___y_3892_;
v___y_3870_ = v_a_3906_;
v___y_3871_ = v___x_3909_;
v___y_3872_ = v___y_3893_;
v___y_3873_ = v___y_3894_;
v___y_3874_ = v___y_3895_;
v___y_3875_ = v___y_3898_;
v___y_3876_ = v___y_3896_;
v___y_3877_ = v___y_3897_;
v___y_3878_ = v___x_3918_;
goto v___jp_3857_;
}
else
{
lean_object* v___x_3919_; lean_object* v___x_3920_; 
v___x_3919_ = l_Int_toNat(v___x_3909_);
v___x_3920_ = l_Lean_instToExprInt_mkNat(v___x_3919_);
v___y_3858_ = v___y_3883_;
v___y_3859_ = v___y_3884_;
v___y_3860_ = v___y_3886_;
v___y_3861_ = v_a_3904_;
v___y_3862_ = v___y_3885_;
v___y_3863_ = v___y_3887_;
v___y_3864_ = v___y_3888_;
v___y_3865_ = v___y_3889_;
v___y_3866_ = v___x_3907_;
v___y_3867_ = v___y_3890_;
v___y_3868_ = v___y_3891_;
v___y_3869_ = v___y_3892_;
v___y_3870_ = v_a_3906_;
v___y_3871_ = v___x_3909_;
v___y_3872_ = v___y_3893_;
v___y_3873_ = v___y_3894_;
v___y_3874_ = v___y_3895_;
v___y_3875_ = v___y_3898_;
v___y_3876_ = v___y_3896_;
v___y_3877_ = v___y_3897_;
v___y_3878_ = v___x_3920_;
goto v___jp_3857_;
}
}
else
{
lean_object* v_a_3921_; lean_object* v___x_3923_; uint8_t v_isShared_3924_; uint8_t v_isSharedCheck_3928_; 
lean_dec(v_a_3904_);
lean_dec(v___y_3895_);
lean_dec(v___y_3894_);
lean_dec_ref(v___y_3891_);
lean_dec_ref(v___y_3890_);
lean_dec_ref(v___y_3883_);
lean_dec(v___y_3882_);
v_a_3921_ = lean_ctor_get(v___x_3905_, 0);
v_isSharedCheck_3928_ = !lean_is_exclusive(v___x_3905_);
if (v_isSharedCheck_3928_ == 0)
{
v___x_3923_ = v___x_3905_;
v_isShared_3924_ = v_isSharedCheck_3928_;
goto v_resetjp_3922_;
}
else
{
lean_inc(v_a_3921_);
lean_dec(v___x_3905_);
v___x_3923_ = lean_box(0);
v_isShared_3924_ = v_isSharedCheck_3928_;
goto v_resetjp_3922_;
}
v_resetjp_3922_:
{
lean_object* v___x_3926_; 
if (v_isShared_3924_ == 0)
{
v___x_3926_ = v___x_3923_;
goto v_reusejp_3925_;
}
else
{
lean_object* v_reuseFailAlloc_3927_; 
v_reuseFailAlloc_3927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3927_, 0, v_a_3921_);
v___x_3926_ = v_reuseFailAlloc_3927_;
goto v_reusejp_3925_;
}
v_reusejp_3925_:
{
return v___x_3926_;
}
}
}
}
else
{
lean_object* v_a_3929_; lean_object* v___x_3931_; uint8_t v_isShared_3932_; uint8_t v_isSharedCheck_3936_; 
lean_dec(v___y_3895_);
lean_dec(v___y_3894_);
lean_dec_ref(v___y_3891_);
lean_dec_ref(v___y_3890_);
lean_dec_ref(v___y_3883_);
lean_dec(v___y_3882_);
v_a_3929_ = lean_ctor_get(v___x_3903_, 0);
v_isSharedCheck_3936_ = !lean_is_exclusive(v___x_3903_);
if (v_isSharedCheck_3936_ == 0)
{
v___x_3931_ = v___x_3903_;
v_isShared_3932_ = v_isSharedCheck_3936_;
goto v_resetjp_3930_;
}
else
{
lean_inc(v_a_3929_);
lean_dec(v___x_3903_);
v___x_3931_ = lean_box(0);
v_isShared_3932_ = v_isSharedCheck_3936_;
goto v_resetjp_3930_;
}
v_resetjp_3930_:
{
lean_object* v___x_3934_; 
if (v_isShared_3932_ == 0)
{
v___x_3934_ = v___x_3931_;
goto v_reusejp_3933_;
}
else
{
lean_object* v_reuseFailAlloc_3935_; 
v_reuseFailAlloc_3935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3935_, 0, v_a_3929_);
v___x_3934_ = v_reuseFailAlloc_3935_;
goto v_reusejp_3933_;
}
v_reusejp_3933_:
{
return v___x_3934_;
}
}
}
}
}
}
else
{
lean_object* v_a_3937_; lean_object* v___x_3939_; uint8_t v_isShared_3940_; uint8_t v_isSharedCheck_3944_; 
lean_dec(v___y_3895_);
lean_dec(v___y_3894_);
lean_dec_ref(v___y_3891_);
lean_dec_ref(v___y_3890_);
lean_dec_ref(v___y_3883_);
lean_dec(v___y_3882_);
v_a_3937_ = lean_ctor_get(v___x_3900_, 0);
v_isSharedCheck_3944_ = !lean_is_exclusive(v___x_3900_);
if (v_isSharedCheck_3944_ == 0)
{
v___x_3939_ = v___x_3900_;
v_isShared_3940_ = v_isSharedCheck_3944_;
goto v_resetjp_3938_;
}
else
{
lean_inc(v_a_3937_);
lean_dec(v___x_3900_);
v___x_3939_ = lean_box(0);
v_isShared_3940_ = v_isSharedCheck_3944_;
goto v_resetjp_3938_;
}
v_resetjp_3938_:
{
lean_object* v___x_3942_; 
if (v_isShared_3940_ == 0)
{
v___x_3942_ = v___x_3939_;
goto v_reusejp_3941_;
}
else
{
lean_object* v_reuseFailAlloc_3943_; 
v_reuseFailAlloc_3943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3943_, 0, v_a_3937_);
v___x_3942_ = v_reuseFailAlloc_3943_;
goto v_reusejp_3941_;
}
v_reusejp_3941_:
{
return v___x_3942_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___boxed(lean_object* v_c_4277_, lean_object* v_e_4278_, lean_object* v_he_4279_, lean_object* v_a_4280_, lean_object* v_a_4281_, lean_object* v_a_4282_, lean_object* v_a_4283_, lean_object* v_a_4284_, lean_object* v_a_4285_, lean_object* v_a_4286_, lean_object* v_a_4287_, lean_object* v_a_4288_, lean_object* v_a_4289_, lean_object* v_a_4290_, lean_object* v_a_4291_){
_start:
{
lean_object* v_res_4292_; 
v_res_4292_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse(v_c_4277_, v_e_4278_, v_he_4279_, v_a_4280_, v_a_4281_, v_a_4282_, v_a_4283_, v_a_4284_, v_a_4285_, v_a_4286_, v_a_4287_, v_a_4288_, v_a_4289_, v_a_4290_);
lean_dec(v_a_4290_);
lean_dec_ref(v_a_4289_);
lean_dec(v_a_4288_);
lean_dec_ref(v_a_4287_);
lean_dec(v_a_4286_);
lean_dec_ref(v_a_4285_);
lean_dec(v_a_4284_);
lean_dec_ref(v_a_4283_);
lean_dec(v_a_4282_);
lean_dec(v_a_4281_);
lean_dec(v_a_4280_);
return v_res_4292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___redArg(lean_object* v_e_4293_, lean_object* v_a_4294_, lean_object* v_a_4295_){
_start:
{
lean_object* v___x_4297_; 
v___x_4297_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_4294_, v_a_4295_);
if (lean_obj_tag(v___x_4297_) == 0)
{
lean_object* v_a_4298_; lean_object* v___x_4300_; uint8_t v_isShared_4301_; uint8_t v_isSharedCheck_4307_; 
v_a_4298_ = lean_ctor_get(v___x_4297_, 0);
v_isSharedCheck_4307_ = !lean_is_exclusive(v___x_4297_);
if (v_isSharedCheck_4307_ == 0)
{
v___x_4300_ = v___x_4297_;
v_isShared_4301_ = v_isSharedCheck_4307_;
goto v_resetjp_4299_;
}
else
{
lean_inc(v_a_4298_);
lean_dec(v___x_4297_);
v___x_4300_ = lean_box(0);
v_isShared_4301_ = v_isSharedCheck_4307_;
goto v_resetjp_4299_;
}
v_resetjp_4299_:
{
lean_object* v_exprToStructId_4302_; lean_object* v___x_4303_; lean_object* v___x_4305_; 
v_exprToStructId_4302_ = lean_ctor_get(v_a_4298_, 2);
lean_inc_ref(v_exprToStructId_4302_);
lean_dec(v_a_4298_);
v___x_4303_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_exprToStructId_4302_, v_e_4293_);
lean_dec_ref(v_exprToStructId_4302_);
if (v_isShared_4301_ == 0)
{
lean_ctor_set(v___x_4300_, 0, v___x_4303_);
v___x_4305_ = v___x_4300_;
goto v_reusejp_4304_;
}
else
{
lean_object* v_reuseFailAlloc_4306_; 
v_reuseFailAlloc_4306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4306_, 0, v___x_4303_);
v___x_4305_ = v_reuseFailAlloc_4306_;
goto v_reusejp_4304_;
}
v_reusejp_4304_:
{
return v___x_4305_;
}
}
}
else
{
lean_object* v_a_4308_; lean_object* v___x_4310_; uint8_t v_isShared_4311_; uint8_t v_isSharedCheck_4315_; 
v_a_4308_ = lean_ctor_get(v___x_4297_, 0);
v_isSharedCheck_4315_ = !lean_is_exclusive(v___x_4297_);
if (v_isSharedCheck_4315_ == 0)
{
v___x_4310_ = v___x_4297_;
v_isShared_4311_ = v_isSharedCheck_4315_;
goto v_resetjp_4309_;
}
else
{
lean_inc(v_a_4308_);
lean_dec(v___x_4297_);
v___x_4310_ = lean_box(0);
v_isShared_4311_ = v_isSharedCheck_4315_;
goto v_resetjp_4309_;
}
v_resetjp_4309_:
{
lean_object* v___x_4313_; 
if (v_isShared_4311_ == 0)
{
v___x_4313_ = v___x_4310_;
goto v_reusejp_4312_;
}
else
{
lean_object* v_reuseFailAlloc_4314_; 
v_reuseFailAlloc_4314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4314_, 0, v_a_4308_);
v___x_4313_ = v_reuseFailAlloc_4314_;
goto v_reusejp_4312_;
}
v_reusejp_4312_:
{
return v___x_4313_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___redArg___boxed(lean_object* v_e_4316_, lean_object* v_a_4317_, lean_object* v_a_4318_, lean_object* v_a_4319_){
_start:
{
lean_object* v_res_4320_; 
v_res_4320_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___redArg(v_e_4316_, v_a_4317_, v_a_4318_);
lean_dec_ref(v_a_4318_);
lean_dec(v_a_4317_);
lean_dec_ref(v_e_4316_);
return v_res_4320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f(lean_object* v_e_4321_, lean_object* v_a_4322_, lean_object* v_a_4323_, lean_object* v_a_4324_, lean_object* v_a_4325_, lean_object* v_a_4326_, lean_object* v_a_4327_, lean_object* v_a_4328_, lean_object* v_a_4329_, lean_object* v_a_4330_, lean_object* v_a_4331_){
_start:
{
lean_object* v___x_4333_; 
v___x_4333_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___redArg(v_e_4321_, v_a_4322_, v_a_4330_);
return v___x_4333_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___boxed(lean_object* v_e_4334_, lean_object* v_a_4335_, lean_object* v_a_4336_, lean_object* v_a_4337_, lean_object* v_a_4338_, lean_object* v_a_4339_, lean_object* v_a_4340_, lean_object* v_a_4341_, lean_object* v_a_4342_, lean_object* v_a_4343_, lean_object* v_a_4344_, lean_object* v_a_4345_){
_start:
{
lean_object* v_res_4346_; 
v_res_4346_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f(v_e_4334_, v_a_4335_, v_a_4336_, v_a_4337_, v_a_4338_, v_a_4339_, v_a_4340_, v_a_4341_, v_a_4342_, v_a_4343_, v_a_4344_);
lean_dec(v_a_4344_);
lean_dec_ref(v_a_4343_);
lean_dec(v_a_4342_);
lean_dec_ref(v_a_4341_);
lean_dec(v_a_4340_);
lean_dec_ref(v_a_4339_);
lean_dec(v_a_4338_);
lean_dec_ref(v_a_4337_);
lean_dec(v_a_4336_);
lean_dec(v_a_4335_);
lean_dec_ref(v_e_4334_);
return v_res_4346_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__2(void){
_start:
{
lean_object* v___x_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; 
v___x_4353_ = lean_box(0);
v___x_4354_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__1));
v___x_4355_ = l_Lean_mkConst(v___x_4354_, v___x_4353_);
return v___x_4355_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__5(void){
_start:
{
lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; 
v___x_4362_ = lean_box(0);
v___x_4363_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__4));
v___x_4364_ = l_Lean_mkConst(v___x_4363_, v___x_4362_);
return v___x_4364_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go(lean_object* v_e_4365_, lean_object* v_e_x27_4366_, lean_object* v_he_x3f_4367_, lean_object* v_a_4368_, lean_object* v_a_4369_, lean_object* v_a_4370_, lean_object* v_a_4371_, lean_object* v_a_4372_, lean_object* v_a_4373_, lean_object* v_a_4374_, lean_object* v_a_4375_, lean_object* v_a_4376_, lean_object* v_a_4377_){
_start:
{
lean_object* v___x_4379_; 
v___x_4379_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___redArg(v_e_x27_4366_, v_a_4368_, v_a_4376_);
if (lean_obj_tag(v___x_4379_) == 0)
{
lean_object* v_a_4380_; lean_object* v___x_4382_; uint8_t v_isShared_4383_; uint8_t v_isSharedCheck_4470_; 
v_a_4380_ = lean_ctor_get(v___x_4379_, 0);
v_isSharedCheck_4470_ = !lean_is_exclusive(v___x_4379_);
if (v_isSharedCheck_4470_ == 0)
{
v___x_4382_ = v___x_4379_;
v_isShared_4383_ = v_isSharedCheck_4470_;
goto v_resetjp_4381_;
}
else
{
lean_inc(v_a_4380_);
lean_dec(v___x_4379_);
v___x_4382_ = lean_box(0);
v_isShared_4383_ = v_isSharedCheck_4470_;
goto v_resetjp_4381_;
}
v_resetjp_4381_:
{
if (lean_obj_tag(v_a_4380_) == 1)
{
lean_object* v_val_4384_; lean_object* v___x_4385_; 
lean_del_object(v___x_4382_);
v_val_4384_ = lean_ctor_get(v_a_4380_, 0);
lean_inc(v_val_4384_);
lean_dec_ref_known(v_a_4380_, 1);
v___x_4385_ = l_Lean_Meta_Grind_Order_getCnstr_x3f___redArg(v_e_x27_4366_, v_val_4384_, v_a_4368_, v_a_4376_);
if (lean_obj_tag(v___x_4385_) == 0)
{
lean_object* v_a_4386_; lean_object* v___x_4388_; uint8_t v_isShared_4389_; uint8_t v_isSharedCheck_4457_; 
v_a_4386_ = lean_ctor_get(v___x_4385_, 0);
v_isSharedCheck_4457_ = !lean_is_exclusive(v___x_4385_);
if (v_isSharedCheck_4457_ == 0)
{
v___x_4388_ = v___x_4385_;
v_isShared_4389_ = v_isSharedCheck_4457_;
goto v_resetjp_4387_;
}
else
{
lean_inc(v_a_4386_);
lean_dec(v___x_4385_);
v___x_4388_ = lean_box(0);
v_isShared_4389_ = v_isSharedCheck_4457_;
goto v_resetjp_4387_;
}
v_resetjp_4387_:
{
if (lean_obj_tag(v_a_4386_) == 1)
{
lean_object* v_val_4390_; lean_object* v___x_4391_; 
lean_del_object(v___x_4388_);
v_val_4390_ = lean_ctor_get(v_a_4386_, 0);
lean_inc(v_val_4390_);
lean_dec_ref_known(v_a_4386_, 1);
lean_inc_ref(v_e_4365_);
v___x_4391_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_4365_, v_a_4368_, v_a_4372_, v_a_4374_, v_a_4375_, v_a_4376_, v_a_4377_);
if (lean_obj_tag(v___x_4391_) == 0)
{
lean_object* v_a_4392_; uint8_t v___x_4393_; 
v_a_4392_ = lean_ctor_get(v___x_4391_, 0);
lean_inc(v_a_4392_);
lean_dec_ref_known(v___x_4391_, 1);
v___x_4393_ = lean_unbox(v_a_4392_);
lean_dec(v_a_4392_);
if (v___x_4393_ == 0)
{
lean_object* v___x_4394_; 
lean_inc_ref(v_e_4365_);
v___x_4394_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_4365_, v_a_4368_, v_a_4372_, v_a_4374_, v_a_4375_, v_a_4376_, v_a_4377_);
if (lean_obj_tag(v___x_4394_) == 0)
{
lean_object* v_a_4395_; lean_object* v___x_4397_; uint8_t v_isShared_4398_; uint8_t v_isSharedCheck_4420_; 
v_a_4395_ = lean_ctor_get(v___x_4394_, 0);
v_isSharedCheck_4420_ = !lean_is_exclusive(v___x_4394_);
if (v_isSharedCheck_4420_ == 0)
{
v___x_4397_ = v___x_4394_;
v_isShared_4398_ = v_isSharedCheck_4420_;
goto v_resetjp_4396_;
}
else
{
lean_inc(v_a_4395_);
lean_dec(v___x_4394_);
v___x_4397_ = lean_box(0);
v_isShared_4398_ = v_isSharedCheck_4420_;
goto v_resetjp_4396_;
}
v_resetjp_4396_:
{
uint8_t v___x_4399_; 
v___x_4399_ = lean_unbox(v_a_4395_);
lean_dec(v_a_4395_);
if (v___x_4399_ == 0)
{
lean_object* v___x_4400_; lean_object* v___x_4402_; 
lean_dec(v_val_4390_);
lean_dec(v_val_4384_);
lean_dec(v_he_x3f_4367_);
lean_dec_ref(v_e_x27_4366_);
lean_dec_ref(v_e_4365_);
v___x_4400_ = lean_box(0);
if (v_isShared_4398_ == 0)
{
lean_ctor_set(v___x_4397_, 0, v___x_4400_);
v___x_4402_ = v___x_4397_;
goto v_reusejp_4401_;
}
else
{
lean_object* v_reuseFailAlloc_4403_; 
v_reuseFailAlloc_4403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4403_, 0, v___x_4400_);
v___x_4402_ = v_reuseFailAlloc_4403_;
goto v_reusejp_4401_;
}
v_reusejp_4401_:
{
return v___x_4402_;
}
}
else
{
lean_object* v___x_4404_; 
lean_del_object(v___x_4397_);
lean_inc_ref(v_e_4365_);
v___x_4404_ = l_Lean_Meta_Grind_mkEqFalseProof(v_e_4365_, v_a_4368_, v_a_4369_, v_a_4370_, v_a_4371_, v_a_4372_, v_a_4373_, v_a_4374_, v_a_4375_, v_a_4376_, v_a_4377_);
if (lean_obj_tag(v___x_4404_) == 0)
{
if (lean_obj_tag(v_he_x3f_4367_) == 1)
{
lean_object* v_a_4405_; lean_object* v_val_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; 
v_a_4405_ = lean_ctor_get(v___x_4404_, 0);
lean_inc(v_a_4405_);
lean_dec_ref_known(v___x_4404_, 1);
v_val_4406_ = lean_ctor_get(v_he_x3f_4367_, 0);
lean_inc(v_val_4406_);
lean_dec_ref_known(v_he_x3f_4367_, 1);
v___x_4407_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__2, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__2);
lean_inc_ref(v_e_x27_4366_);
v___x_4408_ = l_Lean_mkApp4(v___x_4407_, v_e_4365_, v_e_x27_4366_, v_val_4406_, v_a_4405_);
v___x_4409_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse(v_val_4390_, v_e_x27_4366_, v___x_4408_, v_val_4384_, v_a_4368_, v_a_4369_, v_a_4370_, v_a_4371_, v_a_4372_, v_a_4373_, v_a_4374_, v_a_4375_, v_a_4376_, v_a_4377_);
lean_dec(v_val_4384_);
return v___x_4409_;
}
else
{
lean_object* v_a_4410_; lean_object* v___x_4411_; 
lean_dec(v_he_x3f_4367_);
lean_dec_ref(v_e_4365_);
v_a_4410_ = lean_ctor_get(v___x_4404_, 0);
lean_inc(v_a_4410_);
lean_dec_ref_known(v___x_4404_, 1);
v___x_4411_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse(v_val_4390_, v_e_x27_4366_, v_a_4410_, v_val_4384_, v_a_4368_, v_a_4369_, v_a_4370_, v_a_4371_, v_a_4372_, v_a_4373_, v_a_4374_, v_a_4375_, v_a_4376_, v_a_4377_);
lean_dec(v_val_4384_);
return v___x_4411_;
}
}
else
{
lean_object* v_a_4412_; lean_object* v___x_4414_; uint8_t v_isShared_4415_; uint8_t v_isSharedCheck_4419_; 
lean_dec(v_val_4390_);
lean_dec(v_val_4384_);
lean_dec(v_he_x3f_4367_);
lean_dec_ref(v_e_x27_4366_);
lean_dec_ref(v_e_4365_);
v_a_4412_ = lean_ctor_get(v___x_4404_, 0);
v_isSharedCheck_4419_ = !lean_is_exclusive(v___x_4404_);
if (v_isSharedCheck_4419_ == 0)
{
v___x_4414_ = v___x_4404_;
v_isShared_4415_ = v_isSharedCheck_4419_;
goto v_resetjp_4413_;
}
else
{
lean_inc(v_a_4412_);
lean_dec(v___x_4404_);
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
}
}
}
else
{
lean_object* v_a_4421_; lean_object* v___x_4423_; uint8_t v_isShared_4424_; uint8_t v_isSharedCheck_4428_; 
lean_dec(v_val_4390_);
lean_dec(v_val_4384_);
lean_dec(v_he_x3f_4367_);
lean_dec_ref(v_e_x27_4366_);
lean_dec_ref(v_e_4365_);
v_a_4421_ = lean_ctor_get(v___x_4394_, 0);
v_isSharedCheck_4428_ = !lean_is_exclusive(v___x_4394_);
if (v_isSharedCheck_4428_ == 0)
{
v___x_4423_ = v___x_4394_;
v_isShared_4424_ = v_isSharedCheck_4428_;
goto v_resetjp_4422_;
}
else
{
lean_inc(v_a_4421_);
lean_dec(v___x_4394_);
v___x_4423_ = lean_box(0);
v_isShared_4424_ = v_isSharedCheck_4428_;
goto v_resetjp_4422_;
}
v_resetjp_4422_:
{
lean_object* v___x_4426_; 
if (v_isShared_4424_ == 0)
{
v___x_4426_ = v___x_4423_;
goto v_reusejp_4425_;
}
else
{
lean_object* v_reuseFailAlloc_4427_; 
v_reuseFailAlloc_4427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4427_, 0, v_a_4421_);
v___x_4426_ = v_reuseFailAlloc_4427_;
goto v_reusejp_4425_;
}
v_reusejp_4425_:
{
return v___x_4426_;
}
}
}
}
else
{
lean_object* v___x_4429_; 
lean_inc_ref(v_e_4365_);
v___x_4429_ = l_Lean_Meta_Grind_mkEqTrueProof(v_e_4365_, v_a_4368_, v_a_4369_, v_a_4370_, v_a_4371_, v_a_4372_, v_a_4373_, v_a_4374_, v_a_4375_, v_a_4376_, v_a_4377_);
if (lean_obj_tag(v___x_4429_) == 0)
{
if (lean_obj_tag(v_he_x3f_4367_) == 1)
{
lean_object* v_a_4430_; lean_object* v_val_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; lean_object* v___x_4434_; 
v_a_4430_ = lean_ctor_get(v___x_4429_, 0);
lean_inc(v_a_4430_);
lean_dec_ref_known(v___x_4429_, 1);
v_val_4431_ = lean_ctor_get(v_he_x3f_4367_, 0);
lean_inc(v_val_4431_);
lean_dec_ref_known(v_he_x3f_4367_, 1);
v___x_4432_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__5);
lean_inc_ref(v_e_x27_4366_);
v___x_4433_ = l_Lean_mkApp4(v___x_4432_, v_e_4365_, v_e_x27_4366_, v_val_4431_, v_a_4430_);
v___x_4434_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue(v_val_4390_, v_e_x27_4366_, v___x_4433_, v_val_4384_, v_a_4368_, v_a_4369_, v_a_4370_, v_a_4371_, v_a_4372_, v_a_4373_, v_a_4374_, v_a_4375_, v_a_4376_, v_a_4377_);
lean_dec(v_val_4384_);
return v___x_4434_;
}
else
{
lean_object* v_a_4435_; lean_object* v___x_4436_; 
lean_dec(v_he_x3f_4367_);
lean_dec_ref(v_e_4365_);
v_a_4435_ = lean_ctor_get(v___x_4429_, 0);
lean_inc(v_a_4435_);
lean_dec_ref_known(v___x_4429_, 1);
v___x_4436_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue(v_val_4390_, v_e_x27_4366_, v_a_4435_, v_val_4384_, v_a_4368_, v_a_4369_, v_a_4370_, v_a_4371_, v_a_4372_, v_a_4373_, v_a_4374_, v_a_4375_, v_a_4376_, v_a_4377_);
lean_dec(v_val_4384_);
return v___x_4436_;
}
}
else
{
lean_object* v_a_4437_; lean_object* v___x_4439_; uint8_t v_isShared_4440_; uint8_t v_isSharedCheck_4444_; 
lean_dec(v_val_4390_);
lean_dec(v_val_4384_);
lean_dec(v_he_x3f_4367_);
lean_dec_ref(v_e_x27_4366_);
lean_dec_ref(v_e_4365_);
v_a_4437_ = lean_ctor_get(v___x_4429_, 0);
v_isSharedCheck_4444_ = !lean_is_exclusive(v___x_4429_);
if (v_isSharedCheck_4444_ == 0)
{
v___x_4439_ = v___x_4429_;
v_isShared_4440_ = v_isSharedCheck_4444_;
goto v_resetjp_4438_;
}
else
{
lean_inc(v_a_4437_);
lean_dec(v___x_4429_);
v___x_4439_ = lean_box(0);
v_isShared_4440_ = v_isSharedCheck_4444_;
goto v_resetjp_4438_;
}
v_resetjp_4438_:
{
lean_object* v___x_4442_; 
if (v_isShared_4440_ == 0)
{
v___x_4442_ = v___x_4439_;
goto v_reusejp_4441_;
}
else
{
lean_object* v_reuseFailAlloc_4443_; 
v_reuseFailAlloc_4443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4443_, 0, v_a_4437_);
v___x_4442_ = v_reuseFailAlloc_4443_;
goto v_reusejp_4441_;
}
v_reusejp_4441_:
{
return v___x_4442_;
}
}
}
}
}
else
{
lean_object* v_a_4445_; lean_object* v___x_4447_; uint8_t v_isShared_4448_; uint8_t v_isSharedCheck_4452_; 
lean_dec(v_val_4390_);
lean_dec(v_val_4384_);
lean_dec(v_he_x3f_4367_);
lean_dec_ref(v_e_x27_4366_);
lean_dec_ref(v_e_4365_);
v_a_4445_ = lean_ctor_get(v___x_4391_, 0);
v_isSharedCheck_4452_ = !lean_is_exclusive(v___x_4391_);
if (v_isSharedCheck_4452_ == 0)
{
v___x_4447_ = v___x_4391_;
v_isShared_4448_ = v_isSharedCheck_4452_;
goto v_resetjp_4446_;
}
else
{
lean_inc(v_a_4445_);
lean_dec(v___x_4391_);
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
lean_object* v___x_4453_; lean_object* v___x_4455_; 
lean_dec(v_a_4386_);
lean_dec(v_val_4384_);
lean_dec(v_he_x3f_4367_);
lean_dec_ref(v_e_x27_4366_);
lean_dec_ref(v_e_4365_);
v___x_4453_ = lean_box(0);
if (v_isShared_4389_ == 0)
{
lean_ctor_set(v___x_4388_, 0, v___x_4453_);
v___x_4455_ = v___x_4388_;
goto v_reusejp_4454_;
}
else
{
lean_object* v_reuseFailAlloc_4456_; 
v_reuseFailAlloc_4456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4456_, 0, v___x_4453_);
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
lean_object* v_a_4458_; lean_object* v___x_4460_; uint8_t v_isShared_4461_; uint8_t v_isSharedCheck_4465_; 
lean_dec(v_val_4384_);
lean_dec(v_he_x3f_4367_);
lean_dec_ref(v_e_x27_4366_);
lean_dec_ref(v_e_4365_);
v_a_4458_ = lean_ctor_get(v___x_4385_, 0);
v_isSharedCheck_4465_ = !lean_is_exclusive(v___x_4385_);
if (v_isSharedCheck_4465_ == 0)
{
v___x_4460_ = v___x_4385_;
v_isShared_4461_ = v_isSharedCheck_4465_;
goto v_resetjp_4459_;
}
else
{
lean_inc(v_a_4458_);
lean_dec(v___x_4385_);
v___x_4460_ = lean_box(0);
v_isShared_4461_ = v_isSharedCheck_4465_;
goto v_resetjp_4459_;
}
v_resetjp_4459_:
{
lean_object* v___x_4463_; 
if (v_isShared_4461_ == 0)
{
v___x_4463_ = v___x_4460_;
goto v_reusejp_4462_;
}
else
{
lean_object* v_reuseFailAlloc_4464_; 
v_reuseFailAlloc_4464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4464_, 0, v_a_4458_);
v___x_4463_ = v_reuseFailAlloc_4464_;
goto v_reusejp_4462_;
}
v_reusejp_4462_:
{
return v___x_4463_;
}
}
}
}
else
{
lean_object* v___x_4466_; lean_object* v___x_4468_; 
lean_dec(v_a_4380_);
lean_dec(v_he_x3f_4367_);
lean_dec_ref(v_e_x27_4366_);
lean_dec_ref(v_e_4365_);
v___x_4466_ = lean_box(0);
if (v_isShared_4383_ == 0)
{
lean_ctor_set(v___x_4382_, 0, v___x_4466_);
v___x_4468_ = v___x_4382_;
goto v_reusejp_4467_;
}
else
{
lean_object* v_reuseFailAlloc_4469_; 
v_reuseFailAlloc_4469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4469_, 0, v___x_4466_);
v___x_4468_ = v_reuseFailAlloc_4469_;
goto v_reusejp_4467_;
}
v_reusejp_4467_:
{
return v___x_4468_;
}
}
}
}
else
{
lean_object* v_a_4471_; lean_object* v___x_4473_; uint8_t v_isShared_4474_; uint8_t v_isSharedCheck_4478_; 
lean_dec(v_he_x3f_4367_);
lean_dec_ref(v_e_x27_4366_);
lean_dec_ref(v_e_4365_);
v_a_4471_ = lean_ctor_get(v___x_4379_, 0);
v_isSharedCheck_4478_ = !lean_is_exclusive(v___x_4379_);
if (v_isSharedCheck_4478_ == 0)
{
v___x_4473_ = v___x_4379_;
v_isShared_4474_ = v_isSharedCheck_4478_;
goto v_resetjp_4472_;
}
else
{
lean_inc(v_a_4471_);
lean_dec(v___x_4379_);
v___x_4473_ = lean_box(0);
v_isShared_4474_ = v_isSharedCheck_4478_;
goto v_resetjp_4472_;
}
v_resetjp_4472_:
{
lean_object* v___x_4476_; 
if (v_isShared_4474_ == 0)
{
v___x_4476_ = v___x_4473_;
goto v_reusejp_4475_;
}
else
{
lean_object* v_reuseFailAlloc_4477_; 
v_reuseFailAlloc_4477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4477_, 0, v_a_4471_);
v___x_4476_ = v_reuseFailAlloc_4477_;
goto v_reusejp_4475_;
}
v_reusejp_4475_:
{
return v___x_4476_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___boxed(lean_object* v_e_4479_, lean_object* v_e_x27_4480_, lean_object* v_he_x3f_4481_, lean_object* v_a_4482_, lean_object* v_a_4483_, lean_object* v_a_4484_, lean_object* v_a_4485_, lean_object* v_a_4486_, lean_object* v_a_4487_, lean_object* v_a_4488_, lean_object* v_a_4489_, lean_object* v_a_4490_, lean_object* v_a_4491_, lean_object* v_a_4492_){
_start:
{
lean_object* v_res_4493_; 
v_res_4493_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go(v_e_4479_, v_e_x27_4480_, v_he_x3f_4481_, v_a_4482_, v_a_4483_, v_a_4484_, v_a_4485_, v_a_4486_, v_a_4487_, v_a_4488_, v_a_4489_, v_a_4490_, v_a_4491_);
lean_dec(v_a_4491_);
lean_dec_ref(v_a_4490_);
lean_dec(v_a_4489_);
lean_dec_ref(v_a_4488_);
lean_dec(v_a_4487_);
lean_dec_ref(v_a_4486_);
lean_dec(v_a_4485_);
lean_dec_ref(v_a_4484_);
lean_dec(v_a_4483_);
lean_dec(v_a_4482_);
return v_res_4493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq(lean_object* v_e_4494_, lean_object* v_a_4495_, lean_object* v_a_4496_, lean_object* v_a_4497_, lean_object* v_a_4498_, lean_object* v_a_4499_, lean_object* v_a_4500_, lean_object* v_a_4501_, lean_object* v_a_4502_, lean_object* v_a_4503_, lean_object* v_a_4504_){
_start:
{
lean_object* v___x_4506_; 
v___x_4506_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_4495_, v_a_4503_);
if (lean_obj_tag(v___x_4506_) == 0)
{
lean_object* v_a_4507_; lean_object* v_termMap_4508_; lean_object* v___x_4509_; 
v_a_4507_ = lean_ctor_get(v___x_4506_, 0);
lean_inc(v_a_4507_);
lean_dec_ref_known(v___x_4506_, 1);
v_termMap_4508_ = lean_ctor_get(v_a_4507_, 3);
lean_inc_ref(v_termMap_4508_);
lean_dec(v_a_4507_);
v___x_4509_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMap_4508_, v_e_4494_);
lean_dec_ref(v_termMap_4508_);
if (lean_obj_tag(v___x_4509_) == 1)
{
lean_object* v_val_4510_; lean_object* v___x_4512_; uint8_t v_isShared_4513_; uint8_t v_isSharedCheck_4520_; 
v_val_4510_ = lean_ctor_get(v___x_4509_, 0);
v_isSharedCheck_4520_ = !lean_is_exclusive(v___x_4509_);
if (v_isSharedCheck_4520_ == 0)
{
v___x_4512_ = v___x_4509_;
v_isShared_4513_ = v_isSharedCheck_4520_;
goto v_resetjp_4511_;
}
else
{
lean_inc(v_val_4510_);
lean_dec(v___x_4509_);
v___x_4512_ = lean_box(0);
v_isShared_4513_ = v_isSharedCheck_4520_;
goto v_resetjp_4511_;
}
v_resetjp_4511_:
{
lean_object* v_e_4514_; lean_object* v_h_4515_; lean_object* v___x_4517_; 
v_e_4514_ = lean_ctor_get(v_val_4510_, 0);
lean_inc_ref(v_e_4514_);
v_h_4515_ = lean_ctor_get(v_val_4510_, 1);
lean_inc_ref(v_h_4515_);
lean_dec(v_val_4510_);
if (v_isShared_4513_ == 0)
{
lean_ctor_set(v___x_4512_, 0, v_h_4515_);
v___x_4517_ = v___x_4512_;
goto v_reusejp_4516_;
}
else
{
lean_object* v_reuseFailAlloc_4519_; 
v_reuseFailAlloc_4519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4519_, 0, v_h_4515_);
v___x_4517_ = v_reuseFailAlloc_4519_;
goto v_reusejp_4516_;
}
v_reusejp_4516_:
{
lean_object* v___x_4518_; 
v___x_4518_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go(v_e_4494_, v_e_4514_, v___x_4517_, v_a_4495_, v_a_4496_, v_a_4497_, v_a_4498_, v_a_4499_, v_a_4500_, v_a_4501_, v_a_4502_, v_a_4503_, v_a_4504_);
return v___x_4518_;
}
}
}
else
{
lean_object* v___x_4521_; lean_object* v___x_4522_; 
lean_dec(v___x_4509_);
v___x_4521_ = lean_box(0);
lean_inc_ref(v_e_4494_);
v___x_4522_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go(v_e_4494_, v_e_4494_, v___x_4521_, v_a_4495_, v_a_4496_, v_a_4497_, v_a_4498_, v_a_4499_, v_a_4500_, v_a_4501_, v_a_4502_, v_a_4503_, v_a_4504_);
return v___x_4522_;
}
}
else
{
lean_object* v_a_4523_; lean_object* v___x_4525_; uint8_t v_isShared_4526_; uint8_t v_isSharedCheck_4530_; 
lean_dec_ref(v_e_4494_);
v_a_4523_ = lean_ctor_get(v___x_4506_, 0);
v_isSharedCheck_4530_ = !lean_is_exclusive(v___x_4506_);
if (v_isSharedCheck_4530_ == 0)
{
v___x_4525_ = v___x_4506_;
v_isShared_4526_ = v_isSharedCheck_4530_;
goto v_resetjp_4524_;
}
else
{
lean_inc(v_a_4523_);
lean_dec(v___x_4506_);
v___x_4525_ = lean_box(0);
v_isShared_4526_ = v_isSharedCheck_4530_;
goto v_resetjp_4524_;
}
v_resetjp_4524_:
{
lean_object* v___x_4528_; 
if (v_isShared_4526_ == 0)
{
v___x_4528_ = v___x_4525_;
goto v_reusejp_4527_;
}
else
{
lean_object* v_reuseFailAlloc_4529_; 
v_reuseFailAlloc_4529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4529_, 0, v_a_4523_);
v___x_4528_ = v_reuseFailAlloc_4529_;
goto v_reusejp_4527_;
}
v_reusejp_4527_:
{
return v___x_4528_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq___boxed(lean_object* v_e_4531_, lean_object* v_a_4532_, lean_object* v_a_4533_, lean_object* v_a_4534_, lean_object* v_a_4535_, lean_object* v_a_4536_, lean_object* v_a_4537_, lean_object* v_a_4538_, lean_object* v_a_4539_, lean_object* v_a_4540_, lean_object* v_a_4541_, lean_object* v_a_4542_){
_start:
{
lean_object* v_res_4543_; 
v_res_4543_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq(v_e_4531_, v_a_4532_, v_a_4533_, v_a_4534_, v_a_4535_, v_a_4536_, v_a_4537_, v_a_4538_, v_a_4539_, v_a_4540_, v_a_4541_);
lean_dec(v_a_4541_);
lean_dec_ref(v_a_4540_);
lean_dec(v_a_4539_);
lean_dec_ref(v_a_4538_);
lean_dec(v_a_4537_);
lean_dec_ref(v_a_4536_);
lean_dec(v_a_4535_);
lean_dec_ref(v_a_4534_);
lean_dec(v_a_4533_);
lean_dec(v_a_4532_);
return v_res_4543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE(lean_object* v_e_4544_, lean_object* v_a_4545_, lean_object* v_a_4546_, lean_object* v_a_4547_, lean_object* v_a_4548_, lean_object* v_a_4549_, lean_object* v_a_4550_, lean_object* v_a_4551_, lean_object* v_a_4552_, lean_object* v_a_4553_, lean_object* v_a_4554_){
_start:
{
lean_object* v___x_4556_; 
v___x_4556_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq(v_e_4544_, v_a_4545_, v_a_4546_, v_a_4547_, v_a_4548_, v_a_4549_, v_a_4550_, v_a_4551_, v_a_4552_, v_a_4553_, v_a_4554_);
return v___x_4556_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___boxed(lean_object* v_e_4557_, lean_object* v_a_4558_, lean_object* v_a_4559_, lean_object* v_a_4560_, lean_object* v_a_4561_, lean_object* v_a_4562_, lean_object* v_a_4563_, lean_object* v_a_4564_, lean_object* v_a_4565_, lean_object* v_a_4566_, lean_object* v_a_4567_, lean_object* v_a_4568_){
_start:
{
lean_object* v_res_4569_; 
v_res_4569_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE(v_e_4557_, v_a_4558_, v_a_4559_, v_a_4560_, v_a_4561_, v_a_4562_, v_a_4563_, v_a_4564_, v_a_4565_, v_a_4566_, v_a_4567_);
lean_dec(v_a_4567_);
lean_dec_ref(v_a_4566_);
lean_dec(v_a_4565_);
lean_dec_ref(v_a_4564_);
lean_dec(v_a_4563_);
lean_dec_ref(v_a_4562_);
lean_dec(v_a_4561_);
lean_dec_ref(v_a_4560_);
lean_dec(v_a_4559_);
lean_dec(v_a_4558_);
return v_res_4569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_9_(){
_start:
{
lean_object* v___f_4577_; lean_object* v___x_4578_; lean_object* v___x_4579_; 
v___f_4577_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_9_));
v___x_4578_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_9_));
v___x_4579_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_4578_, v___f_4577_);
return v___x_4579_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_9____boxed(lean_object* v_a_4580_){
_start:
{
lean_object* v_res_4581_; 
v_res_4581_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_9_();
return v_res_4581_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT(lean_object* v_e_4582_, lean_object* v_a_4583_, lean_object* v_a_4584_, lean_object* v_a_4585_, lean_object* v_a_4586_, lean_object* v_a_4587_, lean_object* v_a_4588_, lean_object* v_a_4589_, lean_object* v_a_4590_, lean_object* v_a_4591_, lean_object* v_a_4592_){
_start:
{
lean_object* v___x_4594_; 
v___x_4594_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq(v_e_4582_, v_a_4583_, v_a_4584_, v_a_4585_, v_a_4586_, v_a_4587_, v_a_4588_, v_a_4589_, v_a_4590_, v_a_4591_, v_a_4592_);
return v___x_4594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___boxed(lean_object* v_e_4595_, lean_object* v_a_4596_, lean_object* v_a_4597_, lean_object* v_a_4598_, lean_object* v_a_4599_, lean_object* v_a_4600_, lean_object* v_a_4601_, lean_object* v_a_4602_, lean_object* v_a_4603_, lean_object* v_a_4604_, lean_object* v_a_4605_, lean_object* v_a_4606_){
_start:
{
lean_object* v_res_4607_; 
v_res_4607_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT(v_e_4595_, v_a_4596_, v_a_4597_, v_a_4598_, v_a_4599_, v_a_4600_, v_a_4601_, v_a_4602_, v_a_4603_, v_a_4604_, v_a_4605_);
lean_dec(v_a_4605_);
lean_dec_ref(v_a_4604_);
lean_dec(v_a_4603_);
lean_dec_ref(v_a_4602_);
lean_dec(v_a_4601_);
lean_dec_ref(v_a_4600_);
lean_dec(v_a_4599_);
lean_dec_ref(v_a_4598_);
lean_dec(v_a_4597_);
lean_dec(v_a_4596_);
return v_res_4607_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_1204040634____hygCtx___hyg_9_(){
_start:
{
lean_object* v___f_4614_; lean_object* v___x_4615_; lean_object* v___x_4616_; 
v___f_4614_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_9_));
v___x_4615_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_1204040634____hygCtx___hyg_9_));
v___x_4616_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_4615_, v___f_4614_);
return v___x_4616_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_1204040634____hygCtx___hyg_9____boxed(lean_object* v_a_4617_){
_start:
{
lean_object* v_res_4618_; 
v_res_4618_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_1204040634____hygCtx___hyg_9_();
return v_res_4618_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f___redArg(lean_object* v_e_4619_, lean_object* v_a_4620_, lean_object* v_a_4621_){
_start:
{
lean_object* v___x_4623_; 
v___x_4623_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_4620_, v_a_4621_);
if (lean_obj_tag(v___x_4623_) == 0)
{
lean_object* v_a_4624_; lean_object* v___x_4626_; uint8_t v_isShared_4627_; uint8_t v_isSharedCheck_4633_; 
v_a_4624_ = lean_ctor_get(v___x_4623_, 0);
v_isSharedCheck_4633_ = !lean_is_exclusive(v___x_4623_);
if (v_isSharedCheck_4633_ == 0)
{
v___x_4626_ = v___x_4623_;
v_isShared_4627_ = v_isSharedCheck_4633_;
goto v_resetjp_4625_;
}
else
{
lean_inc(v_a_4624_);
lean_dec(v___x_4623_);
v___x_4626_ = lean_box(0);
v_isShared_4627_ = v_isSharedCheck_4633_;
goto v_resetjp_4625_;
}
v_resetjp_4625_:
{
lean_object* v_termMap_4628_; lean_object* v___x_4629_; lean_object* v___x_4631_; 
v_termMap_4628_ = lean_ctor_get(v_a_4624_, 3);
lean_inc_ref(v_termMap_4628_);
lean_dec(v_a_4624_);
v___x_4629_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMap_4628_, v_e_4619_);
lean_dec_ref(v_termMap_4628_);
if (v_isShared_4627_ == 0)
{
lean_ctor_set(v___x_4626_, 0, v___x_4629_);
v___x_4631_ = v___x_4626_;
goto v_reusejp_4630_;
}
else
{
lean_object* v_reuseFailAlloc_4632_; 
v_reuseFailAlloc_4632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4632_, 0, v___x_4629_);
v___x_4631_ = v_reuseFailAlloc_4632_;
goto v_reusejp_4630_;
}
v_reusejp_4630_:
{
return v___x_4631_;
}
}
}
else
{
lean_object* v_a_4634_; lean_object* v___x_4636_; uint8_t v_isShared_4637_; uint8_t v_isSharedCheck_4641_; 
v_a_4634_ = lean_ctor_get(v___x_4623_, 0);
v_isSharedCheck_4641_ = !lean_is_exclusive(v___x_4623_);
if (v_isSharedCheck_4641_ == 0)
{
v___x_4636_ = v___x_4623_;
v_isShared_4637_ = v_isSharedCheck_4641_;
goto v_resetjp_4635_;
}
else
{
lean_inc(v_a_4634_);
lean_dec(v___x_4623_);
v___x_4636_ = lean_box(0);
v_isShared_4637_ = v_isSharedCheck_4641_;
goto v_resetjp_4635_;
}
v_resetjp_4635_:
{
lean_object* v___x_4639_; 
if (v_isShared_4637_ == 0)
{
v___x_4639_ = v___x_4636_;
goto v_reusejp_4638_;
}
else
{
lean_object* v_reuseFailAlloc_4640_; 
v_reuseFailAlloc_4640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4640_, 0, v_a_4634_);
v___x_4639_ = v_reuseFailAlloc_4640_;
goto v_reusejp_4638_;
}
v_reusejp_4638_:
{
return v___x_4639_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f___redArg___boxed(lean_object* v_e_4642_, lean_object* v_a_4643_, lean_object* v_a_4644_, lean_object* v_a_4645_){
_start:
{
lean_object* v_res_4646_; 
v_res_4646_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f___redArg(v_e_4642_, v_a_4643_, v_a_4644_);
lean_dec_ref(v_a_4644_);
lean_dec(v_a_4643_);
lean_dec_ref(v_e_4642_);
return v_res_4646_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f(lean_object* v_e_4647_, lean_object* v_a_4648_, lean_object* v_a_4649_, lean_object* v_a_4650_, lean_object* v_a_4651_, lean_object* v_a_4652_, lean_object* v_a_4653_, lean_object* v_a_4654_, lean_object* v_a_4655_, lean_object* v_a_4656_, lean_object* v_a_4657_){
_start:
{
lean_object* v___x_4659_; 
v___x_4659_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f___redArg(v_e_4647_, v_a_4648_, v_a_4656_);
return v___x_4659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f___boxed(lean_object* v_e_4660_, lean_object* v_a_4661_, lean_object* v_a_4662_, lean_object* v_a_4663_, lean_object* v_a_4664_, lean_object* v_a_4665_, lean_object* v_a_4666_, lean_object* v_a_4667_, lean_object* v_a_4668_, lean_object* v_a_4669_, lean_object* v_a_4670_, lean_object* v_a_4671_){
_start:
{
lean_object* v_res_4672_; 
v_res_4672_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f(v_e_4660_, v_a_4661_, v_a_4662_, v_a_4663_, v_a_4664_, v_a_4665_, v_a_4666_, v_a_4667_, v_a_4668_, v_a_4669_, v_a_4670_);
lean_dec(v_a_4670_);
lean_dec_ref(v_a_4669_);
lean_dec(v_a_4668_);
lean_dec_ref(v_a_4667_);
lean_dec(v_a_4666_);
lean_dec_ref(v_a_4665_);
lean_dec(v_a_4664_);
lean_dec_ref(v_a_4663_);
lean_dec(v_a_4662_);
lean_dec(v_a_4661_);
lean_dec_ref(v_e_4660_);
return v_res_4672_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__8(void){
_start:
{
uint8_t v___x_4697_; lean_object* v___x_4698_; lean_object* v___x_4699_; 
v___x_4697_ = 0;
v___x_4698_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4);
v___x_4699_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4699_, 0, v___x_4698_);
lean_ctor_set_uint8(v___x_4699_, sizeof(void*)*1, v___x_4697_);
return v___x_4699_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__10(void){
_start:
{
lean_object* v___x_4701_; lean_object* v___x_4702_; 
v___x_4701_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__9));
v___x_4702_ = l_Lean_stringToMessageData(v___x_4701_);
return v___x_4702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go(lean_object* v_a_4703_, lean_object* v_b_4704_, lean_object* v_h_4705_, lean_object* v_a_4706_, lean_object* v_a_4707_, lean_object* v_a_4708_, lean_object* v_a_4709_, lean_object* v_a_4710_, lean_object* v_a_4711_, lean_object* v_a_4712_, lean_object* v_a_4713_, lean_object* v_a_4714_, lean_object* v_a_4715_){
_start:
{
lean_object* v___y_4718_; lean_object* v___y_4719_; lean_object* v___y_4720_; lean_object* v___y_4721_; lean_object* v___y_4722_; lean_object* v___y_4723_; lean_object* v___y_4724_; lean_object* v___y_4725_; lean_object* v___y_4726_; lean_object* v___y_4727_; lean_object* v___y_4728_; lean_object* v___x_4816_; 
v___x_4816_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___redArg(v_a_4703_, v_a_4706_, v_a_4714_);
if (lean_obj_tag(v___x_4816_) == 0)
{
lean_object* v_a_4817_; lean_object* v___x_4819_; uint8_t v_isShared_4820_; uint8_t v_isSharedCheck_4863_; 
v_a_4817_ = lean_ctor_get(v___x_4816_, 0);
v_isSharedCheck_4863_ = !lean_is_exclusive(v___x_4816_);
if (v_isSharedCheck_4863_ == 0)
{
v___x_4819_ = v___x_4816_;
v_isShared_4820_ = v_isSharedCheck_4863_;
goto v_resetjp_4818_;
}
else
{
lean_inc(v_a_4817_);
lean_dec(v___x_4816_);
v___x_4819_ = lean_box(0);
v_isShared_4820_ = v_isSharedCheck_4863_;
goto v_resetjp_4818_;
}
v_resetjp_4818_:
{
if (lean_obj_tag(v_a_4817_) == 1)
{
lean_object* v_val_4821_; lean_object* v___x_4822_; 
lean_del_object(v___x_4819_);
v_val_4821_ = lean_ctor_get(v_a_4817_, 0);
lean_inc(v_val_4821_);
lean_dec_ref_known(v_a_4817_, 1);
v___x_4822_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___redArg(v_b_4704_, v_a_4706_, v_a_4714_);
if (lean_obj_tag(v___x_4822_) == 0)
{
lean_object* v_a_4823_; lean_object* v___x_4825_; uint8_t v_isShared_4826_; uint8_t v_isSharedCheck_4850_; 
v_a_4823_ = lean_ctor_get(v___x_4822_, 0);
v_isSharedCheck_4850_ = !lean_is_exclusive(v___x_4822_);
if (v_isSharedCheck_4850_ == 0)
{
v___x_4825_ = v___x_4822_;
v_isShared_4826_ = v_isSharedCheck_4850_;
goto v_resetjp_4824_;
}
else
{
lean_inc(v_a_4823_);
lean_dec(v___x_4822_);
v___x_4825_ = lean_box(0);
v_isShared_4826_ = v_isSharedCheck_4850_;
goto v_resetjp_4824_;
}
v_resetjp_4824_:
{
if (lean_obj_tag(v_a_4823_) == 1)
{
lean_object* v_val_4827_; uint8_t v___x_4828_; 
v_val_4827_ = lean_ctor_get(v_a_4823_, 0);
lean_inc(v_val_4827_);
lean_dec_ref_known(v_a_4823_, 1);
v___x_4828_ = lean_nat_dec_eq(v_val_4821_, v_val_4827_);
lean_dec(v_val_4827_);
if (v___x_4828_ == 0)
{
lean_object* v___x_4829_; lean_object* v___x_4831_; 
lean_dec(v_val_4821_);
lean_dec_ref(v_h_4705_);
lean_dec_ref(v_b_4704_);
lean_dec_ref(v_a_4703_);
v___x_4829_ = lean_box(0);
if (v_isShared_4826_ == 0)
{
lean_ctor_set(v___x_4825_, 0, v___x_4829_);
v___x_4831_ = v___x_4825_;
goto v_reusejp_4830_;
}
else
{
lean_object* v_reuseFailAlloc_4832_; 
v_reuseFailAlloc_4832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4832_, 0, v___x_4829_);
v___x_4831_ = v_reuseFailAlloc_4832_;
goto v_reusejp_4830_;
}
v_reusejp_4830_:
{
return v___x_4831_;
}
}
else
{
lean_object* v_toCold_4833_; lean_object* v_options_4834_; uint8_t v_hasTrace_4835_; 
lean_del_object(v___x_4825_);
v_toCold_4833_ = lean_ctor_get(v_a_4714_, 0);
v_options_4834_ = lean_ctor_get(v_toCold_4833_, 2);
v_hasTrace_4835_ = lean_ctor_get_uint8(v_options_4834_, sizeof(void*)*1);
if (v_hasTrace_4835_ == 0)
{
v___y_4718_ = v_val_4821_;
v___y_4719_ = v_a_4706_;
v___y_4720_ = v_a_4707_;
v___y_4721_ = v_a_4708_;
v___y_4722_ = v_a_4709_;
v___y_4723_ = v_a_4710_;
v___y_4724_ = v_a_4711_;
v___y_4725_ = v_a_4712_;
v___y_4726_ = v_a_4713_;
v___y_4727_ = v_a_4714_;
v___y_4728_ = v_a_4715_;
goto v___jp_4717_;
}
else
{
lean_object* v_inheritedTraceOptions_4836_; lean_object* v___x_4837_; lean_object* v___x_4838_; uint8_t v___x_4839_; 
v_inheritedTraceOptions_4836_ = lean_ctor_get(v_toCold_4833_, 11);
v___x_4837_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__4));
v___x_4838_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5);
v___x_4839_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4836_, v_options_4834_, v___x_4838_);
if (v___x_4839_ == 0)
{
v___y_4718_ = v_val_4821_;
v___y_4719_ = v_a_4706_;
v___y_4720_ = v_a_4707_;
v___y_4721_ = v_a_4708_;
v___y_4722_ = v_a_4709_;
v___y_4723_ = v_a_4710_;
v___y_4724_ = v_a_4711_;
v___y_4725_ = v_a_4712_;
v___y_4726_ = v_a_4713_;
v___y_4727_ = v_a_4714_;
v___y_4728_ = v_a_4715_;
goto v___jp_4717_;
}
else
{
lean_object* v___x_4840_; lean_object* v___x_4841_; lean_object* v___x_4842_; lean_object* v___x_4843_; lean_object* v___x_4844_; lean_object* v___x_4845_; 
lean_inc_ref(v_a_4703_);
v___x_4840_ = l_Lean_MessageData_ofExpr(v_a_4703_);
v___x_4841_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__10, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__10);
v___x_4842_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4842_, 0, v___x_4840_);
lean_ctor_set(v___x_4842_, 1, v___x_4841_);
lean_inc_ref(v_b_4704_);
v___x_4843_ = l_Lean_MessageData_ofExpr(v_b_4704_);
v___x_4844_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4844_, 0, v___x_4842_);
lean_ctor_set(v___x_4844_, 1, v___x_4843_);
v___x_4845_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(v___x_4837_, v___x_4844_, v_a_4712_, v_a_4713_, v_a_4714_, v_a_4715_);
if (lean_obj_tag(v___x_4845_) == 0)
{
lean_dec_ref_known(v___x_4845_, 1);
v___y_4718_ = v_val_4821_;
v___y_4719_ = v_a_4706_;
v___y_4720_ = v_a_4707_;
v___y_4721_ = v_a_4708_;
v___y_4722_ = v_a_4709_;
v___y_4723_ = v_a_4710_;
v___y_4724_ = v_a_4711_;
v___y_4725_ = v_a_4712_;
v___y_4726_ = v_a_4713_;
v___y_4727_ = v_a_4714_;
v___y_4728_ = v_a_4715_;
goto v___jp_4717_;
}
else
{
lean_dec(v_val_4821_);
lean_dec_ref(v_h_4705_);
lean_dec_ref(v_b_4704_);
lean_dec_ref(v_a_4703_);
return v___x_4845_;
}
}
}
}
}
else
{
lean_object* v___x_4846_; lean_object* v___x_4848_; 
lean_dec(v_a_4823_);
lean_dec(v_val_4821_);
lean_dec_ref(v_h_4705_);
lean_dec_ref(v_b_4704_);
lean_dec_ref(v_a_4703_);
v___x_4846_ = lean_box(0);
if (v_isShared_4826_ == 0)
{
lean_ctor_set(v___x_4825_, 0, v___x_4846_);
v___x_4848_ = v___x_4825_;
goto v_reusejp_4847_;
}
else
{
lean_object* v_reuseFailAlloc_4849_; 
v_reuseFailAlloc_4849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4849_, 0, v___x_4846_);
v___x_4848_ = v_reuseFailAlloc_4849_;
goto v_reusejp_4847_;
}
v_reusejp_4847_:
{
return v___x_4848_;
}
}
}
}
else
{
lean_object* v_a_4851_; lean_object* v___x_4853_; uint8_t v_isShared_4854_; uint8_t v_isSharedCheck_4858_; 
lean_dec(v_val_4821_);
lean_dec_ref(v_h_4705_);
lean_dec_ref(v_b_4704_);
lean_dec_ref(v_a_4703_);
v_a_4851_ = lean_ctor_get(v___x_4822_, 0);
v_isSharedCheck_4858_ = !lean_is_exclusive(v___x_4822_);
if (v_isSharedCheck_4858_ == 0)
{
v___x_4853_ = v___x_4822_;
v_isShared_4854_ = v_isSharedCheck_4858_;
goto v_resetjp_4852_;
}
else
{
lean_inc(v_a_4851_);
lean_dec(v___x_4822_);
v___x_4853_ = lean_box(0);
v_isShared_4854_ = v_isSharedCheck_4858_;
goto v_resetjp_4852_;
}
v_resetjp_4852_:
{
lean_object* v___x_4856_; 
if (v_isShared_4854_ == 0)
{
v___x_4856_ = v___x_4853_;
goto v_reusejp_4855_;
}
else
{
lean_object* v_reuseFailAlloc_4857_; 
v_reuseFailAlloc_4857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4857_, 0, v_a_4851_);
v___x_4856_ = v_reuseFailAlloc_4857_;
goto v_reusejp_4855_;
}
v_reusejp_4855_:
{
return v___x_4856_;
}
}
}
}
else
{
lean_object* v___x_4859_; lean_object* v___x_4861_; 
lean_dec(v_a_4817_);
lean_dec_ref(v_h_4705_);
lean_dec_ref(v_b_4704_);
lean_dec_ref(v_a_4703_);
v___x_4859_ = lean_box(0);
if (v_isShared_4820_ == 0)
{
lean_ctor_set(v___x_4819_, 0, v___x_4859_);
v___x_4861_ = v___x_4819_;
goto v_reusejp_4860_;
}
else
{
lean_object* v_reuseFailAlloc_4862_; 
v_reuseFailAlloc_4862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4862_, 0, v___x_4859_);
v___x_4861_ = v_reuseFailAlloc_4862_;
goto v_reusejp_4860_;
}
v_reusejp_4860_:
{
return v___x_4861_;
}
}
}
}
else
{
lean_object* v_a_4864_; lean_object* v___x_4866_; uint8_t v_isShared_4867_; uint8_t v_isSharedCheck_4871_; 
lean_dec_ref(v_h_4705_);
lean_dec_ref(v_b_4704_);
lean_dec_ref(v_a_4703_);
v_a_4864_ = lean_ctor_get(v___x_4816_, 0);
v_isSharedCheck_4871_ = !lean_is_exclusive(v___x_4816_);
if (v_isSharedCheck_4871_ == 0)
{
v___x_4866_ = v___x_4816_;
v_isShared_4867_ = v_isSharedCheck_4871_;
goto v_resetjp_4865_;
}
else
{
lean_inc(v_a_4864_);
lean_dec(v___x_4816_);
v___x_4866_ = lean_box(0);
v_isShared_4867_ = v_isSharedCheck_4871_;
goto v_resetjp_4865_;
}
v_resetjp_4865_:
{
lean_object* v___x_4869_; 
if (v_isShared_4867_ == 0)
{
v___x_4869_ = v___x_4866_;
goto v_reusejp_4868_;
}
else
{
lean_object* v_reuseFailAlloc_4870_; 
v_reuseFailAlloc_4870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4870_, 0, v_a_4864_);
v___x_4869_ = v_reuseFailAlloc_4870_;
goto v_reusejp_4868_;
}
v_reusejp_4868_:
{
return v___x_4869_;
}
}
}
v___jp_4717_:
{
lean_object* v___x_4729_; 
lean_inc_ref(v_a_4703_);
v___x_4729_ = l_Lean_Meta_Grind_Order_getNodeId___redArg(v_a_4703_, v___y_4718_, v___y_4719_, v___y_4725_, v___y_4726_, v___y_4727_, v___y_4728_);
if (lean_obj_tag(v___x_4729_) == 0)
{
lean_object* v_a_4730_; lean_object* v___x_4731_; 
v_a_4730_ = lean_ctor_get(v___x_4729_, 0);
lean_inc(v_a_4730_);
lean_dec_ref_known(v___x_4729_, 1);
lean_inc_ref(v_b_4704_);
v___x_4731_ = l_Lean_Meta_Grind_Order_getNodeId___redArg(v_b_4704_, v___y_4718_, v___y_4719_, v___y_4725_, v___y_4726_, v___y_4727_, v___y_4728_);
if (lean_obj_tag(v___x_4731_) == 0)
{
lean_object* v_a_4732_; lean_object* v___x_4733_; 
v_a_4732_ = lean_ctor_get(v___x_4731_, 0);
lean_inc(v_a_4732_);
lean_dec_ref_known(v___x_4731_, 1);
v___x_4733_ = l_Lean_Meta_Grind_Order_isRing(v___y_4718_, v___y_4719_, v___y_4720_, v___y_4721_, v___y_4722_, v___y_4723_, v___y_4724_, v___y_4725_, v___y_4726_, v___y_4727_, v___y_4728_);
if (lean_obj_tag(v___x_4733_) == 0)
{
lean_object* v_a_4734_; uint8_t v___x_4735_; 
v_a_4734_ = lean_ctor_get(v___x_4733_, 0);
lean_inc(v_a_4734_);
lean_dec_ref_known(v___x_4733_, 1);
v___x_4735_ = lean_unbox(v_a_4734_);
if (v___x_4735_ == 0)
{
lean_object* v___x_4736_; lean_object* v___x_4737_; 
v___x_4736_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__1));
v___x_4737_ = l_Lean_Meta_Grind_Order_mkLePreorderPrefix(v___x_4736_, v___y_4718_, v___y_4719_, v___y_4720_, v___y_4721_, v___y_4722_, v___y_4723_, v___y_4724_, v___y_4725_, v___y_4726_, v___y_4727_, v___y_4728_);
if (lean_obj_tag(v___x_4737_) == 0)
{
lean_object* v_a_4738_; lean_object* v___x_4739_; lean_object* v___x_4740_; lean_object* v___x_4741_; 
v_a_4738_ = lean_ctor_get(v___x_4737_, 0);
lean_inc(v_a_4738_);
lean_dec_ref_known(v___x_4737_, 1);
lean_inc_ref(v_h_4705_);
lean_inc_ref(v_b_4704_);
lean_inc_ref(v_a_4703_);
v___x_4739_ = l_Lean_mkApp3(v_a_4738_, v_a_4703_, v_b_4704_, v_h_4705_);
v___x_4740_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__3));
v___x_4741_ = l_Lean_Meta_Grind_Order_mkLePreorderPrefix(v___x_4740_, v___y_4718_, v___y_4719_, v___y_4720_, v___y_4721_, v___y_4722_, v___y_4723_, v___y_4724_, v___y_4725_, v___y_4726_, v___y_4727_, v___y_4728_);
if (lean_obj_tag(v___x_4741_) == 0)
{
lean_object* v_a_4742_; lean_object* v___x_4743_; lean_object* v___x_4744_; lean_object* v___x_4745_; uint8_t v___x_4746_; lean_object* v___x_4747_; 
v_a_4742_ = lean_ctor_get(v___x_4741_, 0);
lean_inc(v_a_4742_);
lean_dec_ref_known(v___x_4741_, 1);
v___x_4743_ = l_Lean_mkApp3(v_a_4742_, v_a_4703_, v_b_4704_, v_h_4705_);
v___x_4744_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4);
v___x_4745_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4745_, 0, v___x_4744_);
v___x_4746_ = lean_unbox(v_a_4734_);
lean_dec(v_a_4734_);
lean_ctor_set_uint8(v___x_4745_, sizeof(void*)*1, v___x_4746_);
lean_inc_ref(v___x_4745_);
lean_inc(v_a_4732_);
lean_inc(v_a_4730_);
v___x_4747_ = l_Lean_Meta_Grind_Order_addEdge(v_a_4730_, v_a_4732_, v___x_4745_, v___x_4739_, v___y_4718_, v___y_4719_, v___y_4720_, v___y_4721_, v___y_4722_, v___y_4723_, v___y_4724_, v___y_4725_, v___y_4726_, v___y_4727_, v___y_4728_);
if (lean_obj_tag(v___x_4747_) == 0)
{
lean_object* v___x_4748_; 
lean_dec_ref_known(v___x_4747_, 1);
v___x_4748_ = l_Lean_Meta_Grind_Order_addEdge(v_a_4732_, v_a_4730_, v___x_4745_, v___x_4743_, v___y_4718_, v___y_4719_, v___y_4720_, v___y_4721_, v___y_4722_, v___y_4723_, v___y_4724_, v___y_4725_, v___y_4726_, v___y_4727_, v___y_4728_);
lean_dec(v___y_4718_);
return v___x_4748_;
}
else
{
lean_dec_ref_known(v___x_4745_, 1);
lean_dec_ref(v___x_4743_);
lean_dec(v_a_4732_);
lean_dec(v_a_4730_);
lean_dec(v___y_4718_);
return v___x_4747_;
}
}
else
{
lean_object* v_a_4749_; lean_object* v___x_4751_; uint8_t v_isShared_4752_; uint8_t v_isSharedCheck_4756_; 
lean_dec_ref(v___x_4739_);
lean_dec(v_a_4734_);
lean_dec(v_a_4732_);
lean_dec(v_a_4730_);
lean_dec(v___y_4718_);
lean_dec_ref(v_h_4705_);
lean_dec_ref(v_b_4704_);
lean_dec_ref(v_a_4703_);
v_a_4749_ = lean_ctor_get(v___x_4741_, 0);
v_isSharedCheck_4756_ = !lean_is_exclusive(v___x_4741_);
if (v_isSharedCheck_4756_ == 0)
{
v___x_4751_ = v___x_4741_;
v_isShared_4752_ = v_isSharedCheck_4756_;
goto v_resetjp_4750_;
}
else
{
lean_inc(v_a_4749_);
lean_dec(v___x_4741_);
v___x_4751_ = lean_box(0);
v_isShared_4752_ = v_isSharedCheck_4756_;
goto v_resetjp_4750_;
}
v_resetjp_4750_:
{
lean_object* v___x_4754_; 
if (v_isShared_4752_ == 0)
{
v___x_4754_ = v___x_4751_;
goto v_reusejp_4753_;
}
else
{
lean_object* v_reuseFailAlloc_4755_; 
v_reuseFailAlloc_4755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4755_, 0, v_a_4749_);
v___x_4754_ = v_reuseFailAlloc_4755_;
goto v_reusejp_4753_;
}
v_reusejp_4753_:
{
return v___x_4754_;
}
}
}
}
else
{
lean_object* v_a_4757_; lean_object* v___x_4759_; uint8_t v_isShared_4760_; uint8_t v_isSharedCheck_4764_; 
lean_dec(v_a_4734_);
lean_dec(v_a_4732_);
lean_dec(v_a_4730_);
lean_dec(v___y_4718_);
lean_dec_ref(v_h_4705_);
lean_dec_ref(v_b_4704_);
lean_dec_ref(v_a_4703_);
v_a_4757_ = lean_ctor_get(v___x_4737_, 0);
v_isSharedCheck_4764_ = !lean_is_exclusive(v___x_4737_);
if (v_isSharedCheck_4764_ == 0)
{
v___x_4759_ = v___x_4737_;
v_isShared_4760_ = v_isSharedCheck_4764_;
goto v_resetjp_4758_;
}
else
{
lean_inc(v_a_4757_);
lean_dec(v___x_4737_);
v___x_4759_ = lean_box(0);
v_isShared_4760_ = v_isSharedCheck_4764_;
goto v_resetjp_4758_;
}
v_resetjp_4758_:
{
lean_object* v___x_4762_; 
if (v_isShared_4760_ == 0)
{
v___x_4762_ = v___x_4759_;
goto v_reusejp_4761_;
}
else
{
lean_object* v_reuseFailAlloc_4763_; 
v_reuseFailAlloc_4763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4763_, 0, v_a_4757_);
v___x_4762_ = v_reuseFailAlloc_4763_;
goto v_reusejp_4761_;
}
v_reusejp_4761_:
{
return v___x_4762_;
}
}
}
}
else
{
lean_object* v___x_4765_; lean_object* v___x_4766_; 
lean_dec(v_a_4734_);
v___x_4765_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__5));
v___x_4766_ = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(v___x_4765_, v___y_4718_, v___y_4719_, v___y_4720_, v___y_4721_, v___y_4722_, v___y_4723_, v___y_4724_, v___y_4725_, v___y_4726_, v___y_4727_, v___y_4728_);
if (lean_obj_tag(v___x_4766_) == 0)
{
lean_object* v_a_4767_; lean_object* v___x_4768_; lean_object* v___x_4769_; lean_object* v___x_4770_; 
v_a_4767_ = lean_ctor_get(v___x_4766_, 0);
lean_inc(v_a_4767_);
lean_dec_ref_known(v___x_4766_, 1);
lean_inc_ref(v_h_4705_);
lean_inc_ref(v_b_4704_);
lean_inc_ref(v_a_4703_);
v___x_4768_ = l_Lean_mkApp3(v_a_4767_, v_a_4703_, v_b_4704_, v_h_4705_);
v___x_4769_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__7));
v___x_4770_ = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(v___x_4769_, v___y_4718_, v___y_4719_, v___y_4720_, v___y_4721_, v___y_4722_, v___y_4723_, v___y_4724_, v___y_4725_, v___y_4726_, v___y_4727_, v___y_4728_);
if (lean_obj_tag(v___x_4770_) == 0)
{
lean_object* v_a_4771_; lean_object* v___x_4772_; lean_object* v___x_4773_; lean_object* v___x_4774_; 
v_a_4771_ = lean_ctor_get(v___x_4770_, 0);
lean_inc(v_a_4771_);
lean_dec_ref_known(v___x_4770_, 1);
v___x_4772_ = l_Lean_mkApp3(v_a_4771_, v_a_4703_, v_b_4704_, v_h_4705_);
v___x_4773_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__8, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__8);
lean_inc(v_a_4732_);
lean_inc(v_a_4730_);
v___x_4774_ = l_Lean_Meta_Grind_Order_addEdge(v_a_4730_, v_a_4732_, v___x_4773_, v___x_4768_, v___y_4718_, v___y_4719_, v___y_4720_, v___y_4721_, v___y_4722_, v___y_4723_, v___y_4724_, v___y_4725_, v___y_4726_, v___y_4727_, v___y_4728_);
if (lean_obj_tag(v___x_4774_) == 0)
{
lean_object* v___x_4775_; 
lean_dec_ref_known(v___x_4774_, 1);
v___x_4775_ = l_Lean_Meta_Grind_Order_addEdge(v_a_4732_, v_a_4730_, v___x_4773_, v___x_4772_, v___y_4718_, v___y_4719_, v___y_4720_, v___y_4721_, v___y_4722_, v___y_4723_, v___y_4724_, v___y_4725_, v___y_4726_, v___y_4727_, v___y_4728_);
lean_dec(v___y_4718_);
return v___x_4775_;
}
else
{
lean_dec_ref(v___x_4772_);
lean_dec(v_a_4732_);
lean_dec(v_a_4730_);
lean_dec(v___y_4718_);
return v___x_4774_;
}
}
else
{
lean_object* v_a_4776_; lean_object* v___x_4778_; uint8_t v_isShared_4779_; uint8_t v_isSharedCheck_4783_; 
lean_dec_ref(v___x_4768_);
lean_dec(v_a_4732_);
lean_dec(v_a_4730_);
lean_dec(v___y_4718_);
lean_dec_ref(v_h_4705_);
lean_dec_ref(v_b_4704_);
lean_dec_ref(v_a_4703_);
v_a_4776_ = lean_ctor_get(v___x_4770_, 0);
v_isSharedCheck_4783_ = !lean_is_exclusive(v___x_4770_);
if (v_isSharedCheck_4783_ == 0)
{
v___x_4778_ = v___x_4770_;
v_isShared_4779_ = v_isSharedCheck_4783_;
goto v_resetjp_4777_;
}
else
{
lean_inc(v_a_4776_);
lean_dec(v___x_4770_);
v___x_4778_ = lean_box(0);
v_isShared_4779_ = v_isSharedCheck_4783_;
goto v_resetjp_4777_;
}
v_resetjp_4777_:
{
lean_object* v___x_4781_; 
if (v_isShared_4779_ == 0)
{
v___x_4781_ = v___x_4778_;
goto v_reusejp_4780_;
}
else
{
lean_object* v_reuseFailAlloc_4782_; 
v_reuseFailAlloc_4782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4782_, 0, v_a_4776_);
v___x_4781_ = v_reuseFailAlloc_4782_;
goto v_reusejp_4780_;
}
v_reusejp_4780_:
{
return v___x_4781_;
}
}
}
}
else
{
lean_object* v_a_4784_; lean_object* v___x_4786_; uint8_t v_isShared_4787_; uint8_t v_isSharedCheck_4791_; 
lean_dec(v_a_4732_);
lean_dec(v_a_4730_);
lean_dec(v___y_4718_);
lean_dec_ref(v_h_4705_);
lean_dec_ref(v_b_4704_);
lean_dec_ref(v_a_4703_);
v_a_4784_ = lean_ctor_get(v___x_4766_, 0);
v_isSharedCheck_4791_ = !lean_is_exclusive(v___x_4766_);
if (v_isSharedCheck_4791_ == 0)
{
v___x_4786_ = v___x_4766_;
v_isShared_4787_ = v_isSharedCheck_4791_;
goto v_resetjp_4785_;
}
else
{
lean_inc(v_a_4784_);
lean_dec(v___x_4766_);
v___x_4786_ = lean_box(0);
v_isShared_4787_ = v_isSharedCheck_4791_;
goto v_resetjp_4785_;
}
v_resetjp_4785_:
{
lean_object* v___x_4789_; 
if (v_isShared_4787_ == 0)
{
v___x_4789_ = v___x_4786_;
goto v_reusejp_4788_;
}
else
{
lean_object* v_reuseFailAlloc_4790_; 
v_reuseFailAlloc_4790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4790_, 0, v_a_4784_);
v___x_4789_ = v_reuseFailAlloc_4790_;
goto v_reusejp_4788_;
}
v_reusejp_4788_:
{
return v___x_4789_;
}
}
}
}
}
else
{
lean_object* v_a_4792_; lean_object* v___x_4794_; uint8_t v_isShared_4795_; uint8_t v_isSharedCheck_4799_; 
lean_dec(v_a_4732_);
lean_dec(v_a_4730_);
lean_dec(v___y_4718_);
lean_dec_ref(v_h_4705_);
lean_dec_ref(v_b_4704_);
lean_dec_ref(v_a_4703_);
v_a_4792_ = lean_ctor_get(v___x_4733_, 0);
v_isSharedCheck_4799_ = !lean_is_exclusive(v___x_4733_);
if (v_isSharedCheck_4799_ == 0)
{
v___x_4794_ = v___x_4733_;
v_isShared_4795_ = v_isSharedCheck_4799_;
goto v_resetjp_4793_;
}
else
{
lean_inc(v_a_4792_);
lean_dec(v___x_4733_);
v___x_4794_ = lean_box(0);
v_isShared_4795_ = v_isSharedCheck_4799_;
goto v_resetjp_4793_;
}
v_resetjp_4793_:
{
lean_object* v___x_4797_; 
if (v_isShared_4795_ == 0)
{
v___x_4797_ = v___x_4794_;
goto v_reusejp_4796_;
}
else
{
lean_object* v_reuseFailAlloc_4798_; 
v_reuseFailAlloc_4798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4798_, 0, v_a_4792_);
v___x_4797_ = v_reuseFailAlloc_4798_;
goto v_reusejp_4796_;
}
v_reusejp_4796_:
{
return v___x_4797_;
}
}
}
}
else
{
lean_object* v_a_4800_; lean_object* v___x_4802_; uint8_t v_isShared_4803_; uint8_t v_isSharedCheck_4807_; 
lean_dec(v_a_4730_);
lean_dec(v___y_4718_);
lean_dec_ref(v_h_4705_);
lean_dec_ref(v_b_4704_);
lean_dec_ref(v_a_4703_);
v_a_4800_ = lean_ctor_get(v___x_4731_, 0);
v_isSharedCheck_4807_ = !lean_is_exclusive(v___x_4731_);
if (v_isSharedCheck_4807_ == 0)
{
v___x_4802_ = v___x_4731_;
v_isShared_4803_ = v_isSharedCheck_4807_;
goto v_resetjp_4801_;
}
else
{
lean_inc(v_a_4800_);
lean_dec(v___x_4731_);
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
lean_dec(v___y_4718_);
lean_dec_ref(v_h_4705_);
lean_dec_ref(v_b_4704_);
lean_dec_ref(v_a_4703_);
v_a_4808_ = lean_ctor_get(v___x_4729_, 0);
v_isSharedCheck_4815_ = !lean_is_exclusive(v___x_4729_);
if (v_isSharedCheck_4815_ == 0)
{
v___x_4810_ = v___x_4729_;
v_isShared_4811_ = v_isSharedCheck_4815_;
goto v_resetjp_4809_;
}
else
{
lean_inc(v_a_4808_);
lean_dec(v___x_4729_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___boxed(lean_object* v_a_4872_, lean_object* v_b_4873_, lean_object* v_h_4874_, lean_object* v_a_4875_, lean_object* v_a_4876_, lean_object* v_a_4877_, lean_object* v_a_4878_, lean_object* v_a_4879_, lean_object* v_a_4880_, lean_object* v_a_4881_, lean_object* v_a_4882_, lean_object* v_a_4883_, lean_object* v_a_4884_, lean_object* v_a_4885_){
_start:
{
lean_object* v_res_4886_; 
v_res_4886_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go(v_a_4872_, v_b_4873_, v_h_4874_, v_a_4875_, v_a_4876_, v_a_4877_, v_a_4878_, v_a_4879_, v_a_4880_, v_a_4881_, v_a_4882_, v_a_4883_, v_a_4884_);
lean_dec(v_a_4884_);
lean_dec_ref(v_a_4883_);
lean_dec(v_a_4882_);
lean_dec_ref(v_a_4881_);
lean_dec(v_a_4880_);
lean_dec_ref(v_a_4879_);
lean_dec(v_a_4878_);
lean_dec_ref(v_a_4877_);
lean_dec(v_a_4876_);
lean_dec(v_a_4875_);
return v_res_4886_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_processNewEq___closed__6(void){
_start:
{
lean_object* v___x_4902_; lean_object* v___x_4903_; lean_object* v___x_4904_; 
v___x_4902_ = lean_box(0);
v___x_4903_ = ((lean_object*)(l_Lean_Meta_Grind_Order_processNewEq___closed__5));
v___x_4904_ = l_Lean_mkConst(v___x_4903_, v___x_4902_);
return v___x_4904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_processNewEq(lean_object* v_a_4905_, lean_object* v_b_4906_, lean_object* v_a_4907_, lean_object* v_a_4908_, lean_object* v_a_4909_, lean_object* v_a_4910_, lean_object* v_a_4911_, lean_object* v_a_4912_, lean_object* v_a_4913_, lean_object* v_a_4914_, lean_object* v_a_4915_, lean_object* v_a_4916_){
_start:
{
size_t v___x_4918_; size_t v___x_4919_; uint8_t v___x_4920_; 
v___x_4918_ = lean_ptr_addr(v_a_4905_);
v___x_4919_ = lean_ptr_addr(v_b_4906_);
v___x_4920_ = lean_usize_dec_eq(v___x_4918_, v___x_4919_);
if (v___x_4920_ == 0)
{
lean_object* v___x_4921_; 
lean_inc(v_a_4916_);
lean_inc_ref(v_a_4915_);
lean_inc(v_a_4914_);
lean_inc_ref(v_a_4913_);
lean_inc(v_a_4912_);
lean_inc_ref(v_a_4911_);
lean_inc(v_a_4910_);
lean_inc_ref(v_a_4909_);
lean_inc(v_a_4908_);
lean_inc(v_a_4907_);
lean_inc_ref(v_b_4906_);
lean_inc_ref(v_a_4905_);
v___x_4921_ = lean_grind_mk_eq_proof(v_a_4905_, v_b_4906_, v_a_4907_, v_a_4908_, v_a_4909_, v_a_4910_, v_a_4911_, v_a_4912_, v_a_4913_, v_a_4914_, v_a_4915_, v_a_4916_);
if (lean_obj_tag(v___x_4921_) == 0)
{
lean_object* v_a_4922_; lean_object* v___x_4923_; 
v_a_4922_ = lean_ctor_get(v___x_4921_, 0);
lean_inc(v_a_4922_);
lean_dec_ref_known(v___x_4921_, 1);
v___x_4923_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f___redArg(v_a_4905_, v_a_4907_, v_a_4915_);
if (lean_obj_tag(v___x_4923_) == 0)
{
lean_object* v_a_4924_; 
v_a_4924_ = lean_ctor_get(v___x_4923_, 0);
lean_inc(v_a_4924_);
lean_dec_ref_known(v___x_4923_, 1);
if (lean_obj_tag(v_a_4924_) == 1)
{
lean_object* v_val_4925_; lean_object* v_e_4926_; lean_object* v_h_4927_; lean_object* v_00_u03b1_4928_; lean_object* v___x_4929_; 
v_val_4925_ = lean_ctor_get(v_a_4924_, 0);
lean_inc(v_val_4925_);
lean_dec_ref_known(v_a_4924_, 1);
v_e_4926_ = lean_ctor_get(v_val_4925_, 0);
lean_inc_ref(v_e_4926_);
v_h_4927_ = lean_ctor_get(v_val_4925_, 1);
lean_inc_ref(v_h_4927_);
v_00_u03b1_4928_ = lean_ctor_get(v_val_4925_, 2);
lean_inc_ref(v_00_u03b1_4928_);
lean_dec(v_val_4925_);
v___x_4929_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f___redArg(v_b_4906_, v_a_4907_, v_a_4915_);
if (lean_obj_tag(v___x_4929_) == 0)
{
lean_object* v_a_4930_; lean_object* v___x_4932_; uint8_t v_isShared_4933_; uint8_t v_isSharedCheck_4975_; 
v_a_4930_ = lean_ctor_get(v___x_4929_, 0);
v_isSharedCheck_4975_ = !lean_is_exclusive(v___x_4929_);
if (v_isSharedCheck_4975_ == 0)
{
v___x_4932_ = v___x_4929_;
v_isShared_4933_ = v_isSharedCheck_4975_;
goto v_resetjp_4931_;
}
else
{
lean_inc(v_a_4930_);
lean_dec(v___x_4929_);
v___x_4932_ = lean_box(0);
v_isShared_4933_ = v_isSharedCheck_4975_;
goto v_resetjp_4931_;
}
v_resetjp_4931_:
{
if (lean_obj_tag(v_a_4930_) == 1)
{
lean_object* v_val_4934_; lean_object* v_e_4935_; lean_object* v_h_4936_; lean_object* v___x_4937_; uint8_t v___x_4938_; 
lean_del_object(v___x_4932_);
v_val_4934_ = lean_ctor_get(v_a_4930_, 0);
lean_inc(v_val_4934_);
lean_dec_ref_known(v_a_4930_, 1);
v_e_4935_ = lean_ctor_get(v_val_4934_, 0);
lean_inc_ref(v_e_4935_);
v_h_4936_ = lean_ctor_get(v_val_4934_, 1);
lean_inc_ref(v_h_4936_);
lean_dec(v_val_4934_);
v___x_4937_ = l_Lean_Int_mkType;
v___x_4938_ = lean_expr_eqv(v_00_u03b1_4928_, v___x_4937_);
if (v___x_4938_ == 0)
{
lean_object* v___x_4939_; 
lean_inc_ref(v_00_u03b1_4928_);
v___x_4939_ = l_Lean_Meta_getDecLevel(v_00_u03b1_4928_, v_a_4913_, v_a_4914_, v_a_4915_, v_a_4916_);
if (lean_obj_tag(v___x_4939_) == 0)
{
lean_object* v_a_4940_; lean_object* v___x_4941_; lean_object* v___x_4942_; lean_object* v___x_4943_; lean_object* v___x_4944_; lean_object* v___x_4945_; lean_object* v___x_4946_; 
v_a_4940_ = lean_ctor_get(v___x_4939_, 0);
lean_inc(v_a_4940_);
lean_dec_ref_known(v___x_4939_, 1);
v___x_4941_ = ((lean_object*)(l_Lean_Meta_Grind_Order_processNewEq___closed__1));
v___x_4942_ = lean_box(0);
v___x_4943_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4943_, 0, v_a_4940_);
lean_ctor_set(v___x_4943_, 1, v___x_4942_);
lean_inc_ref(v___x_4943_);
v___x_4944_ = l_Lean_mkConst(v___x_4941_, v___x_4943_);
lean_inc_ref(v_00_u03b1_4928_);
v___x_4945_ = l_Lean_Expr_app___override(v___x_4944_, v_00_u03b1_4928_);
v___x_4946_ = l_Lean_Meta_Sym_synthInstance(v___x_4945_, v_a_4911_, v_a_4912_, v_a_4913_, v_a_4914_, v_a_4915_, v_a_4916_);
if (lean_obj_tag(v___x_4946_) == 0)
{
lean_object* v_a_4947_; lean_object* v___x_4948_; lean_object* v___x_4949_; lean_object* v___x_4950_; lean_object* v___x_4951_; 
v_a_4947_ = lean_ctor_get(v___x_4946_, 0);
lean_inc(v_a_4947_);
lean_dec_ref_known(v___x_4946_, 1);
v___x_4948_ = ((lean_object*)(l_Lean_Meta_Grind_Order_processNewEq___closed__3));
v___x_4949_ = l_Lean_mkConst(v___x_4948_, v___x_4943_);
lean_inc_ref(v_e_4935_);
lean_inc_ref(v_e_4926_);
v___x_4950_ = l_Lean_mkApp9(v___x_4949_, v_00_u03b1_4928_, v_a_4947_, v_a_4905_, v_b_4906_, v_e_4926_, v_e_4935_, v_h_4927_, v_h_4936_, v_a_4922_);
v___x_4951_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go(v_e_4926_, v_e_4935_, v___x_4950_, v_a_4907_, v_a_4908_, v_a_4909_, v_a_4910_, v_a_4911_, v_a_4912_, v_a_4913_, v_a_4914_, v_a_4915_, v_a_4916_);
return v___x_4951_;
}
else
{
lean_object* v_a_4952_; lean_object* v___x_4954_; uint8_t v_isShared_4955_; uint8_t v_isSharedCheck_4959_; 
lean_dec_ref_known(v___x_4943_, 2);
lean_dec_ref(v_h_4936_);
lean_dec_ref(v_e_4935_);
lean_dec_ref(v_00_u03b1_4928_);
lean_dec_ref(v_h_4927_);
lean_dec_ref(v_e_4926_);
lean_dec(v_a_4922_);
lean_dec_ref(v_b_4906_);
lean_dec_ref(v_a_4905_);
v_a_4952_ = lean_ctor_get(v___x_4946_, 0);
v_isSharedCheck_4959_ = !lean_is_exclusive(v___x_4946_);
if (v_isSharedCheck_4959_ == 0)
{
v___x_4954_ = v___x_4946_;
v_isShared_4955_ = v_isSharedCheck_4959_;
goto v_resetjp_4953_;
}
else
{
lean_inc(v_a_4952_);
lean_dec(v___x_4946_);
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
lean_dec_ref(v_h_4936_);
lean_dec_ref(v_e_4935_);
lean_dec_ref(v_00_u03b1_4928_);
lean_dec_ref(v_h_4927_);
lean_dec_ref(v_e_4926_);
lean_dec(v_a_4922_);
lean_dec_ref(v_b_4906_);
lean_dec_ref(v_a_4905_);
v_a_4960_ = lean_ctor_get(v___x_4939_, 0);
v_isSharedCheck_4967_ = !lean_is_exclusive(v___x_4939_);
if (v_isSharedCheck_4967_ == 0)
{
v___x_4962_ = v___x_4939_;
v_isShared_4963_ = v_isSharedCheck_4967_;
goto v_resetjp_4961_;
}
else
{
lean_inc(v_a_4960_);
lean_dec(v___x_4939_);
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
lean_object* v___x_4968_; lean_object* v___x_4969_; lean_object* v___x_4970_; 
lean_dec_ref(v_00_u03b1_4928_);
v___x_4968_ = lean_obj_once(&l_Lean_Meta_Grind_Order_processNewEq___closed__6, &l_Lean_Meta_Grind_Order_processNewEq___closed__6_once, _init_l_Lean_Meta_Grind_Order_processNewEq___closed__6);
lean_inc_ref(v_e_4935_);
lean_inc_ref(v_e_4926_);
v___x_4969_ = l_Lean_mkApp7(v___x_4968_, v_a_4905_, v_b_4906_, v_e_4926_, v_e_4935_, v_h_4927_, v_h_4936_, v_a_4922_);
v___x_4970_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go(v_e_4926_, v_e_4935_, v___x_4969_, v_a_4907_, v_a_4908_, v_a_4909_, v_a_4910_, v_a_4911_, v_a_4912_, v_a_4913_, v_a_4914_, v_a_4915_, v_a_4916_);
return v___x_4970_;
}
}
else
{
lean_object* v___x_4971_; lean_object* v___x_4973_; 
lean_dec(v_a_4930_);
lean_dec_ref(v_00_u03b1_4928_);
lean_dec_ref(v_h_4927_);
lean_dec_ref(v_e_4926_);
lean_dec(v_a_4922_);
lean_dec_ref(v_b_4906_);
lean_dec_ref(v_a_4905_);
v___x_4971_ = lean_box(0);
if (v_isShared_4933_ == 0)
{
lean_ctor_set(v___x_4932_, 0, v___x_4971_);
v___x_4973_ = v___x_4932_;
goto v_reusejp_4972_;
}
else
{
lean_object* v_reuseFailAlloc_4974_; 
v_reuseFailAlloc_4974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4974_, 0, v___x_4971_);
v___x_4973_ = v_reuseFailAlloc_4974_;
goto v_reusejp_4972_;
}
v_reusejp_4972_:
{
return v___x_4973_;
}
}
}
}
else
{
lean_object* v_a_4976_; lean_object* v___x_4978_; uint8_t v_isShared_4979_; uint8_t v_isSharedCheck_4983_; 
lean_dec_ref(v_00_u03b1_4928_);
lean_dec_ref(v_h_4927_);
lean_dec_ref(v_e_4926_);
lean_dec(v_a_4922_);
lean_dec_ref(v_b_4906_);
lean_dec_ref(v_a_4905_);
v_a_4976_ = lean_ctor_get(v___x_4929_, 0);
v_isSharedCheck_4983_ = !lean_is_exclusive(v___x_4929_);
if (v_isSharedCheck_4983_ == 0)
{
v___x_4978_ = v___x_4929_;
v_isShared_4979_ = v_isSharedCheck_4983_;
goto v_resetjp_4977_;
}
else
{
lean_inc(v_a_4976_);
lean_dec(v___x_4929_);
v___x_4978_ = lean_box(0);
v_isShared_4979_ = v_isSharedCheck_4983_;
goto v_resetjp_4977_;
}
v_resetjp_4977_:
{
lean_object* v___x_4981_; 
if (v_isShared_4979_ == 0)
{
v___x_4981_ = v___x_4978_;
goto v_reusejp_4980_;
}
else
{
lean_object* v_reuseFailAlloc_4982_; 
v_reuseFailAlloc_4982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4982_, 0, v_a_4976_);
v___x_4981_ = v_reuseFailAlloc_4982_;
goto v_reusejp_4980_;
}
v_reusejp_4980_:
{
return v___x_4981_;
}
}
}
}
else
{
lean_object* v___x_4984_; 
lean_dec(v_a_4924_);
v___x_4984_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go(v_a_4905_, v_b_4906_, v_a_4922_, v_a_4907_, v_a_4908_, v_a_4909_, v_a_4910_, v_a_4911_, v_a_4912_, v_a_4913_, v_a_4914_, v_a_4915_, v_a_4916_);
return v___x_4984_;
}
}
else
{
lean_object* v_a_4985_; lean_object* v___x_4987_; uint8_t v_isShared_4988_; uint8_t v_isSharedCheck_4992_; 
lean_dec(v_a_4922_);
lean_dec_ref(v_b_4906_);
lean_dec_ref(v_a_4905_);
v_a_4985_ = lean_ctor_get(v___x_4923_, 0);
v_isSharedCheck_4992_ = !lean_is_exclusive(v___x_4923_);
if (v_isSharedCheck_4992_ == 0)
{
v___x_4987_ = v___x_4923_;
v_isShared_4988_ = v_isSharedCheck_4992_;
goto v_resetjp_4986_;
}
else
{
lean_inc(v_a_4985_);
lean_dec(v___x_4923_);
v___x_4987_ = lean_box(0);
v_isShared_4988_ = v_isSharedCheck_4992_;
goto v_resetjp_4986_;
}
v_resetjp_4986_:
{
lean_object* v___x_4990_; 
if (v_isShared_4988_ == 0)
{
v___x_4990_ = v___x_4987_;
goto v_reusejp_4989_;
}
else
{
lean_object* v_reuseFailAlloc_4991_; 
v_reuseFailAlloc_4991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4991_, 0, v_a_4985_);
v___x_4990_ = v_reuseFailAlloc_4991_;
goto v_reusejp_4989_;
}
v_reusejp_4989_:
{
return v___x_4990_;
}
}
}
}
else
{
lean_object* v_a_4993_; lean_object* v___x_4995_; uint8_t v_isShared_4996_; uint8_t v_isSharedCheck_5000_; 
lean_dec_ref(v_b_4906_);
lean_dec_ref(v_a_4905_);
v_a_4993_ = lean_ctor_get(v___x_4921_, 0);
v_isSharedCheck_5000_ = !lean_is_exclusive(v___x_4921_);
if (v_isSharedCheck_5000_ == 0)
{
v___x_4995_ = v___x_4921_;
v_isShared_4996_ = v_isSharedCheck_5000_;
goto v_resetjp_4994_;
}
else
{
lean_inc(v_a_4993_);
lean_dec(v___x_4921_);
v___x_4995_ = lean_box(0);
v_isShared_4996_ = v_isSharedCheck_5000_;
goto v_resetjp_4994_;
}
v_resetjp_4994_:
{
lean_object* v___x_4998_; 
if (v_isShared_4996_ == 0)
{
v___x_4998_ = v___x_4995_;
goto v_reusejp_4997_;
}
else
{
lean_object* v_reuseFailAlloc_4999_; 
v_reuseFailAlloc_4999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4999_, 0, v_a_4993_);
v___x_4998_ = v_reuseFailAlloc_4999_;
goto v_reusejp_4997_;
}
v_reusejp_4997_:
{
return v___x_4998_;
}
}
}
}
else
{
lean_object* v___x_5001_; lean_object* v___x_5002_; 
lean_dec_ref(v_b_4906_);
lean_dec_ref(v_a_4905_);
v___x_5001_ = lean_box(0);
v___x_5002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5002_, 0, v___x_5001_);
return v___x_5002_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_processNewEq___boxed(lean_object* v_a_5003_, lean_object* v_b_5004_, lean_object* v_a_5005_, lean_object* v_a_5006_, lean_object* v_a_5007_, lean_object* v_a_5008_, lean_object* v_a_5009_, lean_object* v_a_5010_, lean_object* v_a_5011_, lean_object* v_a_5012_, lean_object* v_a_5013_, lean_object* v_a_5014_, lean_object* v_a_5015_){
_start:
{
lean_object* v_res_5016_; 
v_res_5016_ = l_Lean_Meta_Grind_Order_processNewEq(v_a_5003_, v_b_5004_, v_a_5005_, v_a_5006_, v_a_5007_, v_a_5008_, v_a_5009_, v_a_5010_, v_a_5011_, v_a_5012_, v_a_5013_, v_a_5014_);
lean_dec(v_a_5014_);
lean_dec_ref(v_a_5013_);
lean_dec(v_a_5012_);
lean_dec_ref(v_a_5011_);
lean_dec(v_a_5010_);
lean_dec_ref(v_a_5009_);
lean_dec(v_a_5008_);
lean_dec_ref(v_a_5007_);
lean_dec(v_a_5006_);
lean_dec(v_a_5005_);
return v_res_5016_;
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
