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
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath_go(lean_object* v_u_1_, lean_object* v_v_2_, lean_object* v_p_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_, lean_object* v_a_13_, lean_object* v_a_14_){
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
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_1_ = stack[0].m_obj;
lean_object* v_v_2_ = stack[1].m_obj;
lean_object* v_p_3_ = stack[2].m_obj;
lean_object* v_a_4_ = stack[3].m_obj;
lean_object* v_a_5_ = stack[4].m_obj;
lean_object* v_a_6_ = stack[5].m_obj;
lean_object* v_a_7_ = stack[6].m_obj;
lean_object* v_a_8_ = stack[7].m_obj;
lean_object* v_a_9_ = stack[8].m_obj;
lean_object* v_a_10_ = stack[9].m_obj;
lean_object* v_a_11_ = stack[10].m_obj;
lean_object* v_a_12_ = stack[11].m_obj;
lean_object* v_a_13_ = stack[12].m_obj;
lean_object* v_a_14_ = stack[13].m_obj;
lean_object* v_res_41_;
v_res_41_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath_go(v_u_1_, v_v_2_, v_p_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_, v_a_10_, v_a_11_, v_a_12_, v_a_13_, v_a_14_);
stack->m_obj
 = v_res_41_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath_go___boxed(lean_object* v_u_42_, lean_object* v_v_43_, lean_object* v_p_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath_go(v_u_42_, v_v_43_, v_p_44_, v_a_45_, v_a_46_, v_a_47_, v_a_48_, v_a_49_, v_a_50_, v_a_51_, v_a_52_, v_a_53_, v_a_54_, v_a_55_);
lean_dec(v_a_55_);
lean_dec_ref(v_a_54_);
lean_dec(v_a_53_);
lean_dec_ref(v_a_52_);
lean_dec(v_a_51_);
lean_dec_ref(v_a_50_);
lean_dec(v_a_49_);
lean_dec_ref(v_a_48_);
lean_dec(v_a_47_);
lean_dec(v_a_46_);
lean_dec(v_a_45_);
lean_dec(v_v_43_);
lean_dec(v_u_42_);
return v_res_57_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath(lean_object* v_u_58_, lean_object* v_v_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = l_Lean_Meta_Grind_Order_getProof___redArg(v_u_58_, v_v_59_, v_a_60_, v_a_61_, v_a_67_, v_a_68_, v_a_69_, v_a_70_);
if (lean_obj_tag(v___x_72_) == 0)
{
lean_object* v_a_73_; lean_object* v___x_74_; 
v_a_73_ = lean_ctor_get(v___x_72_, 0);
lean_inc(v_a_73_);
lean_dec_ref_known(v___x_72_, 1);
v___x_74_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath_go(v_u_58_, v_v_59_, v_a_73_, v_a_60_, v_a_61_, v_a_62_, v_a_63_, v_a_64_, v_a_65_, v_a_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_);
return v___x_74_;
}
else
{
lean_object* v_a_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_82_; 
v_a_75_ = lean_ctor_get(v___x_72_, 0);
v_isSharedCheck_82_ = !lean_is_exclusive(v___x_72_);
if (v_isSharedCheck_82_ == 0)
{
v___x_77_ = v___x_72_;
v_isShared_78_ = v_isSharedCheck_82_;
goto v_resetjp_76_;
}
else
{
lean_inc(v_a_75_);
lean_dec(v___x_72_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_82_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
lean_object* v___x_80_; 
if (v_isShared_78_ == 0)
{
v___x_80_ = v___x_77_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v_a_75_);
v___x_80_ = v_reuseFailAlloc_81_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
return v___x_80_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_58_ = stack[0].m_obj;
lean_object* v_v_59_ = stack[1].m_obj;
lean_object* v_a_60_ = stack[2].m_obj;
lean_object* v_a_61_ = stack[3].m_obj;
lean_object* v_a_62_ = stack[4].m_obj;
lean_object* v_a_63_ = stack[5].m_obj;
lean_object* v_a_64_ = stack[6].m_obj;
lean_object* v_a_65_ = stack[7].m_obj;
lean_object* v_a_66_ = stack[8].m_obj;
lean_object* v_a_67_ = stack[9].m_obj;
lean_object* v_a_68_ = stack[10].m_obj;
lean_object* v_a_69_ = stack[11].m_obj;
lean_object* v_a_70_ = stack[12].m_obj;
lean_object* v_res_83_;
v_res_83_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath(v_u_58_, v_v_59_, v_a_60_, v_a_61_, v_a_62_, v_a_63_, v_a_64_, v_a_65_, v_a_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_);
stack->m_obj
 = v_res_83_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath___boxed(lean_object* v_u_84_, lean_object* v_v_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath(v_u_84_, v_v_85_, v_a_86_, v_a_87_, v_a_88_, v_a_89_, v_a_90_, v_a_91_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_);
lean_dec(v_a_96_);
lean_dec_ref(v_a_95_);
lean_dec(v_a_94_);
lean_dec_ref(v_a_93_);
lean_dec(v_a_92_);
lean_dec_ref(v_a_91_);
lean_dec(v_a_90_);
lean_dec_ref(v_a_89_);
lean_dec(v_a_88_);
lean_dec(v_a_87_);
lean_dec(v_a_86_);
lean_dec(v_v_85_);
lean_dec(v_u_84_);
return v_res_98_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setUnsat(lean_object* v_u_99_, lean_object* v_v_100_, lean_object* v_kuv_101_, lean_object* v_huv_102_, lean_object* v_kvu_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath(v_v_100_, v_u_99_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, v_a_111_, v_a_112_, v_a_113_, v_a_114_);
if (lean_obj_tag(v___x_116_) == 0)
{
lean_object* v_a_117_; lean_object* v___x_118_; 
v_a_117_ = lean_ctor_get(v___x_116_, 0);
lean_inc(v_a_117_);
lean_dec_ref_known(v___x_116_, 1);
v___x_118_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_u_99_, v_a_104_, v_a_105_, v_a_113_);
if (lean_obj_tag(v___x_118_) == 0)
{
lean_object* v_a_119_; lean_object* v___x_120_; 
v_a_119_ = lean_ctor_get(v___x_118_, 0);
lean_inc(v_a_119_);
lean_dec_ref_known(v___x_118_, 1);
v___x_120_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_v_100_, v_a_104_, v_a_105_, v_a_113_);
if (lean_obj_tag(v___x_120_) == 0)
{
lean_object* v_a_121_; lean_object* v___x_122_; 
v_a_121_ = lean_ctor_get(v___x_120_, 0);
lean_inc(v_a_121_);
lean_dec_ref_known(v___x_120_, 1);
v___x_122_ = l_Lean_Meta_Grind_Order_mkUnsatProof(v_a_119_, v_a_121_, v_kuv_101_, v_huv_102_, v_kvu_103_, v_a_117_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, v_a_111_, v_a_112_, v_a_113_, v_a_114_);
if (lean_obj_tag(v___x_122_) == 0)
{
lean_object* v_a_123_; lean_object* v___x_124_; 
v_a_123_ = lean_ctor_get(v___x_122_, 0);
lean_inc(v_a_123_);
lean_dec_ref_known(v___x_122_, 1);
v___x_124_ = l_Lean_Meta_Grind_closeGoal(v_a_123_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, v_a_111_, v_a_112_, v_a_113_, v_a_114_);
return v___x_124_;
}
else
{
lean_object* v_a_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_132_; 
v_a_125_ = lean_ctor_get(v___x_122_, 0);
v_isSharedCheck_132_ = !lean_is_exclusive(v___x_122_);
if (v_isSharedCheck_132_ == 0)
{
v___x_127_ = v___x_122_;
v_isShared_128_ = v_isSharedCheck_132_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_a_125_);
lean_dec(v___x_122_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_132_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v___x_130_; 
if (v_isShared_128_ == 0)
{
v___x_130_ = v___x_127_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v_a_125_);
v___x_130_ = v_reuseFailAlloc_131_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
return v___x_130_;
}
}
}
}
else
{
lean_object* v_a_133_; lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_140_; 
lean_dec(v_a_119_);
lean_dec(v_a_117_);
lean_dec_ref(v_huv_102_);
v_a_133_ = lean_ctor_get(v___x_120_, 0);
v_isSharedCheck_140_ = !lean_is_exclusive(v___x_120_);
if (v_isSharedCheck_140_ == 0)
{
v___x_135_ = v___x_120_;
v_isShared_136_ = v_isSharedCheck_140_;
goto v_resetjp_134_;
}
else
{
lean_inc(v_a_133_);
lean_dec(v___x_120_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_140_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
lean_object* v___x_138_; 
if (v_isShared_136_ == 0)
{
v___x_138_ = v___x_135_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v_a_133_);
v___x_138_ = v_reuseFailAlloc_139_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
return v___x_138_;
}
}
}
}
else
{
lean_object* v_a_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_148_; 
lean_dec(v_a_117_);
lean_dec_ref(v_huv_102_);
v_a_141_ = lean_ctor_get(v___x_118_, 0);
v_isSharedCheck_148_ = !lean_is_exclusive(v___x_118_);
if (v_isSharedCheck_148_ == 0)
{
v___x_143_ = v___x_118_;
v_isShared_144_ = v_isSharedCheck_148_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_a_141_);
lean_dec(v___x_118_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_148_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v___x_146_; 
if (v_isShared_144_ == 0)
{
v___x_146_ = v___x_143_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v_a_141_);
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
lean_object* v_a_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_156_; 
lean_dec_ref(v_huv_102_);
v_a_149_ = lean_ctor_get(v___x_116_, 0);
v_isSharedCheck_156_ = !lean_is_exclusive(v___x_116_);
if (v_isSharedCheck_156_ == 0)
{
v___x_151_ = v___x_116_;
v_isShared_152_ = v_isSharedCheck_156_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_a_149_);
lean_dec(v___x_116_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_156_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v___x_154_; 
if (v_isShared_152_ == 0)
{
v___x_154_ = v___x_151_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v_a_149_);
v___x_154_ = v_reuseFailAlloc_155_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
return v___x_154_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setUnsat_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_99_ = stack[0].m_obj;
lean_object* v_v_100_ = stack[1].m_obj;
lean_object* v_kuv_101_ = stack[2].m_obj;
lean_object* v_huv_102_ = stack[3].m_obj;
lean_object* v_kvu_103_ = stack[4].m_obj;
lean_object* v_a_104_ = stack[5].m_obj;
lean_object* v_a_105_ = stack[6].m_obj;
lean_object* v_a_106_ = stack[7].m_obj;
lean_object* v_a_107_ = stack[8].m_obj;
lean_object* v_a_108_ = stack[9].m_obj;
lean_object* v_a_109_ = stack[10].m_obj;
lean_object* v_a_110_ = stack[11].m_obj;
lean_object* v_a_111_ = stack[12].m_obj;
lean_object* v_a_112_ = stack[13].m_obj;
lean_object* v_a_113_ = stack[14].m_obj;
lean_object* v_a_114_ = stack[15].m_obj;
lean_object* v_res_157_;
v_res_157_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setUnsat(v_u_99_, v_v_100_, v_kuv_101_, v_huv_102_, v_kvu_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_, v_a_110_, v_a_111_, v_a_112_, v_a_113_, v_a_114_);
stack->m_obj
 = v_res_157_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setUnsat___boxed(lean_object** _args){
lean_object* v_u_158_ = _args[0];
lean_object* v_v_159_ = _args[1];
lean_object* v_kuv_160_ = _args[2];
lean_object* v_huv_161_ = _args[3];
lean_object* v_kvu_162_ = _args[4];
lean_object* v_a_163_ = _args[5];
lean_object* v_a_164_ = _args[6];
lean_object* v_a_165_ = _args[7];
lean_object* v_a_166_ = _args[8];
lean_object* v_a_167_ = _args[9];
lean_object* v_a_168_ = _args[10];
lean_object* v_a_169_ = _args[11];
lean_object* v_a_170_ = _args[12];
lean_object* v_a_171_ = _args[13];
lean_object* v_a_172_ = _args[14];
lean_object* v_a_173_ = _args[15];
lean_object* v_a_174_ = _args[16];
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setUnsat(v_u_158_, v_v_159_, v_kuv_160_, v_huv_161_, v_kvu_162_, v_a_163_, v_a_164_, v_a_165_, v_a_166_, v_a_167_, v_a_168_, v_a_169_, v_a_170_, v_a_171_, v_a_172_, v_a_173_);
lean_dec(v_a_173_);
lean_dec_ref(v_a_172_);
lean_dec(v_a_171_);
lean_dec_ref(v_a_170_);
lean_dec(v_a_169_);
lean_dec_ref(v_a_168_);
lean_dec(v_a_167_);
lean_dec_ref(v_a_166_);
lean_dec(v_a_165_);
lean_dec(v_a_164_);
lean_dec(v_a_163_);
lean_dec_ref(v_kvu_162_);
lean_dec_ref(v_kuv_160_);
lean_dec(v_v_159_);
lean_dec(v_u_158_);
return v_res_175_;
}
}
uint8_t l_Lean_AssocList_contains___at___00Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0_spec__0___redArg(lean_object* v_a_176_, lean_object* v_x_177_){
_start:
{
if (lean_obj_tag(v_x_177_) == 0)
{
uint8_t v___x_178_; 
v___x_178_ = 0;
return v___x_178_;
}
else
{
lean_object* v_key_179_; lean_object* v_tail_180_; uint8_t v___x_181_; 
v_key_179_ = lean_ctor_get(v_x_177_, 0);
v_tail_180_ = lean_ctor_get(v_x_177_, 2);
v___x_181_ = lean_nat_dec_eq(v_key_179_, v_a_176_);
if (v___x_181_ == 0)
{
v_x_177_ = v_tail_180_;
goto _start;
}
else
{
return v___x_181_;
}
}
}
}
LEAN_EXPORT void l_Lean_AssocList_contains___at___00Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_176_ = stack[0].m_obj;
lean_object* v_x_177_ = stack[1].m_obj;
uint8_t v_res_183_;
v_res_183_ = l_Lean_AssocList_contains___at___00Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0_spec__0___redArg(v_a_176_, v_x_177_);
stack->m_num = v_res_183_;
}
LEAN_EXPORT lean_object* l_Lean_AssocList_contains___at___00Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0_spec__0___redArg___boxed(lean_object* v_a_184_, lean_object* v_x_185_){
_start:
{
uint8_t v_res_186_; lean_object* v_r_187_; 
v_res_186_ = l_Lean_AssocList_contains___at___00Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0_spec__0___redArg(v_a_184_, v_x_185_);
lean_dec(v_x_185_);
lean_dec(v_a_184_);
v_r_187_ = lean_box(v_res_186_);
return v_r_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_replace___at___00Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0_spec__1___redArg(lean_object* v_a_188_, lean_object* v_b_189_, lean_object* v_x_190_){
_start:
{
if (lean_obj_tag(v_x_190_) == 0)
{
lean_dec(v_b_189_);
lean_dec(v_a_188_);
return v_x_190_;
}
else
{
lean_object* v_key_191_; lean_object* v_value_192_; lean_object* v_tail_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_205_; 
v_key_191_ = lean_ctor_get(v_x_190_, 0);
v_value_192_ = lean_ctor_get(v_x_190_, 1);
v_tail_193_ = lean_ctor_get(v_x_190_, 2);
v_isSharedCheck_205_ = !lean_is_exclusive(v_x_190_);
if (v_isSharedCheck_205_ == 0)
{
v___x_195_ = v_x_190_;
v_isShared_196_ = v_isSharedCheck_205_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_tail_193_);
lean_inc(v_value_192_);
lean_inc(v_key_191_);
lean_dec(v_x_190_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_205_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
uint8_t v___x_197_; 
v___x_197_ = lean_nat_dec_eq(v_key_191_, v_a_188_);
if (v___x_197_ == 0)
{
lean_object* v___x_198_; lean_object* v___x_200_; 
v___x_198_ = l_Lean_AssocList_replace___at___00Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0_spec__1___redArg(v_a_188_, v_b_189_, v_tail_193_);
if (v_isShared_196_ == 0)
{
lean_ctor_set(v___x_195_, 2, v___x_198_);
v___x_200_ = v___x_195_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v_key_191_);
lean_ctor_set(v_reuseFailAlloc_201_, 1, v_value_192_);
lean_ctor_set(v_reuseFailAlloc_201_, 2, v___x_198_);
v___x_200_ = v_reuseFailAlloc_201_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
return v___x_200_;
}
}
else
{
lean_object* v___x_203_; 
lean_dec(v_value_192_);
lean_dec(v_key_191_);
if (v_isShared_196_ == 0)
{
lean_ctor_set(v___x_195_, 1, v_b_189_);
lean_ctor_set(v___x_195_, 0, v_a_188_);
v___x_203_ = v___x_195_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v_a_188_);
lean_ctor_set(v_reuseFailAlloc_204_, 1, v_b_189_);
lean_ctor_set(v_reuseFailAlloc_204_, 2, v_tail_193_);
v___x_203_ = v_reuseFailAlloc_204_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
return v___x_203_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0___redArg(lean_object* v_m_206_, lean_object* v_k_207_, lean_object* v_v_208_){
_start:
{
uint8_t v___x_209_; 
v___x_209_ = l_Lean_AssocList_contains___at___00Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0_spec__0___redArg(v_k_207_, v_m_206_);
if (v___x_209_ == 0)
{
lean_object* v___x_210_; 
v___x_210_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_210_, 0, v_k_207_);
lean_ctor_set(v___x_210_, 1, v_v_208_);
lean_ctor_set(v___x_210_, 2, v_m_206_);
return v___x_210_;
}
else
{
lean_object* v___x_211_; 
v___x_211_ = l_Lean_AssocList_replace___at___00Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0_spec__1___redArg(v_k_207_, v_v_208_, v_m_206_);
return v___x_211_;
}
}
}
lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1_spec__3(lean_object* v_u_212_, lean_object* v_k_213_, lean_object* v_x_214_, size_t v_x_215_, size_t v_x_216_){
_start:
{
if (lean_obj_tag(v_x_214_) == 0)
{
lean_object* v_cs_217_; size_t v_j_218_; lean_object* v___x_219_; lean_object* v___x_220_; uint8_t v___x_221_; 
v_cs_217_ = lean_ctor_get(v_x_214_, 0);
v_j_218_ = lean_usize_shift_right(v_x_215_, v_x_216_);
v___x_219_ = lean_usize_to_nat(v_j_218_);
v___x_220_ = lean_array_get_size(v_cs_217_);
v___x_221_ = lean_nat_dec_lt(v___x_219_, v___x_220_);
if (v___x_221_ == 0)
{
lean_dec(v___x_219_);
lean_dec_ref(v_k_213_);
lean_dec(v_u_212_);
return v_x_214_;
}
else
{
lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_239_; 
lean_inc_ref(v_cs_217_);
v_isSharedCheck_239_ = !lean_is_exclusive(v_x_214_);
if (v_isSharedCheck_239_ == 0)
{
lean_object* v_unused_240_; 
v_unused_240_ = lean_ctor_get(v_x_214_, 0);
lean_dec(v_unused_240_);
v___x_223_ = v_x_214_;
v_isShared_224_ = v_isSharedCheck_239_;
goto v_resetjp_222_;
}
else
{
lean_dec(v_x_214_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_239_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
size_t v___x_225_; size_t v___x_226_; size_t v___x_227_; size_t v_i_228_; size_t v___x_229_; size_t v_shift_230_; lean_object* v_v_231_; lean_object* v___x_232_; lean_object* v_xs_x27_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_237_; 
v___x_225_ = ((size_t)1ULL);
v___x_226_ = lean_usize_shift_left(v___x_225_, v_x_216_);
v___x_227_ = lean_usize_sub(v___x_226_, v___x_225_);
v_i_228_ = lean_usize_land(v_x_215_, v___x_227_);
v___x_229_ = ((size_t)5ULL);
v_shift_230_ = lean_usize_sub(v_x_216_, v___x_229_);
v_v_231_ = lean_array_fget(v_cs_217_, v___x_219_);
v___x_232_ = lean_box(0);
v_xs_x27_233_ = lean_array_fset(v_cs_217_, v___x_219_, v___x_232_);
v___x_234_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1_spec__3(v_u_212_, v_k_213_, v_v_231_, v_i_228_, v_shift_230_);
v___x_235_ = lean_array_fset(v_xs_x27_233_, v___x_219_, v___x_234_);
lean_dec(v___x_219_);
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 0, v___x_235_);
v___x_237_ = v___x_223_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v___x_235_);
v___x_237_ = v_reuseFailAlloc_238_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
return v___x_237_;
}
}
}
}
else
{
lean_object* v_vs_241_; lean_object* v___x_242_; lean_object* v___x_243_; uint8_t v___x_244_; 
v_vs_241_ = lean_ctor_get(v_x_214_, 0);
v___x_242_ = lean_usize_to_nat(v_x_215_);
v___x_243_ = lean_array_get_size(v_vs_241_);
v___x_244_ = lean_nat_dec_lt(v___x_242_, v___x_243_);
if (v___x_244_ == 0)
{
lean_dec(v___x_242_);
lean_dec_ref(v_k_213_);
lean_dec(v_u_212_);
return v_x_214_;
}
else
{
lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_256_; 
lean_inc_ref(v_vs_241_);
v_isSharedCheck_256_ = !lean_is_exclusive(v_x_214_);
if (v_isSharedCheck_256_ == 0)
{
lean_object* v_unused_257_; 
v_unused_257_ = lean_ctor_get(v_x_214_, 0);
lean_dec(v_unused_257_);
v___x_246_ = v_x_214_;
v_isShared_247_ = v_isSharedCheck_256_;
goto v_resetjp_245_;
}
else
{
lean_dec(v_x_214_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_256_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v_v_248_; lean_object* v___x_249_; lean_object* v_xs_x27_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_254_; 
v_v_248_ = lean_array_fget(v_vs_241_, v___x_242_);
v___x_249_ = lean_box(0);
v_xs_x27_250_ = lean_array_fset(v_vs_241_, v___x_242_, v___x_249_);
v___x_251_ = l_Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0___redArg(v_v_248_, v_u_212_, v_k_213_);
v___x_252_ = lean_array_fset(v_xs_x27_250_, v___x_242_, v___x_251_);
lean_dec(v___x_242_);
if (v_isShared_247_ == 0)
{
lean_ctor_set(v___x_246_, 0, v___x_252_);
v___x_254_ = v___x_246_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v___x_252_);
v___x_254_ = v_reuseFailAlloc_255_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
return v___x_254_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_212_ = stack[0].m_obj;
lean_object* v_k_213_ = stack[1].m_obj;
lean_object* v_x_214_ = stack[2].m_obj;
size_t v_x_215_ = stack[3].m_num;
size_t v_x_216_ = stack[4].m_num;
lean_object* v_res_258_;
v_res_258_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1_spec__3(v_u_212_, v_k_213_, v_x_214_, v_x_215_, v_x_216_);
stack->m_obj
 = v_res_258_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1_spec__3___boxed(lean_object* v_u_259_, lean_object* v_k_260_, lean_object* v_x_261_, lean_object* v_x_262_, lean_object* v_x_263_){
_start:
{
size_t v_x_307__boxed_264_; size_t v_x_308__boxed_265_; lean_object* v_res_266_; 
v_x_307__boxed_264_ = lean_unbox_usize(v_x_262_);
lean_dec(v_x_262_);
v_x_308__boxed_265_ = lean_unbox_usize(v_x_263_);
lean_dec(v_x_263_);
v_res_266_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1_spec__3(v_u_259_, v_k_260_, v_x_261_, v_x_307__boxed_264_, v_x_308__boxed_265_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1(lean_object* v_u_267_, lean_object* v_k_268_, lean_object* v_t_269_, lean_object* v_i_270_){
_start:
{
lean_object* v_root_271_; lean_object* v_tail_272_; lean_object* v_size_273_; size_t v_shift_274_; lean_object* v_tailOff_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_299_; 
v_root_271_ = lean_ctor_get(v_t_269_, 0);
v_tail_272_ = lean_ctor_get(v_t_269_, 1);
v_size_273_ = lean_ctor_get(v_t_269_, 2);
v_shift_274_ = lean_ctor_get_usize(v_t_269_, 4);
v_tailOff_275_ = lean_ctor_get(v_t_269_, 3);
v_isSharedCheck_299_ = !lean_is_exclusive(v_t_269_);
if (v_isSharedCheck_299_ == 0)
{
v___x_277_ = v_t_269_;
v_isShared_278_ = v_isSharedCheck_299_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_tailOff_275_);
lean_inc(v_size_273_);
lean_inc(v_tail_272_);
lean_inc(v_root_271_);
lean_dec(v_t_269_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_299_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
uint8_t v___x_279_; 
v___x_279_ = lean_nat_dec_le(v_tailOff_275_, v_i_270_);
if (v___x_279_ == 0)
{
size_t v___x_280_; lean_object* v___x_281_; lean_object* v___x_283_; 
v___x_280_ = lean_usize_of_nat(v_i_270_);
v___x_281_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1_spec__3(v_u_267_, v_k_268_, v_root_271_, v___x_280_, v_shift_274_);
if (v_isShared_278_ == 0)
{
lean_ctor_set(v___x_277_, 0, v___x_281_);
v___x_283_ = v___x_277_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v___x_281_);
lean_ctor_set(v_reuseFailAlloc_284_, 1, v_tail_272_);
lean_ctor_set(v_reuseFailAlloc_284_, 2, v_size_273_);
lean_ctor_set(v_reuseFailAlloc_284_, 3, v_tailOff_275_);
lean_ctor_set_usize(v_reuseFailAlloc_284_, 4, v_shift_274_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
else
{
lean_object* v___x_285_; lean_object* v___x_286_; uint8_t v___x_287_; 
v___x_285_ = lean_nat_sub(v_i_270_, v_tailOff_275_);
v___x_286_ = lean_array_get_size(v_tail_272_);
v___x_287_ = lean_nat_dec_lt(v___x_285_, v___x_286_);
if (v___x_287_ == 0)
{
lean_object* v___x_289_; 
lean_dec(v___x_285_);
lean_dec_ref(v_k_268_);
lean_dec(v_u_267_);
if (v_isShared_278_ == 0)
{
v___x_289_ = v___x_277_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v_root_271_);
lean_ctor_set(v_reuseFailAlloc_290_, 1, v_tail_272_);
lean_ctor_set(v_reuseFailAlloc_290_, 2, v_size_273_);
lean_ctor_set(v_reuseFailAlloc_290_, 3, v_tailOff_275_);
lean_ctor_set_usize(v_reuseFailAlloc_290_, 4, v_shift_274_);
v___x_289_ = v_reuseFailAlloc_290_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
return v___x_289_;
}
}
else
{
lean_object* v_v_291_; lean_object* v___x_292_; lean_object* v_xs_x27_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_297_; 
v_v_291_ = lean_array_fget(v_tail_272_, v___x_285_);
v___x_292_ = lean_box(0);
v_xs_x27_293_ = lean_array_fset(v_tail_272_, v___x_285_, v___x_292_);
v___x_294_ = l_Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0___redArg(v_v_291_, v_u_267_, v_k_268_);
v___x_295_ = lean_array_fset(v_xs_x27_293_, v___x_285_, v___x_294_);
lean_dec(v___x_285_);
if (v_isShared_278_ == 0)
{
lean_ctor_set(v___x_277_, 1, v___x_295_);
v___x_297_ = v___x_277_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v_root_271_);
lean_ctor_set(v_reuseFailAlloc_298_, 1, v___x_295_);
lean_ctor_set(v_reuseFailAlloc_298_, 2, v_size_273_);
lean_ctor_set(v_reuseFailAlloc_298_, 3, v_tailOff_275_);
lean_ctor_set_usize(v_reuseFailAlloc_298_, 4, v_shift_274_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1___boxed(lean_object* v_u_300_, lean_object* v_k_301_, lean_object* v_t_302_, lean_object* v_i_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1(v_u_300_, v_k_301_, v_t_302_, v_i_303_);
lean_dec(v_i_303_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist___redArg___lam__0(lean_object* v_u_305_, lean_object* v_k_306_, lean_object* v_v_307_, lean_object* v_s_308_){
_start:
{
lean_object* v_id_309_; lean_object* v_nodes_310_; lean_object* v_nodeMap_311_; lean_object* v_cnstrs_312_; lean_object* v_cnstrsOf_313_; lean_object* v_sources_314_; lean_object* v_targets_315_; lean_object* v_proofs_316_; lean_object* v_propagate_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_326_; 
v_id_309_ = lean_ctor_get(v_s_308_, 0);
v_nodes_310_ = lean_ctor_get(v_s_308_, 1);
v_nodeMap_311_ = lean_ctor_get(v_s_308_, 2);
v_cnstrs_312_ = lean_ctor_get(v_s_308_, 3);
v_cnstrsOf_313_ = lean_ctor_get(v_s_308_, 4);
v_sources_314_ = lean_ctor_get(v_s_308_, 5);
v_targets_315_ = lean_ctor_get(v_s_308_, 6);
v_proofs_316_ = lean_ctor_get(v_s_308_, 7);
v_propagate_317_ = lean_ctor_get(v_s_308_, 8);
v_isSharedCheck_326_ = !lean_is_exclusive(v_s_308_);
if (v_isSharedCheck_326_ == 0)
{
v___x_319_ = v_s_308_;
v_isShared_320_ = v_isSharedCheck_326_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_propagate_317_);
lean_inc(v_proofs_316_);
lean_inc(v_targets_315_);
lean_inc(v_sources_314_);
lean_inc(v_cnstrsOf_313_);
lean_inc(v_cnstrs_312_);
lean_inc(v_nodeMap_311_);
lean_inc(v_nodes_310_);
lean_inc(v_id_309_);
lean_dec(v_s_308_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_326_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_324_; 
lean_inc_ref(v_k_306_);
lean_inc(v_u_305_);
v___x_321_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1(v_u_305_, v_k_306_, v_sources_314_, v_v_307_);
v___x_322_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1(v_v_307_, v_k_306_, v_targets_315_, v_u_305_);
lean_dec(v_u_305_);
if (v_isShared_320_ == 0)
{
lean_ctor_set(v___x_319_, 6, v___x_322_);
lean_ctor_set(v___x_319_, 5, v___x_321_);
v___x_324_ = v___x_319_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v_id_309_);
lean_ctor_set(v_reuseFailAlloc_325_, 1, v_nodes_310_);
lean_ctor_set(v_reuseFailAlloc_325_, 2, v_nodeMap_311_);
lean_ctor_set(v_reuseFailAlloc_325_, 3, v_cnstrs_312_);
lean_ctor_set(v_reuseFailAlloc_325_, 4, v_cnstrsOf_313_);
lean_ctor_set(v_reuseFailAlloc_325_, 5, v___x_321_);
lean_ctor_set(v_reuseFailAlloc_325_, 6, v___x_322_);
lean_ctor_set(v_reuseFailAlloc_325_, 7, v_proofs_316_);
lean_ctor_set(v_reuseFailAlloc_325_, 8, v_propagate_317_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
return v___x_324_;
}
}
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist___redArg(lean_object* v_u_327_, lean_object* v_v_328_, lean_object* v_k_329_, lean_object* v_a_330_, lean_object* v_a_331_){
_start:
{
lean_object* v___f_333_; lean_object* v___x_334_; 
v___f_333_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist___redArg___lam__0), 4, 3);
lean_closure_set(v___f_333_, 0, v_u_327_);
lean_closure_set(v___f_333_, 1, v_k_329_);
lean_closure_set(v___f_333_, 2, v_v_328_);
v___x_334_ = l_Lean_Meta_Grind_Order_modifyStruct___redArg(v___f_333_, v_a_330_, v_a_331_);
return v___x_334_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_327_ = stack[0].m_obj;
lean_object* v_v_328_ = stack[1].m_obj;
lean_object* v_k_329_ = stack[2].m_obj;
lean_object* v_a_330_ = stack[3].m_obj;
lean_object* v_a_331_ = stack[4].m_obj;
lean_object* v_res_335_;
v_res_335_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist___redArg(v_u_327_, v_v_328_, v_k_329_, v_a_330_, v_a_331_);
stack->m_obj
 = v_res_335_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist___redArg___boxed(lean_object* v_u_336_, lean_object* v_v_337_, lean_object* v_k_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist___redArg(v_u_336_, v_v_337_, v_k_338_, v_a_339_, v_a_340_);
lean_dec(v_a_340_);
lean_dec(v_a_339_);
return v_res_342_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist(lean_object* v_u_343_, lean_object* v_v_344_, lean_object* v_k_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_){
_start:
{
lean_object* v___x_358_; 
v___x_358_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist___redArg(v_u_343_, v_v_344_, v_k_345_, v_a_346_, v_a_347_);
return v___x_358_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_343_ = stack[0].m_obj;
lean_object* v_v_344_ = stack[1].m_obj;
lean_object* v_k_345_ = stack[2].m_obj;
lean_object* v_a_346_ = stack[3].m_obj;
lean_object* v_a_347_ = stack[4].m_obj;
lean_object* v_a_348_ = stack[5].m_obj;
lean_object* v_a_349_ = stack[6].m_obj;
lean_object* v_a_350_ = stack[7].m_obj;
lean_object* v_a_351_ = stack[8].m_obj;
lean_object* v_a_352_ = stack[9].m_obj;
lean_object* v_a_353_ = stack[10].m_obj;
lean_object* v_a_354_ = stack[11].m_obj;
lean_object* v_a_355_ = stack[12].m_obj;
lean_object* v_a_356_ = stack[13].m_obj;
lean_object* v_res_359_;
v_res_359_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist(v_u_343_, v_v_344_, v_k_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_, v_a_355_, v_a_356_);
stack->m_obj
 = v_res_359_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist___boxed(lean_object* v_u_360_, lean_object* v_v_361_, lean_object* v_k_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist(v_u_360_, v_v_361_, v_k_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_, v_a_371_, v_a_372_, v_a_373_);
lean_dec(v_a_373_);
lean_dec_ref(v_a_372_);
lean_dec(v_a_371_);
lean_dec_ref(v_a_370_);
lean_dec(v_a_369_);
lean_dec_ref(v_a_368_);
lean_dec(v_a_367_);
lean_dec_ref(v_a_366_);
lean_dec(v_a_365_);
lean_dec(v_a_364_);
lean_dec(v_a_363_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0(lean_object* v_00_u03b2_376_, lean_object* v_m_377_, lean_object* v_k_378_, lean_object* v_v_379_){
_start:
{
lean_object* v___x_380_; 
v___x_380_ = l_Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0___redArg(v_m_377_, v_k_378_, v_v_379_);
return v___x_380_;
}
}
uint8_t l_Lean_AssocList_contains___at___00Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0_spec__0(lean_object* v_00_u03b2_381_, lean_object* v_a_382_, lean_object* v_x_383_){
_start:
{
uint8_t v___x_384_; 
v___x_384_ = l_Lean_AssocList_contains___at___00Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0_spec__0___redArg(v_a_382_, v_x_383_);
return v___x_384_;
}
}
LEAN_EXPORT void l_Lean_AssocList_contains___at___00Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_382_ = stack[1].m_obj;
lean_object* v_x_383_ = stack[2].m_obj;
uint8_t v_res_385_;
v_res_385_ = l_Lean_AssocList_contains___at___00Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0_spec__0(lean_box(0), v_a_382_, v_x_383_);
stack->m_num = v_res_385_;
}
LEAN_EXPORT lean_object* l_Lean_AssocList_contains___at___00Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0_spec__0___boxed(lean_object* v_00_u03b2_386_, lean_object* v_a_387_, lean_object* v_x_388_){
_start:
{
uint8_t v_res_389_; lean_object* v_r_390_; 
v_res_389_ = l_Lean_AssocList_contains___at___00Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0_spec__0(v_00_u03b2_386_, v_a_387_, v_x_388_);
lean_dec(v_x_388_);
lean_dec(v_a_387_);
v_r_390_ = lean_box(v_res_389_);
return v_r_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_replace___at___00Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0_spec__1(lean_object* v_00_u03b2_391_, lean_object* v_a_392_, lean_object* v_b_393_, lean_object* v_x_394_){
_start:
{
lean_object* v___x_395_; 
v___x_395_ = l_Lean_AssocList_replace___at___00Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0_spec__1___redArg(v_a_392_, v_b_393_, v_x_394_);
return v___x_395_;
}
}
lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof_spec__0_spec__0(lean_object* v_v_396_, lean_object* v_p_397_, lean_object* v_x_398_, size_t v_x_399_, size_t v_x_400_){
_start:
{
if (lean_obj_tag(v_x_398_) == 0)
{
lean_object* v_cs_401_; size_t v_j_402_; lean_object* v___x_403_; lean_object* v___x_404_; uint8_t v___x_405_; 
v_cs_401_ = lean_ctor_get(v_x_398_, 0);
v_j_402_ = lean_usize_shift_right(v_x_399_, v_x_400_);
v___x_403_ = lean_usize_to_nat(v_j_402_);
v___x_404_ = lean_array_get_size(v_cs_401_);
v___x_405_ = lean_nat_dec_lt(v___x_403_, v___x_404_);
if (v___x_405_ == 0)
{
lean_dec(v___x_403_);
lean_dec_ref(v_p_397_);
lean_dec(v_v_396_);
return v_x_398_;
}
else
{
lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_423_; 
lean_inc_ref(v_cs_401_);
v_isSharedCheck_423_ = !lean_is_exclusive(v_x_398_);
if (v_isSharedCheck_423_ == 0)
{
lean_object* v_unused_424_; 
v_unused_424_ = lean_ctor_get(v_x_398_, 0);
lean_dec(v_unused_424_);
v___x_407_ = v_x_398_;
v_isShared_408_ = v_isSharedCheck_423_;
goto v_resetjp_406_;
}
else
{
lean_dec(v_x_398_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_423_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
size_t v___x_409_; size_t v___x_410_; size_t v___x_411_; size_t v_i_412_; size_t v___x_413_; size_t v_shift_414_; lean_object* v_v_415_; lean_object* v___x_416_; lean_object* v_xs_x27_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_421_; 
v___x_409_ = ((size_t)1ULL);
v___x_410_ = lean_usize_shift_left(v___x_409_, v_x_400_);
v___x_411_ = lean_usize_sub(v___x_410_, v___x_409_);
v_i_412_ = lean_usize_land(v_x_399_, v___x_411_);
v___x_413_ = ((size_t)5ULL);
v_shift_414_ = lean_usize_sub(v_x_400_, v___x_413_);
v_v_415_ = lean_array_fget(v_cs_401_, v___x_403_);
v___x_416_ = lean_box(0);
v_xs_x27_417_ = lean_array_fset(v_cs_401_, v___x_403_, v___x_416_);
v___x_418_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof_spec__0_spec__0(v_v_396_, v_p_397_, v_v_415_, v_i_412_, v_shift_414_);
v___x_419_ = lean_array_fset(v_xs_x27_417_, v___x_403_, v___x_418_);
lean_dec(v___x_403_);
if (v_isShared_408_ == 0)
{
lean_ctor_set(v___x_407_, 0, v___x_419_);
v___x_421_ = v___x_407_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v___x_419_);
v___x_421_ = v_reuseFailAlloc_422_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
return v___x_421_;
}
}
}
}
else
{
lean_object* v_vs_425_; lean_object* v___x_426_; lean_object* v___x_427_; uint8_t v___x_428_; 
v_vs_425_ = lean_ctor_get(v_x_398_, 0);
v___x_426_ = lean_usize_to_nat(v_x_399_);
v___x_427_ = lean_array_get_size(v_vs_425_);
v___x_428_ = lean_nat_dec_lt(v___x_426_, v___x_427_);
if (v___x_428_ == 0)
{
lean_dec(v___x_426_);
lean_dec_ref(v_p_397_);
lean_dec(v_v_396_);
return v_x_398_;
}
else
{
lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_440_; 
lean_inc_ref(v_vs_425_);
v_isSharedCheck_440_ = !lean_is_exclusive(v_x_398_);
if (v_isSharedCheck_440_ == 0)
{
lean_object* v_unused_441_; 
v_unused_441_ = lean_ctor_get(v_x_398_, 0);
lean_dec(v_unused_441_);
v___x_430_ = v_x_398_;
v_isShared_431_ = v_isSharedCheck_440_;
goto v_resetjp_429_;
}
else
{
lean_dec(v_x_398_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_440_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v_v_432_; lean_object* v___x_433_; lean_object* v_xs_x27_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_438_; 
v_v_432_ = lean_array_fget(v_vs_425_, v___x_426_);
v___x_433_ = lean_box(0);
v_xs_x27_434_ = lean_array_fset(v_vs_425_, v___x_426_, v___x_433_);
v___x_435_ = l_Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0___redArg(v_v_432_, v_v_396_, v_p_397_);
v___x_436_ = lean_array_fset(v_xs_x27_434_, v___x_426_, v___x_435_);
lean_dec(v___x_426_);
if (v_isShared_431_ == 0)
{
lean_ctor_set(v___x_430_, 0, v___x_436_);
v___x_438_ = v___x_430_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v___x_436_);
v___x_438_ = v_reuseFailAlloc_439_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
return v___x_438_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_v_396_ = stack[0].m_obj;
lean_object* v_p_397_ = stack[1].m_obj;
lean_object* v_x_398_ = stack[2].m_obj;
size_t v_x_399_ = stack[3].m_num;
size_t v_x_400_ = stack[4].m_num;
lean_object* v_res_442_;
v_res_442_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof_spec__0_spec__0(v_v_396_, v_p_397_, v_x_398_, v_x_399_, v_x_400_);
stack->m_obj
 = v_res_442_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof_spec__0_spec__0___boxed(lean_object* v_v_443_, lean_object* v_p_444_, lean_object* v_x_445_, lean_object* v_x_446_, lean_object* v_x_447_){
_start:
{
size_t v_x_141__boxed_448_; size_t v_x_142__boxed_449_; lean_object* v_res_450_; 
v_x_141__boxed_448_ = lean_unbox_usize(v_x_446_);
lean_dec(v_x_446_);
v_x_142__boxed_449_ = lean_unbox_usize(v_x_447_);
lean_dec(v_x_447_);
v_res_450_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof_spec__0_spec__0(v_v_443_, v_p_444_, v_x_445_, v_x_141__boxed_448_, v_x_142__boxed_449_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof_spec__0(lean_object* v_v_451_, lean_object* v_p_452_, lean_object* v_t_453_, lean_object* v_i_454_){
_start:
{
lean_object* v_root_455_; lean_object* v_tail_456_; lean_object* v_size_457_; size_t v_shift_458_; lean_object* v_tailOff_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_483_; 
v_root_455_ = lean_ctor_get(v_t_453_, 0);
v_tail_456_ = lean_ctor_get(v_t_453_, 1);
v_size_457_ = lean_ctor_get(v_t_453_, 2);
v_shift_458_ = lean_ctor_get_usize(v_t_453_, 4);
v_tailOff_459_ = lean_ctor_get(v_t_453_, 3);
v_isSharedCheck_483_ = !lean_is_exclusive(v_t_453_);
if (v_isSharedCheck_483_ == 0)
{
v___x_461_ = v_t_453_;
v_isShared_462_ = v_isSharedCheck_483_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_tailOff_459_);
lean_inc(v_size_457_);
lean_inc(v_tail_456_);
lean_inc(v_root_455_);
lean_dec(v_t_453_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_483_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
uint8_t v___x_463_; 
v___x_463_ = lean_nat_dec_le(v_tailOff_459_, v_i_454_);
if (v___x_463_ == 0)
{
size_t v___x_464_; lean_object* v___x_465_; lean_object* v___x_467_; 
v___x_464_ = lean_usize_of_nat(v_i_454_);
v___x_465_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof_spec__0_spec__0(v_v_451_, v_p_452_, v_root_455_, v___x_464_, v_shift_458_);
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 0, v___x_465_);
v___x_467_ = v___x_461_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v___x_465_);
lean_ctor_set(v_reuseFailAlloc_468_, 1, v_tail_456_);
lean_ctor_set(v_reuseFailAlloc_468_, 2, v_size_457_);
lean_ctor_set(v_reuseFailAlloc_468_, 3, v_tailOff_459_);
lean_ctor_set_usize(v_reuseFailAlloc_468_, 4, v_shift_458_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
}
}
else
{
lean_object* v___x_469_; lean_object* v___x_470_; uint8_t v___x_471_; 
v___x_469_ = lean_nat_sub(v_i_454_, v_tailOff_459_);
v___x_470_ = lean_array_get_size(v_tail_456_);
v___x_471_ = lean_nat_dec_lt(v___x_469_, v___x_470_);
if (v___x_471_ == 0)
{
lean_object* v___x_473_; 
lean_dec(v___x_469_);
lean_dec_ref(v_p_452_);
lean_dec(v_v_451_);
if (v_isShared_462_ == 0)
{
v___x_473_ = v___x_461_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v_root_455_);
lean_ctor_set(v_reuseFailAlloc_474_, 1, v_tail_456_);
lean_ctor_set(v_reuseFailAlloc_474_, 2, v_size_457_);
lean_ctor_set(v_reuseFailAlloc_474_, 3, v_tailOff_459_);
lean_ctor_set_usize(v_reuseFailAlloc_474_, 4, v_shift_458_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
else
{
lean_object* v_v_475_; lean_object* v___x_476_; lean_object* v_xs_x27_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_481_; 
v_v_475_ = lean_array_fget(v_tail_456_, v___x_469_);
v___x_476_ = lean_box(0);
v_xs_x27_477_ = lean_array_fset(v_tail_456_, v___x_469_, v___x_476_);
v___x_478_ = l_Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0___redArg(v_v_475_, v_v_451_, v_p_452_);
v___x_479_ = lean_array_fset(v_xs_x27_477_, v___x_469_, v___x_478_);
lean_dec(v___x_469_);
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 1, v___x_479_);
v___x_481_ = v___x_461_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v_root_455_);
lean_ctor_set(v_reuseFailAlloc_482_, 1, v___x_479_);
lean_ctor_set(v_reuseFailAlloc_482_, 2, v_size_457_);
lean_ctor_set(v_reuseFailAlloc_482_, 3, v_tailOff_459_);
lean_ctor_set_usize(v_reuseFailAlloc_482_, 4, v_shift_458_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof_spec__0___boxed(lean_object* v_v_484_, lean_object* v_p_485_, lean_object* v_t_486_, lean_object* v_i_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof_spec__0(v_v_484_, v_p_485_, v_t_486_, v_i_487_);
lean_dec(v_i_487_);
return v_res_488_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___redArg___lam__0(lean_object* v_v_489_, lean_object* v_p_490_, lean_object* v_u_491_, lean_object* v_s_492_){
_start:
{
lean_object* v_id_493_; lean_object* v_nodes_494_; lean_object* v_nodeMap_495_; lean_object* v_cnstrs_496_; lean_object* v_cnstrsOf_497_; lean_object* v_sources_498_; lean_object* v_targets_499_; lean_object* v_proofs_500_; lean_object* v_propagate_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_509_; 
v_id_493_ = lean_ctor_get(v_s_492_, 0);
v_nodes_494_ = lean_ctor_get(v_s_492_, 1);
v_nodeMap_495_ = lean_ctor_get(v_s_492_, 2);
v_cnstrs_496_ = lean_ctor_get(v_s_492_, 3);
v_cnstrsOf_497_ = lean_ctor_get(v_s_492_, 4);
v_sources_498_ = lean_ctor_get(v_s_492_, 5);
v_targets_499_ = lean_ctor_get(v_s_492_, 6);
v_proofs_500_ = lean_ctor_get(v_s_492_, 7);
v_propagate_501_ = lean_ctor_get(v_s_492_, 8);
v_isSharedCheck_509_ = !lean_is_exclusive(v_s_492_);
if (v_isSharedCheck_509_ == 0)
{
v___x_503_ = v_s_492_;
v_isShared_504_ = v_isSharedCheck_509_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_propagate_501_);
lean_inc(v_proofs_500_);
lean_inc(v_targets_499_);
lean_inc(v_sources_498_);
lean_inc(v_cnstrsOf_497_);
lean_inc(v_cnstrs_496_);
lean_inc(v_nodeMap_495_);
lean_inc(v_nodes_494_);
lean_inc(v_id_493_);
lean_dec(v_s_492_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_509_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_505_; lean_object* v___x_507_; 
v___x_505_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof_spec__0(v_v_489_, v_p_490_, v_proofs_500_, v_u_491_);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 7, v___x_505_);
v___x_507_ = v___x_503_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v_id_493_);
lean_ctor_set(v_reuseFailAlloc_508_, 1, v_nodes_494_);
lean_ctor_set(v_reuseFailAlloc_508_, 2, v_nodeMap_495_);
lean_ctor_set(v_reuseFailAlloc_508_, 3, v_cnstrs_496_);
lean_ctor_set(v_reuseFailAlloc_508_, 4, v_cnstrsOf_497_);
lean_ctor_set(v_reuseFailAlloc_508_, 5, v_sources_498_);
lean_ctor_set(v_reuseFailAlloc_508_, 6, v_targets_499_);
lean_ctor_set(v_reuseFailAlloc_508_, 7, v___x_505_);
lean_ctor_set(v_reuseFailAlloc_508_, 8, v_propagate_501_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
return v___x_507_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___redArg___lam__0___boxed(lean_object* v_v_510_, lean_object* v_p_511_, lean_object* v_u_512_, lean_object* v_s_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___redArg___lam__0(v_v_510_, v_p_511_, v_u_512_, v_s_513_);
lean_dec(v_u_512_);
return v_res_514_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___redArg(lean_object* v_u_515_, lean_object* v_v_516_, lean_object* v_p_517_, lean_object* v_a_518_, lean_object* v_a_519_){
_start:
{
lean_object* v___f_521_; lean_object* v___x_522_; 
v___f_521_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_521_, 0, v_v_516_);
lean_closure_set(v___f_521_, 1, v_p_517_);
lean_closure_set(v___f_521_, 2, v_u_515_);
v___x_522_ = l_Lean_Meta_Grind_Order_modifyStruct___redArg(v___f_521_, v_a_518_, v_a_519_);
return v___x_522_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_515_ = stack[0].m_obj;
lean_object* v_v_516_ = stack[1].m_obj;
lean_object* v_p_517_ = stack[2].m_obj;
lean_object* v_a_518_ = stack[3].m_obj;
lean_object* v_a_519_ = stack[4].m_obj;
lean_object* v_res_523_;
v_res_523_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___redArg(v_u_515_, v_v_516_, v_p_517_, v_a_518_, v_a_519_);
stack->m_obj
 = v_res_523_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___redArg___boxed(lean_object* v_u_524_, lean_object* v_v_525_, lean_object* v_p_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___redArg(v_u_524_, v_v_525_, v_p_526_, v_a_527_, v_a_528_);
lean_dec(v_a_528_);
lean_dec(v_a_527_);
return v_res_530_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof(lean_object* v_u_531_, lean_object* v_v_532_, lean_object* v_p_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_){
_start:
{
lean_object* v___x_546_; 
v___x_546_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___redArg(v_u_531_, v_v_532_, v_p_533_, v_a_534_, v_a_535_);
return v___x_546_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_531_ = stack[0].m_obj;
lean_object* v_v_532_ = stack[1].m_obj;
lean_object* v_p_533_ = stack[2].m_obj;
lean_object* v_a_534_ = stack[3].m_obj;
lean_object* v_a_535_ = stack[4].m_obj;
lean_object* v_a_536_ = stack[5].m_obj;
lean_object* v_a_537_ = stack[6].m_obj;
lean_object* v_a_538_ = stack[7].m_obj;
lean_object* v_a_539_ = stack[8].m_obj;
lean_object* v_a_540_ = stack[9].m_obj;
lean_object* v_a_541_ = stack[10].m_obj;
lean_object* v_a_542_ = stack[11].m_obj;
lean_object* v_a_543_ = stack[12].m_obj;
lean_object* v_a_544_ = stack[13].m_obj;
lean_object* v_res_547_;
v_res_547_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof(v_u_531_, v_v_532_, v_p_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_, v_a_540_, v_a_541_, v_a_542_, v_a_543_, v_a_544_);
stack->m_obj
 = v_res_547_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___boxed(lean_object* v_u_548_, lean_object* v_v_549_, lean_object* v_p_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof(v_u_548_, v_v_549_, v_p_550_, v_a_551_, v_a_552_, v_a_553_, v_a_554_, v_a_555_, v_a_556_, v_a_557_, v_a_558_, v_a_559_, v_a_560_, v_a_561_);
lean_dec(v_a_561_);
lean_dec_ref(v_a_560_);
lean_dec(v_a_559_);
lean_dec_ref(v_a_558_);
lean_dec(v_a_557_);
lean_dec_ref(v_a_556_);
lean_dec(v_a_555_);
lean_dec_ref(v_a_554_);
lean_dec(v_a_553_);
lean_dec(v_a_552_);
lean_dec(v_a_551_);
return v_res_563_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__0(void){
_start:
{
lean_object* v___x_564_; 
v___x_564_ = l_instMonadEIO___redArg();
return v___x_564_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__1(void){
_start:
{
lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_565_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__0, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__0);
v___x_566_ = l_StateRefT_x27_instMonad___redArg(v___x_565_);
return v___x_566_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf(lean_object* v_u_571_, lean_object* v_f_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_){
_start:
{
lean_object* v___x_585_; lean_object* v_toApplicative_586_; lean_object* v_toFunctor_587_; lean_object* v_toSeq_588_; lean_object* v_toSeqLeft_589_; lean_object* v_toSeqRight_590_; lean_object* v___f_591_; lean_object* v___f_592_; lean_object* v___f_593_; lean_object* v___f_594_; lean_object* v___x_595_; lean_object* v___f_596_; lean_object* v___f_597_; lean_object* v___f_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v_toApplicative_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_656_; 
v___x_585_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__1, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__1);
v_toApplicative_586_ = lean_ctor_get(v___x_585_, 0);
v_toFunctor_587_ = lean_ctor_get(v_toApplicative_586_, 0);
v_toSeq_588_ = lean_ctor_get(v_toApplicative_586_, 2);
v_toSeqLeft_589_ = lean_ctor_get(v_toApplicative_586_, 3);
v_toSeqRight_590_ = lean_ctor_get(v_toApplicative_586_, 4);
v___f_591_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__2));
v___f_592_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__3));
lean_inc_ref_n(v_toFunctor_587_, 2);
v___f_593_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_593_, 0, v_toFunctor_587_);
v___f_594_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_594_, 0, v_toFunctor_587_);
v___x_595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_595_, 0, v___f_593_);
lean_ctor_set(v___x_595_, 1, v___f_594_);
lean_inc(v_toSeqRight_590_);
v___f_596_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_596_, 0, v_toSeqRight_590_);
lean_inc(v_toSeqLeft_589_);
v___f_597_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_597_, 0, v_toSeqLeft_589_);
lean_inc(v_toSeq_588_);
v___f_598_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_598_, 0, v_toSeq_588_);
v___x_599_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_599_, 0, v___x_595_);
lean_ctor_set(v___x_599_, 1, v___f_591_);
lean_ctor_set(v___x_599_, 2, v___f_598_);
lean_ctor_set(v___x_599_, 3, v___f_597_);
lean_ctor_set(v___x_599_, 4, v___f_596_);
v___x_600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_600_, 0, v___x_599_);
lean_ctor_set(v___x_600_, 1, v___f_592_);
v___x_601_ = l_StateRefT_x27_instMonad___redArg(v___x_600_);
v_toApplicative_602_ = lean_ctor_get(v___x_601_, 0);
v_isSharedCheck_656_ = !lean_is_exclusive(v___x_601_);
if (v_isSharedCheck_656_ == 0)
{
lean_object* v_unused_657_; 
v_unused_657_ = lean_ctor_get(v___x_601_, 1);
lean_dec(v_unused_657_);
v___x_604_ = v___x_601_;
v_isShared_605_ = v_isSharedCheck_656_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_toApplicative_602_);
lean_dec(v___x_601_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_656_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v_toFunctor_606_; lean_object* v_toSeq_607_; lean_object* v_toSeqLeft_608_; lean_object* v_toSeqRight_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_654_; 
v_toFunctor_606_ = lean_ctor_get(v_toApplicative_602_, 0);
v_toSeq_607_ = lean_ctor_get(v_toApplicative_602_, 2);
v_toSeqLeft_608_ = lean_ctor_get(v_toApplicative_602_, 3);
v_toSeqRight_609_ = lean_ctor_get(v_toApplicative_602_, 4);
v_isSharedCheck_654_ = !lean_is_exclusive(v_toApplicative_602_);
if (v_isSharedCheck_654_ == 0)
{
lean_object* v_unused_655_; 
v_unused_655_ = lean_ctor_get(v_toApplicative_602_, 1);
lean_dec(v_unused_655_);
v___x_611_ = v_toApplicative_602_;
v_isShared_612_ = v_isSharedCheck_654_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_toSeqRight_609_);
lean_inc(v_toSeqLeft_608_);
lean_inc(v_toSeq_607_);
lean_inc(v_toFunctor_606_);
lean_dec(v_toApplicative_602_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_654_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___f_613_; lean_object* v___f_614_; lean_object* v___f_615_; lean_object* v___f_616_; lean_object* v___x_617_; lean_object* v___f_618_; lean_object* v___f_619_; lean_object* v___f_620_; lean_object* v___x_622_; 
v___f_613_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__4));
v___f_614_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__5));
lean_inc_ref(v_toFunctor_606_);
v___f_615_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_615_, 0, v_toFunctor_606_);
v___f_616_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_616_, 0, v_toFunctor_606_);
v___x_617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_617_, 0, v___f_615_);
lean_ctor_set(v___x_617_, 1, v___f_616_);
v___f_618_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_618_, 0, v_toSeqRight_609_);
v___f_619_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_619_, 0, v_toSeqLeft_608_);
v___f_620_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_620_, 0, v_toSeq_607_);
if (v_isShared_612_ == 0)
{
lean_ctor_set(v___x_611_, 4, v___f_618_);
lean_ctor_set(v___x_611_, 3, v___f_619_);
lean_ctor_set(v___x_611_, 2, v___f_620_);
lean_ctor_set(v___x_611_, 1, v___f_613_);
lean_ctor_set(v___x_611_, 0, v___x_617_);
v___x_622_ = v___x_611_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v___x_617_);
lean_ctor_set(v_reuseFailAlloc_653_, 1, v___f_613_);
lean_ctor_set(v_reuseFailAlloc_653_, 2, v___f_620_);
lean_ctor_set(v_reuseFailAlloc_653_, 3, v___f_619_);
lean_ctor_set(v_reuseFailAlloc_653_, 4, v___f_618_);
v___x_622_ = v_reuseFailAlloc_653_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
lean_object* v___x_624_; 
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 1, v___f_614_);
lean_ctor_set(v___x_604_, 0, v___x_622_);
v___x_624_ = v___x_604_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v___x_622_);
lean_ctor_set(v_reuseFailAlloc_652_, 1, v___f_614_);
v___x_624_ = v_reuseFailAlloc_652_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_625_ = l_StateRefT_x27_instMonad___redArg(v___x_624_);
v___x_626_ = l_ReaderT_instMonad___redArg(v___x_625_);
v___x_627_ = l_StateRefT_x27_instMonad___redArg(v___x_626_);
v___x_628_ = l_ReaderT_instMonad___redArg(v___x_627_);
v___x_629_ = l_ReaderT_instMonad___redArg(v___x_628_);
v___x_630_ = l_StateRefT_x27_instMonad___redArg(v___x_629_);
v___x_631_ = l_ReaderT_instMonad___redArg(v___x_630_);
v___x_632_ = lean_box(0);
v___x_633_ = l_Lean_Meta_Grind_Order_getStruct___redArg(v_a_573_, v_a_574_, v_a_582_);
if (lean_obj_tag(v___x_633_) == 0)
{
lean_object* v_a_634_; lean_object* v_sources_635_; lean_object* v_size_636_; uint8_t v___x_637_; 
v_a_634_ = lean_ctor_get(v___x_633_, 0);
lean_inc(v_a_634_);
lean_dec_ref_known(v___x_633_, 1);
v_sources_635_ = lean_ctor_get(v_a_634_, 5);
lean_inc_ref(v_sources_635_);
lean_dec(v_a_634_);
v_size_636_ = lean_ctor_get(v_sources_635_, 2);
v___x_637_ = lean_nat_dec_lt(v_u_571_, v_size_636_);
if (v___x_637_ == 0)
{
lean_object* v___x_638_; lean_object* v___x_839__overap_639_; lean_object* v___x_640_; 
lean_dec_ref(v_sources_635_);
v___x_638_ = l_outOfBounds___redArg(v___x_632_);
v___x_839__overap_639_ = l_Lean_AssocList_forM___redArg(v___x_631_, v_f_572_, v___x_638_);
lean_inc(v_a_583_);
lean_inc_ref(v_a_582_);
lean_inc(v_a_581_);
lean_inc_ref(v_a_580_);
lean_inc(v_a_579_);
lean_inc_ref(v_a_578_);
lean_inc(v_a_577_);
lean_inc_ref(v_a_576_);
lean_inc(v_a_575_);
lean_inc(v_a_574_);
lean_inc(v_a_573_);
v___x_640_ = lean_apply_12(v___x_839__overap_639_, v_a_573_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_, v_a_583_, lean_box(0));
return v___x_640_;
}
else
{
lean_object* v___x_641_; lean_object* v___x_842__overap_642_; lean_object* v___x_643_; 
v___x_641_ = l_Lean_PersistentArray_get_x21___redArg(v___x_632_, v_sources_635_, v_u_571_);
lean_dec_ref(v_sources_635_);
v___x_842__overap_642_ = l_Lean_AssocList_forM___redArg(v___x_631_, v_f_572_, v___x_641_);
lean_inc(v_a_583_);
lean_inc_ref(v_a_582_);
lean_inc(v_a_581_);
lean_inc_ref(v_a_580_);
lean_inc(v_a_579_);
lean_inc_ref(v_a_578_);
lean_inc(v_a_577_);
lean_inc_ref(v_a_576_);
lean_inc(v_a_575_);
lean_inc(v_a_574_);
lean_inc(v_a_573_);
v___x_643_ = lean_apply_12(v___x_842__overap_642_, v_a_573_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_, v_a_583_, lean_box(0));
return v___x_643_;
}
}
else
{
lean_object* v_a_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_651_; 
lean_dec_ref(v___x_631_);
lean_dec_ref(v_f_572_);
v_a_644_ = lean_ctor_get(v___x_633_, 0);
v_isSharedCheck_651_ = !lean_is_exclusive(v___x_633_);
if (v_isSharedCheck_651_ == 0)
{
v___x_646_ = v___x_633_;
v_isShared_647_ = v_isSharedCheck_651_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_a_644_);
lean_dec(v___x_633_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_651_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___x_649_; 
if (v_isShared_647_ == 0)
{
v___x_649_ = v___x_646_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v_a_644_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_571_ = stack[0].m_obj;
lean_object* v_f_572_ = stack[1].m_obj;
lean_object* v_a_573_ = stack[2].m_obj;
lean_object* v_a_574_ = stack[3].m_obj;
lean_object* v_a_575_ = stack[4].m_obj;
lean_object* v_a_576_ = stack[5].m_obj;
lean_object* v_a_577_ = stack[6].m_obj;
lean_object* v_a_578_ = stack[7].m_obj;
lean_object* v_a_579_ = stack[8].m_obj;
lean_object* v_a_580_ = stack[9].m_obj;
lean_object* v_a_581_ = stack[10].m_obj;
lean_object* v_a_582_ = stack[11].m_obj;
lean_object* v_a_583_ = stack[12].m_obj;
lean_object* v_res_658_;
v_res_658_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf(v_u_571_, v_f_572_, v_a_573_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_, v_a_583_);
stack->m_obj
 = v_res_658_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___boxed(lean_object* v_u_659_, lean_object* v_f_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf(v_u_659_, v_f_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_, v_a_665_, v_a_666_, v_a_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_);
lean_dec(v_a_671_);
lean_dec_ref(v_a_670_);
lean_dec(v_a_669_);
lean_dec_ref(v_a_668_);
lean_dec(v_a_667_);
lean_dec_ref(v_a_666_);
lean_dec(v_a_665_);
lean_dec_ref(v_a_664_);
lean_dec(v_a_663_);
lean_dec(v_a_662_);
lean_dec(v_a_661_);
lean_dec(v_u_659_);
return v_res_673_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachTargetOf(lean_object* v_u_674_, lean_object* v_f_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_){
_start:
{
lean_object* v___x_688_; lean_object* v_toApplicative_689_; lean_object* v_toFunctor_690_; lean_object* v_toSeq_691_; lean_object* v_toSeqLeft_692_; lean_object* v_toSeqRight_693_; lean_object* v___f_694_; lean_object* v___f_695_; lean_object* v___f_696_; lean_object* v___f_697_; lean_object* v___x_698_; lean_object* v___f_699_; lean_object* v___f_700_; lean_object* v___f_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v_toApplicative_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_759_; 
v___x_688_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__1, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__1);
v_toApplicative_689_ = lean_ctor_get(v___x_688_, 0);
v_toFunctor_690_ = lean_ctor_get(v_toApplicative_689_, 0);
v_toSeq_691_ = lean_ctor_get(v_toApplicative_689_, 2);
v_toSeqLeft_692_ = lean_ctor_get(v_toApplicative_689_, 3);
v_toSeqRight_693_ = lean_ctor_get(v_toApplicative_689_, 4);
v___f_694_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__2));
v___f_695_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__3));
lean_inc_ref_n(v_toFunctor_690_, 2);
v___f_696_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_696_, 0, v_toFunctor_690_);
v___f_697_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_697_, 0, v_toFunctor_690_);
v___x_698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_698_, 0, v___f_696_);
lean_ctor_set(v___x_698_, 1, v___f_697_);
lean_inc(v_toSeqRight_693_);
v___f_699_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_699_, 0, v_toSeqRight_693_);
lean_inc(v_toSeqLeft_692_);
v___f_700_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_700_, 0, v_toSeqLeft_692_);
lean_inc(v_toSeq_691_);
v___f_701_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_701_, 0, v_toSeq_691_);
v___x_702_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_702_, 0, v___x_698_);
lean_ctor_set(v___x_702_, 1, v___f_694_);
lean_ctor_set(v___x_702_, 2, v___f_701_);
lean_ctor_set(v___x_702_, 3, v___f_700_);
lean_ctor_set(v___x_702_, 4, v___f_699_);
v___x_703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_703_, 0, v___x_702_);
lean_ctor_set(v___x_703_, 1, v___f_695_);
v___x_704_ = l_StateRefT_x27_instMonad___redArg(v___x_703_);
v_toApplicative_705_ = lean_ctor_get(v___x_704_, 0);
v_isSharedCheck_759_ = !lean_is_exclusive(v___x_704_);
if (v_isSharedCheck_759_ == 0)
{
lean_object* v_unused_760_; 
v_unused_760_ = lean_ctor_get(v___x_704_, 1);
lean_dec(v_unused_760_);
v___x_707_ = v___x_704_;
v_isShared_708_ = v_isSharedCheck_759_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_toApplicative_705_);
lean_dec(v___x_704_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_759_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v_toFunctor_709_; lean_object* v_toSeq_710_; lean_object* v_toSeqLeft_711_; lean_object* v_toSeqRight_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_757_; 
v_toFunctor_709_ = lean_ctor_get(v_toApplicative_705_, 0);
v_toSeq_710_ = lean_ctor_get(v_toApplicative_705_, 2);
v_toSeqLeft_711_ = lean_ctor_get(v_toApplicative_705_, 3);
v_toSeqRight_712_ = lean_ctor_get(v_toApplicative_705_, 4);
v_isSharedCheck_757_ = !lean_is_exclusive(v_toApplicative_705_);
if (v_isSharedCheck_757_ == 0)
{
lean_object* v_unused_758_; 
v_unused_758_ = lean_ctor_get(v_toApplicative_705_, 1);
lean_dec(v_unused_758_);
v___x_714_ = v_toApplicative_705_;
v_isShared_715_ = v_isSharedCheck_757_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_toSeqRight_712_);
lean_inc(v_toSeqLeft_711_);
lean_inc(v_toSeq_710_);
lean_inc(v_toFunctor_709_);
lean_dec(v_toApplicative_705_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_757_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___f_716_; lean_object* v___f_717_; lean_object* v___f_718_; lean_object* v___f_719_; lean_object* v___x_720_; lean_object* v___f_721_; lean_object* v___f_722_; lean_object* v___f_723_; lean_object* v___x_725_; 
v___f_716_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__4));
v___f_717_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__5));
lean_inc_ref(v_toFunctor_709_);
v___f_718_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_718_, 0, v_toFunctor_709_);
v___f_719_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_719_, 0, v_toFunctor_709_);
v___x_720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_720_, 0, v___f_718_);
lean_ctor_set(v___x_720_, 1, v___f_719_);
v___f_721_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_721_, 0, v_toSeqRight_712_);
v___f_722_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_722_, 0, v_toSeqLeft_711_);
v___f_723_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_723_, 0, v_toSeq_710_);
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 4, v___f_721_);
lean_ctor_set(v___x_714_, 3, v___f_722_);
lean_ctor_set(v___x_714_, 2, v___f_723_);
lean_ctor_set(v___x_714_, 1, v___f_716_);
lean_ctor_set(v___x_714_, 0, v___x_720_);
v___x_725_ = v___x_714_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v___x_720_);
lean_ctor_set(v_reuseFailAlloc_756_, 1, v___f_716_);
lean_ctor_set(v_reuseFailAlloc_756_, 2, v___f_723_);
lean_ctor_set(v_reuseFailAlloc_756_, 3, v___f_722_);
lean_ctor_set(v_reuseFailAlloc_756_, 4, v___f_721_);
v___x_725_ = v_reuseFailAlloc_756_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
lean_object* v___x_727_; 
if (v_isShared_708_ == 0)
{
lean_ctor_set(v___x_707_, 1, v___f_717_);
lean_ctor_set(v___x_707_, 0, v___x_725_);
v___x_727_ = v___x_707_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v___x_725_);
lean_ctor_set(v_reuseFailAlloc_755_, 1, v___f_717_);
v___x_727_ = v_reuseFailAlloc_755_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_728_ = l_StateRefT_x27_instMonad___redArg(v___x_727_);
v___x_729_ = l_ReaderT_instMonad___redArg(v___x_728_);
v___x_730_ = l_StateRefT_x27_instMonad___redArg(v___x_729_);
v___x_731_ = l_ReaderT_instMonad___redArg(v___x_730_);
v___x_732_ = l_ReaderT_instMonad___redArg(v___x_731_);
v___x_733_ = l_StateRefT_x27_instMonad___redArg(v___x_732_);
v___x_734_ = l_ReaderT_instMonad___redArg(v___x_733_);
v___x_735_ = lean_box(0);
v___x_736_ = l_Lean_Meta_Grind_Order_getStruct___redArg(v_a_676_, v_a_677_, v_a_685_);
if (lean_obj_tag(v___x_736_) == 0)
{
lean_object* v_a_737_; lean_object* v_targets_738_; lean_object* v_size_739_; uint8_t v___x_740_; 
v_a_737_ = lean_ctor_get(v___x_736_, 0);
lean_inc(v_a_737_);
lean_dec_ref_known(v___x_736_, 1);
v_targets_738_ = lean_ctor_get(v_a_737_, 6);
lean_inc_ref(v_targets_738_);
lean_dec(v_a_737_);
v_size_739_ = lean_ctor_get(v_targets_738_, 2);
v___x_740_ = lean_nat_dec_lt(v_u_674_, v_size_739_);
if (v___x_740_ == 0)
{
lean_object* v___x_741_; lean_object* v___x_839__overap_742_; lean_object* v___x_743_; 
lean_dec_ref(v_targets_738_);
v___x_741_ = l_outOfBounds___redArg(v___x_735_);
v___x_839__overap_742_ = l_Lean_AssocList_forM___redArg(v___x_734_, v_f_675_, v___x_741_);
lean_inc(v_a_686_);
lean_inc_ref(v_a_685_);
lean_inc(v_a_684_);
lean_inc_ref(v_a_683_);
lean_inc(v_a_682_);
lean_inc_ref(v_a_681_);
lean_inc(v_a_680_);
lean_inc_ref(v_a_679_);
lean_inc(v_a_678_);
lean_inc(v_a_677_);
lean_inc(v_a_676_);
v___x_743_ = lean_apply_12(v___x_839__overap_742_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_, v_a_682_, v_a_683_, v_a_684_, v_a_685_, v_a_686_, lean_box(0));
return v___x_743_;
}
else
{
lean_object* v___x_744_; lean_object* v___x_842__overap_745_; lean_object* v___x_746_; 
v___x_744_ = l_Lean_PersistentArray_get_x21___redArg(v___x_735_, v_targets_738_, v_u_674_);
lean_dec_ref(v_targets_738_);
v___x_842__overap_745_ = l_Lean_AssocList_forM___redArg(v___x_734_, v_f_675_, v___x_744_);
lean_inc(v_a_686_);
lean_inc_ref(v_a_685_);
lean_inc(v_a_684_);
lean_inc_ref(v_a_683_);
lean_inc(v_a_682_);
lean_inc_ref(v_a_681_);
lean_inc(v_a_680_);
lean_inc_ref(v_a_679_);
lean_inc(v_a_678_);
lean_inc(v_a_677_);
lean_inc(v_a_676_);
v___x_746_ = lean_apply_12(v___x_842__overap_745_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_, v_a_682_, v_a_683_, v_a_684_, v_a_685_, v_a_686_, lean_box(0));
return v___x_746_;
}
}
else
{
lean_object* v_a_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_754_; 
lean_dec_ref(v___x_734_);
lean_dec_ref(v_f_675_);
v_a_747_ = lean_ctor_get(v___x_736_, 0);
v_isSharedCheck_754_ = !lean_is_exclusive(v___x_736_);
if (v_isSharedCheck_754_ == 0)
{
v___x_749_ = v___x_736_;
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_a_747_);
lean_dec(v___x_736_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_752_; 
if (v_isShared_750_ == 0)
{
v___x_752_ = v___x_749_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v_a_747_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachTargetOf_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_674_ = stack[0].m_obj;
lean_object* v_f_675_ = stack[1].m_obj;
lean_object* v_a_676_ = stack[2].m_obj;
lean_object* v_a_677_ = stack[3].m_obj;
lean_object* v_a_678_ = stack[4].m_obj;
lean_object* v_a_679_ = stack[5].m_obj;
lean_object* v_a_680_ = stack[6].m_obj;
lean_object* v_a_681_ = stack[7].m_obj;
lean_object* v_a_682_ = stack[8].m_obj;
lean_object* v_a_683_ = stack[9].m_obj;
lean_object* v_a_684_ = stack[10].m_obj;
lean_object* v_a_685_ = stack[11].m_obj;
lean_object* v_a_686_ = stack[12].m_obj;
lean_object* v_res_761_;
v_res_761_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachTargetOf(v_u_674_, v_f_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_, v_a_682_, v_a_683_, v_a_684_, v_a_685_, v_a_686_);
stack->m_obj
 = v_res_761_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachTargetOf___boxed(lean_object* v_u_762_, lean_object* v_f_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachTargetOf(v_u_762_, v_f_763_, v_a_764_, v_a_765_, v_a_766_, v_a_767_, v_a_768_, v_a_769_, v_a_770_, v_a_771_, v_a_772_, v_a_773_, v_a_774_);
lean_dec(v_a_774_);
lean_dec_ref(v_a_773_);
lean_dec(v_a_772_);
lean_dec_ref(v_a_771_);
lean_dec(v_a_770_);
lean_dec_ref(v_a_769_);
lean_dec(v_a_768_);
lean_dec_ref(v_a_767_);
lean_dec(v_a_766_);
lean_dec(v_a_765_);
lean_dec(v_a_764_);
lean_dec(v_u_762_);
return v_res_776_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isShorter___redArg(lean_object* v_u_777_, lean_object* v_v_778_, lean_object* v_k_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_){
_start:
{
lean_object* v___x_784_; 
v___x_784_ = l_Lean_Meta_Grind_Order_getDist_x3f___redArg(v_u_777_, v_v_778_, v_a_780_, v_a_781_, v_a_782_);
if (lean_obj_tag(v___x_784_) == 0)
{
lean_object* v_a_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_804_; 
v_a_785_ = lean_ctor_get(v___x_784_, 0);
v_isSharedCheck_804_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_804_ == 0)
{
v___x_787_ = v___x_784_;
v_isShared_788_ = v_isSharedCheck_804_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_a_785_);
lean_dec(v___x_784_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_804_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
if (lean_obj_tag(v_a_785_) == 1)
{
lean_object* v_val_789_; uint8_t v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; uint8_t v___x_794_; lean_object* v___x_795_; lean_object* v___x_797_; 
v_val_789_ = lean_ctor_get(v_a_785_, 0);
lean_inc(v_val_789_);
lean_dec_ref_known(v_a_785_, 1);
v___x_790_ = l_Lean_Meta_Grind_Order_Weight_compare(v_k_779_, v_val_789_);
lean_dec(v_val_789_);
v___x_791_ = lean_box(v___x_790_);
v___x_792_ = lean_obj_tag_nat(v___x_791_);
lean_dec(v___x_791_);
v___x_793_ = lean_unsigned_to_nat(0u);
v___x_794_ = lean_nat_dec_eq(v___x_792_, v___x_793_);
v___x_795_ = lean_box(v___x_794_);
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 0, v___x_795_);
v___x_797_ = v___x_787_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v___x_795_);
v___x_797_ = v_reuseFailAlloc_798_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
return v___x_797_;
}
}
else
{
uint8_t v___x_799_; lean_object* v___x_800_; lean_object* v___x_802_; 
lean_dec(v_a_785_);
v___x_799_ = 1;
v___x_800_ = lean_box(v___x_799_);
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 0, v___x_800_);
v___x_802_ = v___x_787_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v___x_800_);
v___x_802_ = v_reuseFailAlloc_803_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
return v___x_802_;
}
}
}
}
else
{
lean_object* v_a_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_812_; 
v_a_805_ = lean_ctor_get(v___x_784_, 0);
v_isSharedCheck_812_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_812_ == 0)
{
v___x_807_ = v___x_784_;
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_a_805_);
lean_dec(v___x_784_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_810_; 
if (v_isShared_808_ == 0)
{
v___x_810_ = v___x_807_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_a_805_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isShorter___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_777_ = stack[0].m_obj;
lean_object* v_v_778_ = stack[1].m_obj;
lean_object* v_k_779_ = stack[2].m_obj;
lean_object* v_a_780_ = stack[3].m_obj;
lean_object* v_a_781_ = stack[4].m_obj;
lean_object* v_a_782_ = stack[5].m_obj;
lean_object* v_res_813_;
v_res_813_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isShorter___redArg(v_u_777_, v_v_778_, v_k_779_, v_a_780_, v_a_781_, v_a_782_);
stack->m_obj
 = v_res_813_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isShorter___redArg___boxed(lean_object* v_u_814_, lean_object* v_v_815_, lean_object* v_k_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_){
_start:
{
lean_object* v_res_821_; 
v_res_821_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isShorter___redArg(v_u_814_, v_v_815_, v_k_816_, v_a_817_, v_a_818_, v_a_819_);
lean_dec_ref(v_a_819_);
lean_dec(v_a_818_);
lean_dec(v_a_817_);
lean_dec_ref(v_k_816_);
lean_dec(v_v_815_);
lean_dec(v_u_814_);
return v_res_821_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isShorter(lean_object* v_u_822_, lean_object* v_v_823_, lean_object* v_k_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_){
_start:
{
lean_object* v___x_837_; 
v___x_837_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isShorter___redArg(v_u_822_, v_v_823_, v_k_824_, v_a_825_, v_a_826_, v_a_834_);
return v___x_837_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isShorter_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_822_ = stack[0].m_obj;
lean_object* v_v_823_ = stack[1].m_obj;
lean_object* v_k_824_ = stack[2].m_obj;
lean_object* v_a_825_ = stack[3].m_obj;
lean_object* v_a_826_ = stack[4].m_obj;
lean_object* v_a_827_ = stack[5].m_obj;
lean_object* v_a_828_ = stack[6].m_obj;
lean_object* v_a_829_ = stack[7].m_obj;
lean_object* v_a_830_ = stack[8].m_obj;
lean_object* v_a_831_ = stack[9].m_obj;
lean_object* v_a_832_ = stack[10].m_obj;
lean_object* v_a_833_ = stack[11].m_obj;
lean_object* v_a_834_ = stack[12].m_obj;
lean_object* v_a_835_ = stack[13].m_obj;
lean_object* v_res_838_;
v_res_838_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isShorter(v_u_822_, v_v_823_, v_k_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_, v_a_829_, v_a_830_, v_a_831_, v_a_832_, v_a_833_, v_a_834_, v_a_835_);
stack->m_obj
 = v_res_838_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isShorter___boxed(lean_object* v_u_839_, lean_object* v_v_840_, lean_object* v_k_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_){
_start:
{
lean_object* v_res_854_; 
v_res_854_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isShorter(v_u_839_, v_v_840_, v_k_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_);
lean_dec(v_a_852_);
lean_dec_ref(v_a_851_);
lean_dec(v_a_850_);
lean_dec_ref(v_a_849_);
lean_dec(v_a_848_);
lean_dec_ref(v_a_847_);
lean_dec(v_a_846_);
lean_dec_ref(v_a_845_);
lean_dec(v_a_844_);
lean_dec(v_a_843_);
lean_dec(v_a_842_);
lean_dec_ref(v_k_841_);
lean_dec(v_v_840_);
lean_dec(v_u_839_);
return v_res_854_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___lam__0(lean_object* v_p_855_, lean_object* v_s_856_){
_start:
{
lean_object* v_id_857_; lean_object* v_nodes_858_; lean_object* v_nodeMap_859_; lean_object* v_cnstrs_860_; lean_object* v_cnstrsOf_861_; lean_object* v_sources_862_; lean_object* v_targets_863_; lean_object* v_proofs_864_; lean_object* v_propagate_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_873_; 
v_id_857_ = lean_ctor_get(v_s_856_, 0);
v_nodes_858_ = lean_ctor_get(v_s_856_, 1);
v_nodeMap_859_ = lean_ctor_get(v_s_856_, 2);
v_cnstrs_860_ = lean_ctor_get(v_s_856_, 3);
v_cnstrsOf_861_ = lean_ctor_get(v_s_856_, 4);
v_sources_862_ = lean_ctor_get(v_s_856_, 5);
v_targets_863_ = lean_ctor_get(v_s_856_, 6);
v_proofs_864_ = lean_ctor_get(v_s_856_, 7);
v_propagate_865_ = lean_ctor_get(v_s_856_, 8);
v_isSharedCheck_873_ = !lean_is_exclusive(v_s_856_);
if (v_isSharedCheck_873_ == 0)
{
v___x_867_ = v_s_856_;
v_isShared_868_ = v_isSharedCheck_873_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_propagate_865_);
lean_inc(v_proofs_864_);
lean_inc(v_targets_863_);
lean_inc(v_sources_862_);
lean_inc(v_cnstrsOf_861_);
lean_inc(v_cnstrs_860_);
lean_inc(v_nodeMap_859_);
lean_inc(v_nodes_858_);
lean_inc(v_id_857_);
lean_dec(v_s_856_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_873_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_869_; lean_object* v___x_871_; 
v___x_869_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_869_, 0, v_p_855_);
lean_ctor_set(v___x_869_, 1, v_propagate_865_);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 8, v___x_869_);
v___x_871_ = v___x_867_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_id_857_);
lean_ctor_set(v_reuseFailAlloc_872_, 1, v_nodes_858_);
lean_ctor_set(v_reuseFailAlloc_872_, 2, v_nodeMap_859_);
lean_ctor_set(v_reuseFailAlloc_872_, 3, v_cnstrs_860_);
lean_ctor_set(v_reuseFailAlloc_872_, 4, v_cnstrsOf_861_);
lean_ctor_set(v_reuseFailAlloc_872_, 5, v_sources_862_);
lean_ctor_set(v_reuseFailAlloc_872_, 6, v_targets_863_);
lean_ctor_set(v_reuseFailAlloc_872_, 7, v_proofs_864_);
lean_ctor_set(v_reuseFailAlloc_872_, 8, v___x_869_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0_spec__0(lean_object* v_msgData_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_){
_start:
{
lean_object* v___x_880_; lean_object* v_env_881_; uint8_t v___x_882_; lean_object* v_env_883_; lean_object* v___x_884_; lean_object* v_toCold_885_; lean_object* v_mctx_886_; lean_object* v_lctx_887_; lean_object* v_options_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_880_ = lean_st_ref_get(v___y_878_);
v_env_881_ = lean_ctor_get(v___x_880_, 0);
lean_inc_ref(v_env_881_);
lean_dec(v___x_880_);
v___x_882_ = 0;
v_env_883_ = l_Lean_Environment_setRecordingDeps(v_env_881_, v___x_882_);
v___x_884_ = lean_st_ref_get(v___y_876_);
v_toCold_885_ = lean_ctor_get(v___y_877_, 0);
v_mctx_886_ = lean_ctor_get(v___x_884_, 0);
lean_inc_ref(v_mctx_886_);
lean_dec(v___x_884_);
v_lctx_887_ = lean_ctor_get(v___y_875_, 2);
v_options_888_ = lean_ctor_get(v_toCold_885_, 2);
lean_inc_ref(v_options_888_);
lean_inc_ref(v_lctx_887_);
v___x_889_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_889_, 0, v_env_883_);
lean_ctor_set(v___x_889_, 1, v_mctx_886_);
lean_ctor_set(v___x_889_, 2, v_lctx_887_);
lean_ctor_set(v___x_889_, 3, v_options_888_);
v___x_890_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_890_, 0, v___x_889_);
lean_ctor_set(v___x_890_, 1, v_msgData_874_);
v___x_891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_891_, 0, v___x_890_);
return v___x_891_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_874_ = stack[0].m_obj;
lean_object* v___y_875_ = stack[1].m_obj;
lean_object* v___y_876_ = stack[2].m_obj;
lean_object* v___y_877_ = stack[3].m_obj;
lean_object* v___y_878_ = stack[4].m_obj;
lean_object* v_res_892_;
v_res_892_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0_spec__0(v_msgData_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_);
stack->m_obj
 = v_res_892_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0_spec__0___boxed(lean_object* v_msgData_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0_spec__0(v_msgData_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
lean_dec(v___y_895_);
lean_dec_ref(v___y_894_);
return v_res_899_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_900_; double v___x_901_; 
v___x_900_ = lean_unsigned_to_nat(0u);
v___x_901_ = lean_float_of_nat(v___x_900_);
return v___x_901_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(lean_object* v_cls_905_, lean_object* v_msg_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_){
_start:
{
lean_object* v_ref_912_; lean_object* v___x_913_; lean_object* v_a_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_959_; 
v_ref_912_ = lean_ctor_get(v___y_909_, 2);
v___x_913_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0_spec__0(v_msg_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_);
v_a_914_ = lean_ctor_get(v___x_913_, 0);
v_isSharedCheck_959_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_959_ == 0)
{
v___x_916_ = v___x_913_;
v_isShared_917_ = v_isSharedCheck_959_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_a_914_);
lean_dec(v___x_913_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_959_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v___x_918_; lean_object* v_traceState_919_; lean_object* v_env_920_; lean_object* v_nextMacroScope_921_; lean_object* v_ngen_922_; lean_object* v_auxDeclNGen_923_; lean_object* v_cache_924_; lean_object* v_recordedDeps_925_; lean_object* v_messages_926_; lean_object* v_infoState_927_; lean_object* v_snapshotTasks_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_958_; 
v___x_918_ = lean_st_ref_take(v___y_910_);
v_traceState_919_ = lean_ctor_get(v___x_918_, 4);
v_env_920_ = lean_ctor_get(v___x_918_, 0);
v_nextMacroScope_921_ = lean_ctor_get(v___x_918_, 1);
v_ngen_922_ = lean_ctor_get(v___x_918_, 2);
v_auxDeclNGen_923_ = lean_ctor_get(v___x_918_, 3);
v_cache_924_ = lean_ctor_get(v___x_918_, 5);
v_recordedDeps_925_ = lean_ctor_get(v___x_918_, 6);
v_messages_926_ = lean_ctor_get(v___x_918_, 7);
v_infoState_927_ = lean_ctor_get(v___x_918_, 8);
v_snapshotTasks_928_ = lean_ctor_get(v___x_918_, 9);
v_isSharedCheck_958_ = !lean_is_exclusive(v___x_918_);
if (v_isSharedCheck_958_ == 0)
{
v___x_930_ = v___x_918_;
v_isShared_931_ = v_isSharedCheck_958_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_snapshotTasks_928_);
lean_inc(v_infoState_927_);
lean_inc(v_messages_926_);
lean_inc(v_recordedDeps_925_);
lean_inc(v_cache_924_);
lean_inc(v_traceState_919_);
lean_inc(v_auxDeclNGen_923_);
lean_inc(v_ngen_922_);
lean_inc(v_nextMacroScope_921_);
lean_inc(v_env_920_);
lean_dec(v___x_918_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_958_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
uint64_t v_tid_932_; lean_object* v_traces_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_957_; 
v_tid_932_ = lean_ctor_get_uint64(v_traceState_919_, sizeof(void*)*1);
v_traces_933_ = lean_ctor_get(v_traceState_919_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v_traceState_919_);
if (v_isSharedCheck_957_ == 0)
{
v___x_935_ = v_traceState_919_;
v_isShared_936_ = v_isSharedCheck_957_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_traces_933_);
lean_dec(v_traceState_919_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_957_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v___x_937_; lean_object* v___x_938_; double v___x_939_; uint8_t v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_948_; 
v___x_937_ = lean_box(0);
v___x_938_ = lean_box(0);
v___x_939_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg___closed__0);
v___x_940_ = 0;
v___x_941_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg___closed__1));
v___x_942_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_942_, 0, v_cls_905_);
lean_ctor_set(v___x_942_, 1, v___x_938_);
lean_ctor_set(v___x_942_, 2, v___x_941_);
lean_ctor_set_float(v___x_942_, sizeof(void*)*3, v___x_939_);
lean_ctor_set_float(v___x_942_, sizeof(void*)*3 + 8, v___x_939_);
lean_ctor_set_uint8(v___x_942_, sizeof(void*)*3 + 16, v___x_940_);
v___x_943_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg___closed__2));
v___x_944_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_944_, 0, v___x_942_);
lean_ctor_set(v___x_944_, 1, v_a_914_);
lean_ctor_set(v___x_944_, 2, v___x_943_);
lean_inc(v_ref_912_);
v___x_945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_945_, 0, v_ref_912_);
lean_ctor_set(v___x_945_, 1, v___x_944_);
v___x_946_ = l_Lean_PersistentArray_push___redArg(v_traces_933_, v___x_945_);
if (v_isShared_936_ == 0)
{
lean_ctor_set(v___x_935_, 0, v___x_946_);
v___x_948_ = v___x_935_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v___x_946_);
lean_ctor_set_uint64(v_reuseFailAlloc_956_, sizeof(void*)*1, v_tid_932_);
v___x_948_ = v_reuseFailAlloc_956_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
lean_object* v___x_950_; 
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 4, v___x_948_);
v___x_950_ = v___x_930_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v_env_920_);
lean_ctor_set(v_reuseFailAlloc_955_, 1, v_nextMacroScope_921_);
lean_ctor_set(v_reuseFailAlloc_955_, 2, v_ngen_922_);
lean_ctor_set(v_reuseFailAlloc_955_, 3, v_auxDeclNGen_923_);
lean_ctor_set(v_reuseFailAlloc_955_, 4, v___x_948_);
lean_ctor_set(v_reuseFailAlloc_955_, 5, v_cache_924_);
lean_ctor_set(v_reuseFailAlloc_955_, 6, v_recordedDeps_925_);
lean_ctor_set(v_reuseFailAlloc_955_, 7, v_messages_926_);
lean_ctor_set(v_reuseFailAlloc_955_, 8, v_infoState_927_);
lean_ctor_set(v_reuseFailAlloc_955_, 9, v_snapshotTasks_928_);
v___x_950_ = v_reuseFailAlloc_955_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
lean_object* v___x_951_; lean_object* v___x_953_; 
v___x_951_ = lean_st_ref_put(v___y_910_, v___x_950_);
if (v_isShared_917_ == 0)
{
lean_ctor_set(v___x_916_, 0, v___x_937_);
v___x_953_ = v___x_916_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v___x_937_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_905_ = stack[0].m_obj;
lean_object* v_msg_906_ = stack[1].m_obj;
lean_object* v___y_907_ = stack[2].m_obj;
lean_object* v___y_908_ = stack[3].m_obj;
lean_object* v___y_909_ = stack[4].m_obj;
lean_object* v___y_910_ = stack[5].m_obj;
lean_object* v_res_960_;
v_res_960_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(v_cls_905_, v_msg_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_);
stack->m_obj
 = v_res_960_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg___boxed(lean_object* v_cls_961_, lean_object* v_msg_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(v_cls_961_, v_msg_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_);
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
lean_dec(v___y_964_);
lean_dec_ref(v___y_963_);
return v_res_968_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__7(void){
_start:
{
lean_object* v_cls_981_; lean_object* v___x_982_; lean_object* v___x_983_; 
v_cls_981_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__4));
v___x_982_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__6));
v___x_983_ = l_Lean_Name_append(v___x_982_, v_cls_981_);
return v___x_983_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate(lean_object* v_p_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_){
_start:
{
lean_object* v_toCold_997_; lean_object* v_options_998_; lean_object* v_inheritedTraceOptions_999_; uint8_t v_hasTrace_1000_; lean_object* v___f_1001_; 
v_toCold_997_ = lean_ctor_get(v_a_994_, 0);
v_options_998_ = lean_ctor_get(v_toCold_997_, 2);
v_inheritedTraceOptions_999_ = lean_ctor_get(v_toCold_997_, 11);
v_hasTrace_1000_ = lean_ctor_get_uint8(v_options_998_, sizeof(void*)*1);
lean_inc_ref(v_p_984_);
v___f_1001_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___lam__0), 2, 1);
lean_closure_set(v___f_1001_, 0, v_p_984_);
if (v_hasTrace_1000_ == 0)
{
lean_object* v___x_1002_; 
lean_dec_ref(v_p_984_);
v___x_1002_ = l_Lean_Meta_Grind_Order_modifyStruct___redArg(v___f_1001_, v_a_985_, v_a_986_);
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
lean_dec_ref(v_p_984_);
v___x_1006_ = l_Lean_Meta_Grind_Order_modifyStruct___redArg(v___f_1001_, v_a_985_, v_a_986_);
return v___x_1006_;
}
else
{
lean_object* v___x_1007_; 
v___x_1007_ = l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg(v_p_984_, v_a_985_, v_a_986_, v_a_994_);
if (lean_obj_tag(v___x_1007_) == 0)
{
lean_object* v_a_1008_; lean_object* v___x_1009_; 
v_a_1008_ = lean_ctor_get(v___x_1007_, 0);
lean_inc(v_a_1008_);
lean_dec_ref_known(v___x_1007_, 1);
v___x_1009_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(v_cls_1003_, v_a_1008_, v_a_992_, v_a_993_, v_a_994_, v_a_995_);
if (lean_obj_tag(v___x_1009_) == 0)
{
lean_object* v___x_1010_; 
lean_dec_ref_known(v___x_1009_, 1);
v___x_1010_ = l_Lean_Meta_Grind_Order_modifyStruct___redArg(v___f_1001_, v_a_985_, v_a_986_);
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
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_984_ = stack[0].m_obj;
lean_object* v_a_985_ = stack[1].m_obj;
lean_object* v_a_986_ = stack[2].m_obj;
lean_object* v_a_987_ = stack[3].m_obj;
lean_object* v_a_988_ = stack[4].m_obj;
lean_object* v_a_989_ = stack[5].m_obj;
lean_object* v_a_990_ = stack[6].m_obj;
lean_object* v_a_991_ = stack[7].m_obj;
lean_object* v_a_992_ = stack[8].m_obj;
lean_object* v_a_993_ = stack[9].m_obj;
lean_object* v_a_994_ = stack[10].m_obj;
lean_object* v_a_995_ = stack[11].m_obj;
lean_object* v_res_1019_;
v_res_1019_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate(v_p_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_, v_a_995_);
stack->m_obj
 = v_res_1019_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___boxed(lean_object* v_p_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate(v_p_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_);
lean_dec(v_a_1031_);
lean_dec_ref(v_a_1030_);
lean_dec(v_a_1029_);
lean_dec_ref(v_a_1028_);
lean_dec(v_a_1027_);
lean_dec_ref(v_a_1026_);
lean_dec(v_a_1025_);
lean_dec_ref(v_a_1024_);
lean_dec(v_a_1023_);
lean_dec(v_a_1022_);
lean_dec(v_a_1021_);
return v_res_1033_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0(lean_object* v_cls_1034_, lean_object* v_msg_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_){
_start:
{
lean_object* v___x_1048_; 
v___x_1048_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(v_cls_1034_, v_msg_1035_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_);
return v___x_1048_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_1034_ = stack[0].m_obj;
lean_object* v_msg_1035_ = stack[1].m_obj;
lean_object* v___y_1036_ = stack[2].m_obj;
lean_object* v___y_1037_ = stack[3].m_obj;
lean_object* v___y_1038_ = stack[4].m_obj;
lean_object* v___y_1039_ = stack[5].m_obj;
lean_object* v___y_1040_ = stack[6].m_obj;
lean_object* v___y_1041_ = stack[7].m_obj;
lean_object* v___y_1042_ = stack[8].m_obj;
lean_object* v___y_1043_ = stack[9].m_obj;
lean_object* v___y_1044_ = stack[10].m_obj;
lean_object* v___y_1045_ = stack[11].m_obj;
lean_object* v___y_1046_ = stack[12].m_obj;
lean_object* v_res_1049_;
v_res_1049_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0(v_cls_1034_, v_msg_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_);
stack->m_obj
 = v_res_1049_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___boxed(lean_object* v_cls_1050_, lean_object* v_msg_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0(v_cls_1050_, v_msg_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_);
lean_dec(v___y_1062_);
lean_dec_ref(v___y_1061_);
lean_dec(v___y_1060_);
lean_dec_ref(v___y_1059_);
lean_dec(v___y_1058_);
lean_dec_ref(v___y_1057_);
lean_dec(v___y_1056_);
lean_dec_ref(v___y_1055_);
lean_dec(v___y_1054_);
lean_dec(v___y_1053_);
lean_dec(v___y_1052_);
return v_res_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1065_, lean_object* v_vals_1066_, lean_object* v_i_1067_, lean_object* v_k_1068_){
_start:
{
lean_object* v___x_1069_; uint8_t v___x_1070_; 
v___x_1069_ = lean_array_get_size(v_keys_1065_);
v___x_1070_ = lean_nat_dec_lt(v_i_1067_, v___x_1069_);
if (v___x_1070_ == 0)
{
lean_object* v___x_1071_; 
lean_dec(v_i_1067_);
v___x_1071_ = lean_box(0);
return v___x_1071_;
}
else
{
lean_object* v_k_x27_1072_; size_t v___x_1073_; size_t v___x_1074_; uint8_t v___x_1075_; 
v_k_x27_1072_ = lean_array_fget_borrowed(v_keys_1065_, v_i_1067_);
v___x_1073_ = lean_ptr_addr(v_k_1068_);
v___x_1074_ = lean_ptr_addr(v_k_x27_1072_);
v___x_1075_ = lean_usize_dec_eq(v___x_1073_, v___x_1074_);
if (v___x_1075_ == 0)
{
lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1076_ = lean_unsigned_to_nat(1u);
v___x_1077_ = lean_nat_add(v_i_1067_, v___x_1076_);
lean_dec(v_i_1067_);
v_i_1067_ = v___x_1077_;
goto _start;
}
else
{
lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1079_ = lean_array_fget_borrowed(v_vals_1066_, v_i_1067_);
lean_dec(v_i_1067_);
lean_inc(v___x_1079_);
v___x_1080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1079_);
return v___x_1080_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1081_, lean_object* v_vals_1082_, lean_object* v_i_1083_, lean_object* v_k_1084_){
_start:
{
lean_object* v_res_1085_; 
v_res_1085_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0_spec__1___redArg(v_keys_1081_, v_vals_1082_, v_i_1083_, v_k_1084_);
lean_dec_ref(v_k_1084_);
lean_dec_ref(v_vals_1082_);
lean_dec_ref(v_keys_1081_);
return v_res_1085_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg(lean_object* v_x_1086_, size_t v_x_1087_, lean_object* v_x_1088_){
_start:
{
if (lean_obj_tag(v_x_1086_) == 0)
{
lean_object* v_es_1089_; lean_object* v___x_1090_; size_t v___x_1091_; size_t v___x_1092_; lean_object* v_j_1093_; lean_object* v___x_1094_; 
v_es_1089_ = lean_ctor_get(v_x_1086_, 0);
v___x_1090_ = lean_box(2);
v___x_1091_ = ((size_t)31ULL);
v___x_1092_ = lean_usize_land(v_x_1087_, v___x_1091_);
v_j_1093_ = lean_usize_to_nat(v___x_1092_);
v___x_1094_ = lean_array_get_borrowed(v___x_1090_, v_es_1089_, v_j_1093_);
lean_dec(v_j_1093_);
switch(lean_obj_tag(v___x_1094_))
{
case 0:
{
lean_object* v_key_1095_; lean_object* v_val_1096_; size_t v___x_1097_; size_t v___x_1098_; uint8_t v___x_1099_; 
v_key_1095_ = lean_ctor_get(v___x_1094_, 0);
v_val_1096_ = lean_ctor_get(v___x_1094_, 1);
v___x_1097_ = lean_ptr_addr(v_x_1088_);
v___x_1098_ = lean_ptr_addr(v_key_1095_);
v___x_1099_ = lean_usize_dec_eq(v___x_1097_, v___x_1098_);
if (v___x_1099_ == 0)
{
lean_object* v___x_1100_; 
v___x_1100_ = lean_box(0);
return v___x_1100_;
}
else
{
lean_object* v___x_1101_; 
lean_inc(v_val_1096_);
v___x_1101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1101_, 0, v_val_1096_);
return v___x_1101_;
}
}
case 1:
{
lean_object* v_node_1102_; size_t v___x_1103_; size_t v___x_1104_; 
v_node_1102_ = lean_ctor_get(v___x_1094_, 0);
v___x_1103_ = ((size_t)5ULL);
v___x_1104_ = lean_usize_shift_right(v_x_1087_, v___x_1103_);
v_x_1086_ = v_node_1102_;
v_x_1087_ = v___x_1104_;
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
v_ks_1107_ = lean_ctor_get(v_x_1086_, 0);
v_vs_1108_ = lean_ctor_get(v_x_1086_, 1);
v___x_1109_ = lean_unsigned_to_nat(0u);
v___x_1110_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0_spec__1___redArg(v_ks_1107_, v_vs_1108_, v___x_1109_, v_x_1088_);
return v___x_1110_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1086_ = stack[0].m_obj;
size_t v_x_1087_ = stack[1].m_num;
lean_object* v_x_1088_ = stack[2].m_obj;
lean_object* v_res_1111_;
v_res_1111_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg(v_x_1086_, v_x_1087_, v_x_1088_);
stack->m_obj
 = v_res_1111_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg___boxed(lean_object* v_x_1112_, lean_object* v_x_1113_, lean_object* v_x_1114_){
_start:
{
size_t v_x_9912__boxed_1115_; lean_object* v_res_1116_; 
v_x_9912__boxed_1115_ = lean_unbox_usize(v_x_1113_);
lean_dec(v_x_1113_);
v_res_1116_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg(v_x_1112_, v_x_9912__boxed_1115_, v_x_1114_);
lean_dec_ref(v_x_1114_);
lean_dec_ref(v_x_1112_);
return v_res_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(lean_object* v_x_1117_, lean_object* v_x_1118_){
_start:
{
size_t v___x_1119_; size_t v___x_1120_; size_t v___x_1121_; uint64_t v___x_1122_; size_t v___x_1123_; lean_object* v___x_1124_; 
v___x_1119_ = lean_ptr_addr(v_x_1118_);
v___x_1120_ = ((size_t)3ULL);
v___x_1121_ = lean_usize_shift_right(v___x_1119_, v___x_1120_);
v___x_1122_ = lean_usize_to_uint64(v___x_1121_);
v___x_1123_ = lean_uint64_to_usize(v___x_1122_);
v___x_1124_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg(v_x_1117_, v___x_1123_, v_x_1118_);
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg___boxed(lean_object* v_x_1125_, lean_object* v_x_1126_){
_start:
{
lean_object* v_res_1127_; 
v_res_1127_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_x_1125_, v_x_1126_);
lean_dec_ref(v_x_1126_);
lean_dec_ref(v_x_1125_);
return v_res_1127_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5(void){
_start:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1137_ = lean_box(0);
v___x_1138_ = ((lean_object*)(l_Lean_Meta_Grind_Order_propagateEqTrue___closed__4));
v___x_1139_ = l_Lean_mkConst(v___x_1138_, v___x_1137_);
return v___x_1139_;
}
}
lean_object* l_Lean_Meta_Grind_Order_propagateEqTrue(lean_object* v_c_1140_, lean_object* v_e_1141_, lean_object* v_u_1142_, lean_object* v_v_1143_, lean_object* v_k_1144_, lean_object* v_k_x27_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_){
_start:
{
lean_object* v_h_1159_; lean_object* v___y_1160_; lean_object* v___y_1161_; lean_object* v___y_1162_; lean_object* v___y_1163_; lean_object* v___y_1164_; lean_object* v___y_1165_; lean_object* v___y_1166_; lean_object* v___x_1186_; 
v___x_1186_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath(v_u_1142_, v_v_1143_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_);
if (lean_obj_tag(v___x_1186_) == 0)
{
lean_object* v_a_1187_; lean_object* v___x_1188_; 
v_a_1187_ = lean_ctor_get(v___x_1186_, 0);
lean_inc(v_a_1187_);
lean_dec_ref_known(v___x_1186_, 1);
v___x_1188_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_u_1142_, v_a_1146_, v_a_1147_, v_a_1155_);
if (lean_obj_tag(v___x_1188_) == 0)
{
lean_object* v_a_1189_; lean_object* v___x_1190_; 
v_a_1189_ = lean_ctor_get(v___x_1188_, 0);
lean_inc(v_a_1189_);
lean_dec_ref_known(v___x_1188_, 1);
v___x_1190_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_v_1143_, v_a_1146_, v_a_1147_, v_a_1155_);
if (lean_obj_tag(v___x_1190_) == 0)
{
lean_object* v_a_1191_; lean_object* v___x_1192_; 
v_a_1191_ = lean_ctor_get(v___x_1190_, 0);
lean_inc(v_a_1191_);
lean_dec_ref_known(v___x_1190_, 1);
v___x_1192_ = l_Lean_Meta_Grind_Order_mkPropagateEqTrueProof(v_a_1189_, v_a_1191_, v_k_1144_, v_a_1187_, v_k_x27_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_);
if (lean_obj_tag(v___x_1192_) == 0)
{
lean_object* v_h_x3f_1193_; 
v_h_x3f_1193_ = lean_ctor_get(v_c_1140_, 4);
lean_inc(v_h_x3f_1193_);
if (lean_obj_tag(v_h_x3f_1193_) == 1)
{
lean_object* v_a_1194_; lean_object* v_e_1195_; lean_object* v_val_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
v_a_1194_ = lean_ctor_get(v___x_1192_, 0);
lean_inc(v_a_1194_);
lean_dec_ref_known(v___x_1192_, 1);
v_e_1195_ = lean_ctor_get(v_c_1140_, 3);
lean_inc_ref(v_e_1195_);
lean_dec_ref(v_c_1140_);
v_val_1196_ = lean_ctor_get(v_h_x3f_1193_, 0);
lean_inc(v_val_1196_);
lean_dec_ref_known(v_h_x3f_1193_, 1);
v___x_1197_ = lean_obj_once(&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5, &l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5_once, _init_l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5);
lean_inc_ref(v_e_1141_);
v___x_1198_ = l_Lean_mkApp4(v___x_1197_, v_e_1141_, v_e_1195_, v_val_1196_, v_a_1194_);
v_h_1159_ = v___x_1198_;
v___y_1160_ = v_a_1147_;
v___y_1161_ = v_a_1149_;
v___y_1162_ = v_a_1151_;
v___y_1163_ = v_a_1153_;
v___y_1164_ = v_a_1154_;
v___y_1165_ = v_a_1155_;
v___y_1166_ = v_a_1156_;
goto v___jp_1158_;
}
else
{
lean_object* v_a_1199_; 
lean_dec(v_h_x3f_1193_);
lean_dec_ref(v_c_1140_);
v_a_1199_ = lean_ctor_get(v___x_1192_, 0);
lean_inc(v_a_1199_);
lean_dec_ref_known(v___x_1192_, 1);
v_h_1159_ = v_a_1199_;
v___y_1160_ = v_a_1147_;
v___y_1161_ = v_a_1149_;
v___y_1162_ = v_a_1151_;
v___y_1163_ = v_a_1153_;
v___y_1164_ = v_a_1154_;
v___y_1165_ = v_a_1155_;
v___y_1166_ = v_a_1156_;
goto v___jp_1158_;
}
}
else
{
lean_object* v_a_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1207_; 
lean_dec_ref(v_e_1141_);
lean_dec_ref(v_c_1140_);
v_a_1200_ = lean_ctor_get(v___x_1192_, 0);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1202_ = v___x_1192_;
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_a_1200_);
lean_dec(v___x_1192_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1205_; 
if (v_isShared_1203_ == 0)
{
v___x_1205_ = v___x_1202_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_a_1200_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
}
}
else
{
lean_object* v_a_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1215_; 
lean_dec(v_a_1189_);
lean_dec(v_a_1187_);
lean_dec_ref(v_e_1141_);
lean_dec_ref(v_c_1140_);
v_a_1208_ = lean_ctor_get(v___x_1190_, 0);
v_isSharedCheck_1215_ = !lean_is_exclusive(v___x_1190_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_1210_ = v___x_1190_;
v_isShared_1211_ = v_isSharedCheck_1215_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_a_1208_);
lean_dec(v___x_1190_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1215_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v___x_1213_; 
if (v_isShared_1211_ == 0)
{
v___x_1213_ = v___x_1210_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v_a_1208_);
v___x_1213_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
return v___x_1213_;
}
}
}
}
else
{
lean_object* v_a_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1223_; 
lean_dec(v_a_1187_);
lean_dec_ref(v_e_1141_);
lean_dec_ref(v_c_1140_);
v_a_1216_ = lean_ctor_get(v___x_1188_, 0);
v_isSharedCheck_1223_ = !lean_is_exclusive(v___x_1188_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1218_ = v___x_1188_;
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_a_1216_);
lean_dec(v___x_1188_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v___x_1221_; 
if (v_isShared_1219_ == 0)
{
v___x_1221_ = v___x_1218_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v_a_1216_);
v___x_1221_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
return v___x_1221_;
}
}
}
}
else
{
lean_object* v_a_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1231_; 
lean_dec_ref(v_e_1141_);
lean_dec_ref(v_c_1140_);
v_a_1224_ = lean_ctor_get(v___x_1186_, 0);
v_isSharedCheck_1231_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1226_ = v___x_1186_;
v_isShared_1227_ = v_isSharedCheck_1231_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_a_1224_);
lean_dec(v___x_1186_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1231_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v___x_1229_; 
if (v_isShared_1227_ == 0)
{
v___x_1229_ = v___x_1226_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v_a_1224_);
v___x_1229_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
return v___x_1229_;
}
}
}
v___jp_1158_:
{
lean_object* v___x_1167_; 
v___x_1167_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v___y_1160_, v___y_1165_);
if (lean_obj_tag(v___x_1167_) == 0)
{
lean_object* v_a_1168_; lean_object* v_termMapInv_1169_; lean_object* v___x_1170_; 
v_a_1168_ = lean_ctor_get(v___x_1167_, 0);
lean_inc(v_a_1168_);
lean_dec_ref_known(v___x_1167_, 1);
v_termMapInv_1169_ = lean_ctor_get(v_a_1168_, 4);
lean_inc_ref(v_termMapInv_1169_);
lean_dec(v_a_1168_);
v___x_1170_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMapInv_1169_, v_e_1141_);
lean_dec_ref(v_termMapInv_1169_);
if (lean_obj_tag(v___x_1170_) == 1)
{
lean_object* v_val_1171_; lean_object* v_fst_1172_; lean_object* v_snd_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
v_val_1171_ = lean_ctor_get(v___x_1170_, 0);
lean_inc(v_val_1171_);
lean_dec_ref_known(v___x_1170_, 1);
v_fst_1172_ = lean_ctor_get(v_val_1171_, 0);
lean_inc_n(v_fst_1172_, 2);
v_snd_1173_ = lean_ctor_get(v_val_1171_, 1);
lean_inc(v_snd_1173_);
lean_dec(v_val_1171_);
v___x_1174_ = lean_obj_once(&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5, &l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5_once, _init_l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5);
v___x_1175_ = l_Lean_mkApp4(v___x_1174_, v_fst_1172_, v_e_1141_, v_snd_1173_, v_h_1159_);
v___x_1176_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_fst_1172_, v___x_1175_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_);
return v___x_1176_;
}
else
{
lean_object* v___x_1177_; 
lean_dec(v___x_1170_);
v___x_1177_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_e_1141_, v_h_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_);
return v___x_1177_;
}
}
else
{
lean_object* v_a_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1185_; 
lean_dec_ref(v_h_1159_);
lean_dec_ref(v_e_1141_);
v_a_1178_ = lean_ctor_get(v___x_1167_, 0);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_1167_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1180_ = v___x_1167_;
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_a_1178_);
lean_dec(v___x_1167_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1183_; 
if (v_isShared_1181_ == 0)
{
v___x_1183_ = v___x_1180_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_a_1178_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Order_propagateEqTrue_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_1140_ = stack[0].m_obj;
lean_object* v_e_1141_ = stack[1].m_obj;
lean_object* v_u_1142_ = stack[2].m_obj;
lean_object* v_v_1143_ = stack[3].m_obj;
lean_object* v_k_1144_ = stack[4].m_obj;
lean_object* v_k_x27_1145_ = stack[5].m_obj;
lean_object* v_a_1146_ = stack[6].m_obj;
lean_object* v_a_1147_ = stack[7].m_obj;
lean_object* v_a_1148_ = stack[8].m_obj;
lean_object* v_a_1149_ = stack[9].m_obj;
lean_object* v_a_1150_ = stack[10].m_obj;
lean_object* v_a_1151_ = stack[11].m_obj;
lean_object* v_a_1152_ = stack[12].m_obj;
lean_object* v_a_1153_ = stack[13].m_obj;
lean_object* v_a_1154_ = stack[14].m_obj;
lean_object* v_a_1155_ = stack[15].m_obj;
lean_object* v_a_1156_ = stack[16].m_obj;
lean_object* v_res_1232_;
v_res_1232_ = l_Lean_Meta_Grind_Order_propagateEqTrue(v_c_1140_, v_e_1141_, v_u_1142_, v_v_1143_, v_k_1144_, v_k_x27_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_);
stack->m_obj
 = v_res_1232_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateEqTrue___boxed(lean_object** _args){
lean_object* v_c_1233_ = _args[0];
lean_object* v_e_1234_ = _args[1];
lean_object* v_u_1235_ = _args[2];
lean_object* v_v_1236_ = _args[3];
lean_object* v_k_1237_ = _args[4];
lean_object* v_k_x27_1238_ = _args[5];
lean_object* v_a_1239_ = _args[6];
lean_object* v_a_1240_ = _args[7];
lean_object* v_a_1241_ = _args[8];
lean_object* v_a_1242_ = _args[9];
lean_object* v_a_1243_ = _args[10];
lean_object* v_a_1244_ = _args[11];
lean_object* v_a_1245_ = _args[12];
lean_object* v_a_1246_ = _args[13];
lean_object* v_a_1247_ = _args[14];
lean_object* v_a_1248_ = _args[15];
lean_object* v_a_1249_ = _args[16];
lean_object* v_a_1250_ = _args[17];
_start:
{
lean_object* v_res_1251_; 
v_res_1251_ = l_Lean_Meta_Grind_Order_propagateEqTrue(v_c_1233_, v_e_1234_, v_u_1235_, v_v_1236_, v_k_1237_, v_k_x27_1238_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_, v_a_1244_, v_a_1245_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_);
lean_dec(v_a_1249_);
lean_dec_ref(v_a_1248_);
lean_dec(v_a_1247_);
lean_dec_ref(v_a_1246_);
lean_dec(v_a_1245_);
lean_dec_ref(v_a_1244_);
lean_dec(v_a_1243_);
lean_dec_ref(v_a_1242_);
lean_dec(v_a_1241_);
lean_dec(v_a_1240_);
lean_dec(v_a_1239_);
lean_dec_ref(v_k_x27_1238_);
lean_dec_ref(v_k_1237_);
lean_dec(v_v_1236_);
lean_dec(v_u_1235_);
return v_res_1251_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0(lean_object* v_00_u03b2_1252_, lean_object* v_x_1253_, lean_object* v_x_1254_){
_start:
{
lean_object* v___x_1255_; 
v___x_1255_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_x_1253_, v_x_1254_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___boxed(lean_object* v_00_u03b2_1256_, lean_object* v_x_1257_, lean_object* v_x_1258_){
_start:
{
lean_object* v_res_1259_; 
v_res_1259_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0(v_00_u03b2_1256_, v_x_1257_, v_x_1258_);
lean_dec_ref(v_x_1258_);
lean_dec_ref(v_x_1257_);
return v_res_1259_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0(lean_object* v_00_u03b2_1260_, lean_object* v_x_1261_, size_t v_x_1262_, lean_object* v_x_1263_){
_start:
{
lean_object* v___x_1264_; 
v___x_1264_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg(v_x_1261_, v_x_1262_, v_x_1263_);
return v___x_1264_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1261_ = stack[1].m_obj;
size_t v_x_1262_ = stack[2].m_num;
lean_object* v_x_1263_ = stack[3].m_obj;
lean_object* v_res_1265_;
v_res_1265_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0(lean_box(0), v_x_1261_, v_x_1262_, v_x_1263_);
stack->m_obj
 = v_res_1265_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1266_, lean_object* v_x_1267_, lean_object* v_x_1268_, lean_object* v_x_1269_){
_start:
{
size_t v_x_10306__boxed_1270_; lean_object* v_res_1271_; 
v_x_10306__boxed_1270_ = lean_unbox_usize(v_x_1268_);
lean_dec(v_x_1268_);
v_res_1271_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0(v_00_u03b2_1266_, v_x_1267_, v_x_10306__boxed_1270_, v_x_1269_);
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
v___x_1286_ = l_Lean_Meta_Grind_instInhabitedGoalM___redArg();
return v___x_1286_;
}
}
lean_object* l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0(lean_object* v_msg_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_){
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
LEAN_EXPORT void l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1287_ = stack[0].m_obj;
lean_object* v___y_1288_ = stack[1].m_obj;
lean_object* v___y_1289_ = stack[2].m_obj;
lean_object* v___y_1290_ = stack[3].m_obj;
lean_object* v___y_1291_ = stack[4].m_obj;
lean_object* v___y_1292_ = stack[5].m_obj;
lean_object* v___y_1293_ = stack[6].m_obj;
lean_object* v___y_1294_ = stack[7].m_obj;
lean_object* v___y_1295_ = stack[8].m_obj;
lean_object* v___y_1296_ = stack[9].m_obj;
lean_object* v___y_1297_ = stack[10].m_obj;
lean_object* v___y_1298_ = stack[11].m_obj;
lean_object* v_res_1304_;
v_res_1304_ = l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0(v_msg_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_);
stack->m_obj
 = v_res_1304_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0___boxed(lean_object* v_msg_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_){
_start:
{
lean_object* v_res_1318_; 
v_res_1318_ = l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0(v_msg_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
lean_dec(v___y_1316_);
lean_dec_ref(v___y_1315_);
lean_dec(v___y_1314_);
lean_dec_ref(v___y_1313_);
lean_dec(v___y_1312_);
lean_dec_ref(v___y_1311_);
lean_dec(v___y_1310_);
lean_dec_ref(v___y_1309_);
lean_dec(v___y_1308_);
lean_dec(v___y_1307_);
lean_dec(v___y_1306_);
return v_res_1318_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__3(void){
_start:
{
lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; 
v___x_1322_ = ((lean_object*)(l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__2));
v___x_1323_ = lean_unsigned_to_nat(2u);
v___x_1324_ = lean_unsigned_to_nat(86u);
v___x_1325_ = ((lean_object*)(l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__1));
v___x_1326_ = ((lean_object*)(l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__0));
v___x_1327_ = l_mkPanicMessageWithDecl(v___x_1326_, v___x_1325_, v___x_1324_, v___x_1323_, v___x_1322_);
return v___x_1327_;
}
}
lean_object* l_Lean_Meta_Grind_Order_propagateSelfEqTrue(lean_object* v_c_1328_, lean_object* v_e_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_){
_start:
{
lean_object* v_h_1343_; lean_object* v___y_1344_; lean_object* v___y_1345_; lean_object* v___y_1346_; lean_object* v___y_1347_; lean_object* v___y_1348_; lean_object* v___y_1349_; lean_object* v___y_1350_; lean_object* v_u_1370_; lean_object* v_v_1371_; lean_object* v_e_1372_; lean_object* v_h_x3f_1373_; lean_object* v___x_1374_; 
v_u_1370_ = lean_ctor_get(v_c_1328_, 0);
v_v_1371_ = lean_ctor_get(v_c_1328_, 1);
v_e_1372_ = lean_ctor_get(v_c_1328_, 3);
lean_inc_ref(v_e_1372_);
v_h_x3f_1373_ = lean_ctor_get(v_c_1328_, 4);
lean_inc(v_h_x3f_1373_);
v___x_1374_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_u_1370_, v_a_1330_, v_a_1331_, v_a_1339_);
if (lean_obj_tag(v___x_1374_) == 0)
{
lean_object* v_a_1375_; uint8_t v___x_1376_; 
v_a_1375_ = lean_ctor_get(v___x_1374_, 0);
lean_inc(v_a_1375_);
lean_dec_ref_known(v___x_1374_, 1);
v___x_1376_ = lean_nat_dec_eq(v_u_1370_, v_v_1371_);
if (v___x_1376_ == 0)
{
lean_object* v___x_1377_; lean_object* v___x_1378_; 
lean_dec(v_a_1375_);
lean_dec(v_h_x3f_1373_);
lean_dec_ref(v_e_1372_);
lean_dec_ref(v_e_1329_);
lean_dec_ref(v_c_1328_);
v___x_1377_ = lean_obj_once(&l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__3, &l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__3_once, _init_l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__3);
v___x_1378_ = l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0(v___x_1377_, v_a_1330_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_);
return v___x_1378_;
}
else
{
lean_object* v___x_1379_; lean_object* v___x_1380_; 
v___x_1379_ = l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(v_c_1328_);
lean_dec_ref(v_c_1328_);
v___x_1380_ = l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof(v_a_1375_, v___x_1379_, v_a_1330_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_);
lean_dec_ref(v___x_1379_);
if (lean_obj_tag(v___x_1380_) == 0)
{
if (lean_obj_tag(v_h_x3f_1373_) == 1)
{
lean_object* v_a_1381_; lean_object* v_val_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; 
v_a_1381_ = lean_ctor_get(v___x_1380_, 0);
lean_inc(v_a_1381_);
lean_dec_ref_known(v___x_1380_, 1);
v_val_1382_ = lean_ctor_get(v_h_x3f_1373_, 0);
lean_inc(v_val_1382_);
lean_dec_ref_known(v_h_x3f_1373_, 1);
v___x_1383_ = lean_obj_once(&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5, &l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5_once, _init_l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5);
lean_inc_ref(v_e_1329_);
v___x_1384_ = l_Lean_mkApp4(v___x_1383_, v_e_1329_, v_e_1372_, v_val_1382_, v_a_1381_);
v_h_1343_ = v___x_1384_;
v___y_1344_ = v_a_1331_;
v___y_1345_ = v_a_1333_;
v___y_1346_ = v_a_1335_;
v___y_1347_ = v_a_1337_;
v___y_1348_ = v_a_1338_;
v___y_1349_ = v_a_1339_;
v___y_1350_ = v_a_1340_;
goto v___jp_1342_;
}
else
{
lean_object* v_a_1385_; 
lean_dec(v_h_x3f_1373_);
lean_dec_ref(v_e_1372_);
v_a_1385_ = lean_ctor_get(v___x_1380_, 0);
lean_inc(v_a_1385_);
lean_dec_ref_known(v___x_1380_, 1);
v_h_1343_ = v_a_1385_;
v___y_1344_ = v_a_1331_;
v___y_1345_ = v_a_1333_;
v___y_1346_ = v_a_1335_;
v___y_1347_ = v_a_1337_;
v___y_1348_ = v_a_1338_;
v___y_1349_ = v_a_1339_;
v___y_1350_ = v_a_1340_;
goto v___jp_1342_;
}
}
else
{
lean_object* v_a_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1393_; 
lean_dec(v_h_x3f_1373_);
lean_dec_ref(v_e_1372_);
lean_dec_ref(v_e_1329_);
v_a_1386_ = lean_ctor_get(v___x_1380_, 0);
v_isSharedCheck_1393_ = !lean_is_exclusive(v___x_1380_);
if (v_isSharedCheck_1393_ == 0)
{
v___x_1388_ = v___x_1380_;
v_isShared_1389_ = v_isSharedCheck_1393_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_a_1386_);
lean_dec(v___x_1380_);
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
lean_dec(v_h_x3f_1373_);
lean_dec_ref(v_e_1372_);
lean_dec_ref(v_e_1329_);
lean_dec_ref(v_c_1328_);
v_a_1394_ = lean_ctor_get(v___x_1374_, 0);
v_isSharedCheck_1401_ = !lean_is_exclusive(v___x_1374_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1396_ = v___x_1374_;
v_isShared_1397_ = v_isSharedCheck_1401_;
goto v_resetjp_1395_;
}
else
{
lean_inc(v_a_1394_);
lean_dec(v___x_1374_);
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
v___jp_1342_:
{
lean_object* v___x_1351_; 
v___x_1351_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v___y_1344_, v___y_1349_);
if (lean_obj_tag(v___x_1351_) == 0)
{
lean_object* v_a_1352_; lean_object* v_termMapInv_1353_; lean_object* v___x_1354_; 
v_a_1352_ = lean_ctor_get(v___x_1351_, 0);
lean_inc(v_a_1352_);
lean_dec_ref_known(v___x_1351_, 1);
v_termMapInv_1353_ = lean_ctor_get(v_a_1352_, 4);
lean_inc_ref(v_termMapInv_1353_);
lean_dec(v_a_1352_);
v___x_1354_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMapInv_1353_, v_e_1329_);
lean_dec_ref(v_termMapInv_1353_);
if (lean_obj_tag(v___x_1354_) == 1)
{
lean_object* v_val_1355_; lean_object* v_fst_1356_; lean_object* v_snd_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; 
v_val_1355_ = lean_ctor_get(v___x_1354_, 0);
lean_inc(v_val_1355_);
lean_dec_ref_known(v___x_1354_, 1);
v_fst_1356_ = lean_ctor_get(v_val_1355_, 0);
lean_inc_n(v_fst_1356_, 2);
v_snd_1357_ = lean_ctor_get(v_val_1355_, 1);
lean_inc(v_snd_1357_);
lean_dec(v_val_1355_);
v___x_1358_ = lean_obj_once(&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5, &l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5_once, _init_l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5);
v___x_1359_ = l_Lean_mkApp4(v___x_1358_, v_fst_1356_, v_e_1329_, v_snd_1357_, v_h_1343_);
v___x_1360_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_fst_1356_, v___x_1359_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_);
return v___x_1360_;
}
else
{
lean_object* v___x_1361_; 
lean_dec(v___x_1354_);
v___x_1361_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_e_1329_, v_h_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_);
return v___x_1361_;
}
}
else
{
lean_object* v_a_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1369_; 
lean_dec_ref(v_h_1343_);
lean_dec_ref(v_e_1329_);
v_a_1362_ = lean_ctor_get(v___x_1351_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1351_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1364_ = v___x_1351_;
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_a_1362_);
lean_dec(v___x_1351_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1367_; 
if (v_isShared_1365_ == 0)
{
v___x_1367_ = v___x_1364_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_a_1362_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Order_propagateSelfEqTrue_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_1328_ = stack[0].m_obj;
lean_object* v_e_1329_ = stack[1].m_obj;
lean_object* v_a_1330_ = stack[2].m_obj;
lean_object* v_a_1331_ = stack[3].m_obj;
lean_object* v_a_1332_ = stack[4].m_obj;
lean_object* v_a_1333_ = stack[5].m_obj;
lean_object* v_a_1334_ = stack[6].m_obj;
lean_object* v_a_1335_ = stack[7].m_obj;
lean_object* v_a_1336_ = stack[8].m_obj;
lean_object* v_a_1337_ = stack[9].m_obj;
lean_object* v_a_1338_ = stack[10].m_obj;
lean_object* v_a_1339_ = stack[11].m_obj;
lean_object* v_a_1340_ = stack[12].m_obj;
lean_object* v_res_1402_;
v_res_1402_ = l_Lean_Meta_Grind_Order_propagateSelfEqTrue(v_c_1328_, v_e_1329_, v_a_1330_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_);
stack->m_obj
 = v_res_1402_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateSelfEqTrue___boxed(lean_object* v_c_1403_, lean_object* v_e_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_, lean_object* v_a_1416_){
_start:
{
lean_object* v_res_1417_; 
v_res_1417_ = l_Lean_Meta_Grind_Order_propagateSelfEqTrue(v_c_1403_, v_e_1404_, v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_, v_a_1414_, v_a_1415_);
lean_dec(v_a_1415_);
lean_dec_ref(v_a_1414_);
lean_dec(v_a_1413_);
lean_dec_ref(v_a_1412_);
lean_dec(v_a_1411_);
lean_dec_ref(v_a_1410_);
lean_dec(v_a_1409_);
lean_dec_ref(v_a_1408_);
lean_dec(v_a_1407_);
lean_dec(v_a_1406_);
lean_dec(v_a_1405_);
return v_res_1417_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2(void){
_start:
{
lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; 
v___x_1424_ = lean_box(0);
v___x_1425_ = ((lean_object*)(l_Lean_Meta_Grind_Order_propagateEqFalse___closed__1));
v___x_1426_ = l_Lean_mkConst(v___x_1425_, v___x_1424_);
return v___x_1426_;
}
}
lean_object* l_Lean_Meta_Grind_Order_propagateEqFalse(lean_object* v_c_1427_, lean_object* v_e_1428_, lean_object* v_u_1429_, lean_object* v_v_1430_, lean_object* v_k_1431_, lean_object* v_k_x27_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_){
_start:
{
lean_object* v_h_1446_; lean_object* v___y_1447_; lean_object* v___y_1448_; lean_object* v___y_1449_; lean_object* v___y_1450_; lean_object* v___y_1451_; lean_object* v___y_1452_; lean_object* v___y_1453_; lean_object* v___x_1473_; 
v___x_1473_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath(v_u_1429_, v_v_1430_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_);
if (lean_obj_tag(v___x_1473_) == 0)
{
lean_object* v_a_1474_; lean_object* v___x_1475_; 
v_a_1474_ = lean_ctor_get(v___x_1473_, 0);
lean_inc(v_a_1474_);
lean_dec_ref_known(v___x_1473_, 1);
v___x_1475_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_u_1429_, v_a_1433_, v_a_1434_, v_a_1442_);
if (lean_obj_tag(v___x_1475_) == 0)
{
lean_object* v_a_1476_; lean_object* v___x_1477_; 
v_a_1476_ = lean_ctor_get(v___x_1475_, 0);
lean_inc(v_a_1476_);
lean_dec_ref_known(v___x_1475_, 1);
v___x_1477_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_v_1430_, v_a_1433_, v_a_1434_, v_a_1442_);
if (lean_obj_tag(v___x_1477_) == 0)
{
lean_object* v_a_1478_; lean_object* v___x_1479_; 
v_a_1478_ = lean_ctor_get(v___x_1477_, 0);
lean_inc(v_a_1478_);
lean_dec_ref_known(v___x_1477_, 1);
v___x_1479_ = l_Lean_Meta_Grind_Order_mkPropagateEqFalseProof(v_a_1476_, v_a_1478_, v_k_1431_, v_a_1474_, v_k_x27_1432_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_);
if (lean_obj_tag(v___x_1479_) == 0)
{
lean_object* v_h_x3f_1480_; 
v_h_x3f_1480_ = lean_ctor_get(v_c_1427_, 4);
lean_inc(v_h_x3f_1480_);
if (lean_obj_tag(v_h_x3f_1480_) == 1)
{
lean_object* v_a_1481_; lean_object* v_e_1482_; lean_object* v_val_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; 
v_a_1481_ = lean_ctor_get(v___x_1479_, 0);
lean_inc(v_a_1481_);
lean_dec_ref_known(v___x_1479_, 1);
v_e_1482_ = lean_ctor_get(v_c_1427_, 3);
lean_inc_ref(v_e_1482_);
lean_dec_ref(v_c_1427_);
v_val_1483_ = lean_ctor_get(v_h_x3f_1480_, 0);
lean_inc(v_val_1483_);
lean_dec_ref_known(v_h_x3f_1480_, 1);
v___x_1484_ = lean_obj_once(&l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2, &l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2_once, _init_l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2);
lean_inc_ref(v_e_1428_);
v___x_1485_ = l_Lean_mkApp4(v___x_1484_, v_e_1428_, v_e_1482_, v_val_1483_, v_a_1481_);
v_h_1446_ = v___x_1485_;
v___y_1447_ = v_a_1434_;
v___y_1448_ = v_a_1436_;
v___y_1449_ = v_a_1438_;
v___y_1450_ = v_a_1440_;
v___y_1451_ = v_a_1441_;
v___y_1452_ = v_a_1442_;
v___y_1453_ = v_a_1443_;
goto v___jp_1445_;
}
else
{
lean_object* v_a_1486_; 
lean_dec(v_h_x3f_1480_);
lean_dec_ref(v_c_1427_);
v_a_1486_ = lean_ctor_get(v___x_1479_, 0);
lean_inc(v_a_1486_);
lean_dec_ref_known(v___x_1479_, 1);
v_h_1446_ = v_a_1486_;
v___y_1447_ = v_a_1434_;
v___y_1448_ = v_a_1436_;
v___y_1449_ = v_a_1438_;
v___y_1450_ = v_a_1440_;
v___y_1451_ = v_a_1441_;
v___y_1452_ = v_a_1442_;
v___y_1453_ = v_a_1443_;
goto v___jp_1445_;
}
}
else
{
lean_object* v_a_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1494_; 
lean_dec_ref(v_e_1428_);
lean_dec_ref(v_c_1427_);
v_a_1487_ = lean_ctor_get(v___x_1479_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1479_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1489_ = v___x_1479_;
v_isShared_1490_ = v_isSharedCheck_1494_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_a_1487_);
lean_dec(v___x_1479_);
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
else
{
lean_object* v_a_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1502_; 
lean_dec(v_a_1476_);
lean_dec(v_a_1474_);
lean_dec_ref(v_e_1428_);
lean_dec_ref(v_c_1427_);
v_a_1495_ = lean_ctor_get(v___x_1477_, 0);
v_isSharedCheck_1502_ = !lean_is_exclusive(v___x_1477_);
if (v_isSharedCheck_1502_ == 0)
{
v___x_1497_ = v___x_1477_;
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_a_1495_);
lean_dec(v___x_1477_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v___x_1500_; 
if (v_isShared_1498_ == 0)
{
v___x_1500_ = v___x_1497_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v_a_1495_);
v___x_1500_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
return v___x_1500_;
}
}
}
}
else
{
lean_object* v_a_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1510_; 
lean_dec(v_a_1474_);
lean_dec_ref(v_e_1428_);
lean_dec_ref(v_c_1427_);
v_a_1503_ = lean_ctor_get(v___x_1475_, 0);
v_isSharedCheck_1510_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1510_ == 0)
{
v___x_1505_ = v___x_1475_;
v_isShared_1506_ = v_isSharedCheck_1510_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_a_1503_);
lean_dec(v___x_1475_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1510_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
lean_object* v___x_1508_; 
if (v_isShared_1506_ == 0)
{
v___x_1508_ = v___x_1505_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v_a_1503_);
v___x_1508_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
return v___x_1508_;
}
}
}
}
else
{
lean_object* v_a_1511_; lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1518_; 
lean_dec_ref(v_e_1428_);
lean_dec_ref(v_c_1427_);
v_a_1511_ = lean_ctor_get(v___x_1473_, 0);
v_isSharedCheck_1518_ = !lean_is_exclusive(v___x_1473_);
if (v_isSharedCheck_1518_ == 0)
{
v___x_1513_ = v___x_1473_;
v_isShared_1514_ = v_isSharedCheck_1518_;
goto v_resetjp_1512_;
}
else
{
lean_inc(v_a_1511_);
lean_dec(v___x_1473_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1518_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
lean_object* v___x_1516_; 
if (v_isShared_1514_ == 0)
{
v___x_1516_ = v___x_1513_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v_a_1511_);
v___x_1516_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
return v___x_1516_;
}
}
}
v___jp_1445_:
{
lean_object* v___x_1454_; 
v___x_1454_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v___y_1447_, v___y_1452_);
if (lean_obj_tag(v___x_1454_) == 0)
{
lean_object* v_a_1455_; lean_object* v_termMapInv_1456_; lean_object* v___x_1457_; 
v_a_1455_ = lean_ctor_get(v___x_1454_, 0);
lean_inc(v_a_1455_);
lean_dec_ref_known(v___x_1454_, 1);
v_termMapInv_1456_ = lean_ctor_get(v_a_1455_, 4);
lean_inc_ref(v_termMapInv_1456_);
lean_dec(v_a_1455_);
v___x_1457_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMapInv_1456_, v_e_1428_);
lean_dec_ref(v_termMapInv_1456_);
if (lean_obj_tag(v___x_1457_) == 1)
{
lean_object* v_val_1458_; lean_object* v_fst_1459_; lean_object* v_snd_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; 
v_val_1458_ = lean_ctor_get(v___x_1457_, 0);
lean_inc(v_val_1458_);
lean_dec_ref_known(v___x_1457_, 1);
v_fst_1459_ = lean_ctor_get(v_val_1458_, 0);
lean_inc_n(v_fst_1459_, 2);
v_snd_1460_ = lean_ctor_get(v_val_1458_, 1);
lean_inc(v_snd_1460_);
lean_dec(v_val_1458_);
v___x_1461_ = lean_obj_once(&l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2, &l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2_once, _init_l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2);
v___x_1462_ = l_Lean_mkApp4(v___x_1461_, v_fst_1459_, v_e_1428_, v_snd_1460_, v_h_1446_);
v___x_1463_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_fst_1459_, v___x_1462_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_);
return v___x_1463_;
}
else
{
lean_object* v___x_1464_; 
lean_dec(v___x_1457_);
v___x_1464_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_e_1428_, v_h_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_);
return v___x_1464_;
}
}
else
{
lean_object* v_a_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1472_; 
lean_dec_ref(v_h_1446_);
lean_dec_ref(v_e_1428_);
v_a_1465_ = lean_ctor_get(v___x_1454_, 0);
v_isSharedCheck_1472_ = !lean_is_exclusive(v___x_1454_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1467_ = v___x_1454_;
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_a_1465_);
lean_dec(v___x_1454_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v___x_1470_; 
if (v_isShared_1468_ == 0)
{
v___x_1470_ = v___x_1467_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v_a_1465_);
v___x_1470_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
return v___x_1470_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Order_propagateEqFalse_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_1427_ = stack[0].m_obj;
lean_object* v_e_1428_ = stack[1].m_obj;
lean_object* v_u_1429_ = stack[2].m_obj;
lean_object* v_v_1430_ = stack[3].m_obj;
lean_object* v_k_1431_ = stack[4].m_obj;
lean_object* v_k_x27_1432_ = stack[5].m_obj;
lean_object* v_a_1433_ = stack[6].m_obj;
lean_object* v_a_1434_ = stack[7].m_obj;
lean_object* v_a_1435_ = stack[8].m_obj;
lean_object* v_a_1436_ = stack[9].m_obj;
lean_object* v_a_1437_ = stack[10].m_obj;
lean_object* v_a_1438_ = stack[11].m_obj;
lean_object* v_a_1439_ = stack[12].m_obj;
lean_object* v_a_1440_ = stack[13].m_obj;
lean_object* v_a_1441_ = stack[14].m_obj;
lean_object* v_a_1442_ = stack[15].m_obj;
lean_object* v_a_1443_ = stack[16].m_obj;
lean_object* v_res_1519_;
v_res_1519_ = l_Lean_Meta_Grind_Order_propagateEqFalse(v_c_1427_, v_e_1428_, v_u_1429_, v_v_1430_, v_k_1431_, v_k_x27_1432_, v_a_1433_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_, v_a_1443_);
stack->m_obj
 = v_res_1519_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateEqFalse___boxed(lean_object** _args){
lean_object* v_c_1520_ = _args[0];
lean_object* v_e_1521_ = _args[1];
lean_object* v_u_1522_ = _args[2];
lean_object* v_v_1523_ = _args[3];
lean_object* v_k_1524_ = _args[4];
lean_object* v_k_x27_1525_ = _args[5];
lean_object* v_a_1526_ = _args[6];
lean_object* v_a_1527_ = _args[7];
lean_object* v_a_1528_ = _args[8];
lean_object* v_a_1529_ = _args[9];
lean_object* v_a_1530_ = _args[10];
lean_object* v_a_1531_ = _args[11];
lean_object* v_a_1532_ = _args[12];
lean_object* v_a_1533_ = _args[13];
lean_object* v_a_1534_ = _args[14];
lean_object* v_a_1535_ = _args[15];
lean_object* v_a_1536_ = _args[16];
lean_object* v_a_1537_ = _args[17];
_start:
{
lean_object* v_res_1538_; 
v_res_1538_ = l_Lean_Meta_Grind_Order_propagateEqFalse(v_c_1520_, v_e_1521_, v_u_1522_, v_v_1523_, v_k_1524_, v_k_x27_1525_, v_a_1526_, v_a_1527_, v_a_1528_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_);
lean_dec(v_a_1536_);
lean_dec_ref(v_a_1535_);
lean_dec(v_a_1534_);
lean_dec_ref(v_a_1533_);
lean_dec(v_a_1532_);
lean_dec_ref(v_a_1531_);
lean_dec(v_a_1530_);
lean_dec_ref(v_a_1529_);
lean_dec(v_a_1528_);
lean_dec(v_a_1527_);
lean_dec(v_a_1526_);
lean_dec_ref(v_k_x27_1525_);
lean_dec_ref(v_k_1524_);
lean_dec(v_v_1523_);
lean_dec(v_u_1522_);
return v_res_1538_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_propagateSelfEqFalse___closed__1(void){
_start:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; 
v___x_1540_ = ((lean_object*)(l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__2));
v___x_1541_ = lean_unsigned_to_nat(2u);
v___x_1542_ = lean_unsigned_to_nat(111u);
v___x_1543_ = ((lean_object*)(l_Lean_Meta_Grind_Order_propagateSelfEqFalse___closed__0));
v___x_1544_ = ((lean_object*)(l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__0));
v___x_1545_ = l_mkPanicMessageWithDecl(v___x_1544_, v___x_1543_, v___x_1542_, v___x_1541_, v___x_1540_);
return v___x_1545_;
}
}
lean_object* l_Lean_Meta_Grind_Order_propagateSelfEqFalse(lean_object* v_c_1546_, lean_object* v_e_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_){
_start:
{
lean_object* v_h_1561_; lean_object* v___y_1562_; lean_object* v___y_1563_; lean_object* v___y_1564_; lean_object* v___y_1565_; lean_object* v___y_1566_; lean_object* v___y_1567_; lean_object* v___y_1568_; lean_object* v_u_1588_; lean_object* v_v_1589_; lean_object* v_e_1590_; lean_object* v_h_x3f_1591_; lean_object* v___x_1592_; 
v_u_1588_ = lean_ctor_get(v_c_1546_, 0);
v_v_1589_ = lean_ctor_get(v_c_1546_, 1);
v_e_1590_ = lean_ctor_get(v_c_1546_, 3);
lean_inc_ref(v_e_1590_);
v_h_x3f_1591_ = lean_ctor_get(v_c_1546_, 4);
lean_inc(v_h_x3f_1591_);
v___x_1592_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_u_1588_, v_a_1548_, v_a_1549_, v_a_1557_);
if (lean_obj_tag(v___x_1592_) == 0)
{
lean_object* v_a_1593_; uint8_t v___x_1594_; 
v_a_1593_ = lean_ctor_get(v___x_1592_, 0);
lean_inc(v_a_1593_);
lean_dec_ref_known(v___x_1592_, 1);
v___x_1594_ = lean_nat_dec_eq(v_u_1588_, v_v_1589_);
if (v___x_1594_ == 0)
{
lean_object* v___x_1595_; lean_object* v___x_1596_; 
lean_dec(v_a_1593_);
lean_dec(v_h_x3f_1591_);
lean_dec_ref(v_e_1590_);
lean_dec_ref(v_e_1547_);
lean_dec_ref(v_c_1546_);
v___x_1595_ = lean_obj_once(&l_Lean_Meta_Grind_Order_propagateSelfEqFalse___closed__1, &l_Lean_Meta_Grind_Order_propagateSelfEqFalse___closed__1_once, _init_l_Lean_Meta_Grind_Order_propagateSelfEqFalse___closed__1);
v___x_1596_ = l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0(v___x_1595_, v_a_1548_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_);
return v___x_1596_;
}
else
{
lean_object* v___x_1597_; lean_object* v___x_1598_; 
v___x_1597_ = l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(v_c_1546_);
lean_dec_ref(v_c_1546_);
v___x_1598_ = l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof(v_a_1593_, v___x_1597_, v_a_1548_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_);
lean_dec_ref(v___x_1597_);
if (lean_obj_tag(v___x_1598_) == 0)
{
if (lean_obj_tag(v_h_x3f_1591_) == 1)
{
lean_object* v_a_1599_; lean_object* v_val_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; 
v_a_1599_ = lean_ctor_get(v___x_1598_, 0);
lean_inc(v_a_1599_);
lean_dec_ref_known(v___x_1598_, 1);
v_val_1600_ = lean_ctor_get(v_h_x3f_1591_, 0);
lean_inc(v_val_1600_);
lean_dec_ref_known(v_h_x3f_1591_, 1);
v___x_1601_ = lean_obj_once(&l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2, &l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2_once, _init_l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2);
lean_inc_ref(v_e_1547_);
v___x_1602_ = l_Lean_mkApp4(v___x_1601_, v_e_1547_, v_e_1590_, v_val_1600_, v_a_1599_);
v_h_1561_ = v___x_1602_;
v___y_1562_ = v_a_1549_;
v___y_1563_ = v_a_1551_;
v___y_1564_ = v_a_1553_;
v___y_1565_ = v_a_1555_;
v___y_1566_ = v_a_1556_;
v___y_1567_ = v_a_1557_;
v___y_1568_ = v_a_1558_;
goto v___jp_1560_;
}
else
{
lean_object* v_a_1603_; 
lean_dec(v_h_x3f_1591_);
lean_dec_ref(v_e_1590_);
v_a_1603_ = lean_ctor_get(v___x_1598_, 0);
lean_inc(v_a_1603_);
lean_dec_ref_known(v___x_1598_, 1);
v_h_1561_ = v_a_1603_;
v___y_1562_ = v_a_1549_;
v___y_1563_ = v_a_1551_;
v___y_1564_ = v_a_1553_;
v___y_1565_ = v_a_1555_;
v___y_1566_ = v_a_1556_;
v___y_1567_ = v_a_1557_;
v___y_1568_ = v_a_1558_;
goto v___jp_1560_;
}
}
else
{
lean_object* v_a_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1611_; 
lean_dec(v_h_x3f_1591_);
lean_dec_ref(v_e_1590_);
lean_dec_ref(v_e_1547_);
v_a_1604_ = lean_ctor_get(v___x_1598_, 0);
v_isSharedCheck_1611_ = !lean_is_exclusive(v___x_1598_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1606_ = v___x_1598_;
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_a_1604_);
lean_dec(v___x_1598_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v___x_1609_; 
if (v_isShared_1607_ == 0)
{
v___x_1609_ = v___x_1606_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_a_1604_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
return v___x_1609_;
}
}
}
}
}
else
{
lean_object* v_a_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1619_; 
lean_dec(v_h_x3f_1591_);
lean_dec_ref(v_e_1590_);
lean_dec_ref(v_e_1547_);
lean_dec_ref(v_c_1546_);
v_a_1612_ = lean_ctor_get(v___x_1592_, 0);
v_isSharedCheck_1619_ = !lean_is_exclusive(v___x_1592_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1614_ = v___x_1592_;
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_a_1612_);
lean_dec(v___x_1592_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v___x_1617_; 
if (v_isShared_1615_ == 0)
{
v___x_1617_ = v___x_1614_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v_a_1612_);
v___x_1617_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
return v___x_1617_;
}
}
}
v___jp_1560_:
{
lean_object* v___x_1569_; 
v___x_1569_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v___y_1562_, v___y_1567_);
if (lean_obj_tag(v___x_1569_) == 0)
{
lean_object* v_a_1570_; lean_object* v_termMapInv_1571_; lean_object* v___x_1572_; 
v_a_1570_ = lean_ctor_get(v___x_1569_, 0);
lean_inc(v_a_1570_);
lean_dec_ref_known(v___x_1569_, 1);
v_termMapInv_1571_ = lean_ctor_get(v_a_1570_, 4);
lean_inc_ref(v_termMapInv_1571_);
lean_dec(v_a_1570_);
v___x_1572_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMapInv_1571_, v_e_1547_);
lean_dec_ref(v_termMapInv_1571_);
if (lean_obj_tag(v___x_1572_) == 1)
{
lean_object* v_val_1573_; lean_object* v_fst_1574_; lean_object* v_snd_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; 
v_val_1573_ = lean_ctor_get(v___x_1572_, 0);
lean_inc(v_val_1573_);
lean_dec_ref_known(v___x_1572_, 1);
v_fst_1574_ = lean_ctor_get(v_val_1573_, 0);
lean_inc_n(v_fst_1574_, 2);
v_snd_1575_ = lean_ctor_get(v_val_1573_, 1);
lean_inc(v_snd_1575_);
lean_dec(v_val_1573_);
v___x_1576_ = lean_obj_once(&l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2, &l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2_once, _init_l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2);
v___x_1577_ = l_Lean_mkApp4(v___x_1576_, v_fst_1574_, v_e_1547_, v_snd_1575_, v_h_1561_);
v___x_1578_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_fst_1574_, v___x_1577_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_);
return v___x_1578_;
}
else
{
lean_object* v___x_1579_; 
lean_dec(v___x_1572_);
v___x_1579_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_e_1547_, v_h_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_);
return v___x_1579_;
}
}
else
{
lean_object* v_a_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1587_; 
lean_dec_ref(v_h_1561_);
lean_dec_ref(v_e_1547_);
v_a_1580_ = lean_ctor_get(v___x_1569_, 0);
v_isSharedCheck_1587_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1582_ = v___x_1569_;
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_a_1580_);
lean_dec(v___x_1569_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
lean_object* v___x_1585_; 
if (v_isShared_1583_ == 0)
{
v___x_1585_ = v___x_1582_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v_a_1580_);
v___x_1585_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
return v___x_1585_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Order_propagateSelfEqFalse_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_1546_ = stack[0].m_obj;
lean_object* v_e_1547_ = stack[1].m_obj;
lean_object* v_a_1548_ = stack[2].m_obj;
lean_object* v_a_1549_ = stack[3].m_obj;
lean_object* v_a_1550_ = stack[4].m_obj;
lean_object* v_a_1551_ = stack[5].m_obj;
lean_object* v_a_1552_ = stack[6].m_obj;
lean_object* v_a_1553_ = stack[7].m_obj;
lean_object* v_a_1554_ = stack[8].m_obj;
lean_object* v_a_1555_ = stack[9].m_obj;
lean_object* v_a_1556_ = stack[10].m_obj;
lean_object* v_a_1557_ = stack[11].m_obj;
lean_object* v_a_1558_ = stack[12].m_obj;
lean_object* v_res_1620_;
v_res_1620_ = l_Lean_Meta_Grind_Order_propagateSelfEqFalse(v_c_1546_, v_e_1547_, v_a_1548_, v_a_1549_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_);
stack->m_obj
 = v_res_1620_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateSelfEqFalse___boxed(lean_object* v_c_1621_, lean_object* v_e_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_){
_start:
{
lean_object* v_res_1635_; 
v_res_1635_ = l_Lean_Meta_Grind_Order_propagateSelfEqFalse(v_c_1621_, v_e_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_, v_a_1631_, v_a_1632_, v_a_1633_);
lean_dec(v_a_1633_);
lean_dec_ref(v_a_1632_);
lean_dec(v_a_1631_);
lean_dec_ref(v_a_1630_);
lean_dec(v_a_1629_);
lean_dec_ref(v_a_1628_);
lean_dec(v_a_1627_);
lean_dec_ref(v_a_1626_);
lean_dec(v_a_1625_);
lean_dec(v_a_1624_);
lean_dec(v_a_1623_);
return v_res_1635_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f___redArg(lean_object* v_e_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_){
_start:
{
lean_object* v___x_1640_; 
v___x_1640_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_1637_, v_a_1638_);
if (lean_obj_tag(v___x_1640_) == 0)
{
lean_object* v_a_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1650_; 
v_a_1641_ = lean_ctor_get(v___x_1640_, 0);
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1640_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1643_ = v___x_1640_;
v_isShared_1644_ = v_isSharedCheck_1650_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_a_1641_);
lean_dec(v___x_1640_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1650_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v_termMapInv_1645_; lean_object* v___x_1646_; lean_object* v___x_1648_; 
v_termMapInv_1645_ = lean_ctor_get(v_a_1641_, 4);
lean_inc_ref(v_termMapInv_1645_);
lean_dec(v_a_1641_);
v___x_1646_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMapInv_1645_, v_e_1636_);
lean_dec_ref(v_termMapInv_1645_);
if (v_isShared_1644_ == 0)
{
lean_ctor_set(v___x_1643_, 0, v___x_1646_);
v___x_1648_ = v___x_1643_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v___x_1646_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
}
}
}
else
{
lean_object* v_a_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1658_; 
v_a_1651_ = lean_ctor_get(v___x_1640_, 0);
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1640_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1653_ = v___x_1640_;
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_a_1651_);
lean_dec(v___x_1640_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___x_1656_; 
if (v_isShared_1654_ == 0)
{
v___x_1656_ = v___x_1653_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v_a_1651_);
v___x_1656_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
return v___x_1656_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1636_ = stack[0].m_obj;
lean_object* v_a_1637_ = stack[1].m_obj;
lean_object* v_a_1638_ = stack[2].m_obj;
lean_object* v_res_1659_;
v_res_1659_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f___redArg(v_e_1636_, v_a_1637_, v_a_1638_);
stack->m_obj
 = v_res_1659_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f___redArg___boxed(lean_object* v_e_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_){
_start:
{
lean_object* v_res_1664_; 
v_res_1664_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f___redArg(v_e_1660_, v_a_1661_, v_a_1662_);
lean_dec_ref(v_a_1662_);
lean_dec(v_a_1661_);
lean_dec_ref(v_e_1660_);
return v_res_1664_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f(lean_object* v_e_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_){
_start:
{
lean_object* v___x_1677_; 
v___x_1677_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f___redArg(v_e_1665_, v_a_1666_, v_a_1674_);
return v___x_1677_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1665_ = stack[0].m_obj;
lean_object* v_a_1666_ = stack[1].m_obj;
lean_object* v_a_1667_ = stack[2].m_obj;
lean_object* v_a_1668_ = stack[3].m_obj;
lean_object* v_a_1669_ = stack[4].m_obj;
lean_object* v_a_1670_ = stack[5].m_obj;
lean_object* v_a_1671_ = stack[6].m_obj;
lean_object* v_a_1672_ = stack[7].m_obj;
lean_object* v_a_1673_ = stack[8].m_obj;
lean_object* v_a_1674_ = stack[9].m_obj;
lean_object* v_a_1675_ = stack[10].m_obj;
lean_object* v_res_1678_;
v_res_1678_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f(v_e_1665_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_);
stack->m_obj
 = v_res_1678_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f___boxed(lean_object* v_e_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_){
_start:
{
lean_object* v_res_1691_; 
v_res_1691_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f(v_e_1679_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_, v_a_1686_, v_a_1687_, v_a_1688_, v_a_1689_);
lean_dec(v_a_1689_);
lean_dec_ref(v_a_1688_);
lean_dec(v_a_1687_);
lean_dec_ref(v_a_1686_);
lean_dec(v_a_1685_);
lean_dec_ref(v_a_1684_);
lean_dec(v_a_1683_);
lean_dec_ref(v_a_1682_);
lean_dec(v_a_1681_);
lean_dec(v_a_1680_);
lean_dec_ref(v_e_1679_);
return v_res_1691_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending___lam__0(lean_object* v_s_1692_){
_start:
{
lean_object* v_id_1693_; lean_object* v_nodes_1694_; lean_object* v_nodeMap_1695_; lean_object* v_cnstrs_1696_; lean_object* v_cnstrsOf_1697_; lean_object* v_sources_1698_; lean_object* v_targets_1699_; lean_object* v_proofs_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1708_; 
v_id_1693_ = lean_ctor_get(v_s_1692_, 0);
v_nodes_1694_ = lean_ctor_get(v_s_1692_, 1);
v_nodeMap_1695_ = lean_ctor_get(v_s_1692_, 2);
v_cnstrs_1696_ = lean_ctor_get(v_s_1692_, 3);
v_cnstrsOf_1697_ = lean_ctor_get(v_s_1692_, 4);
v_sources_1698_ = lean_ctor_get(v_s_1692_, 5);
v_targets_1699_ = lean_ctor_get(v_s_1692_, 6);
v_proofs_1700_ = lean_ctor_get(v_s_1692_, 7);
v_isSharedCheck_1708_ = !lean_is_exclusive(v_s_1692_);
if (v_isSharedCheck_1708_ == 0)
{
lean_object* v_unused_1709_; 
v_unused_1709_ = lean_ctor_get(v_s_1692_, 8);
lean_dec(v_unused_1709_);
v___x_1702_ = v_s_1692_;
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
lean_inc(v_id_1693_);
lean_dec(v_s_1692_);
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
lean_ctor_set(v___x_1702_, 8, v___x_1704_);
v___x_1706_ = v___x_1702_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v_id_1693_);
lean_ctor_set(v_reuseFailAlloc_1707_, 1, v_nodes_1694_);
lean_ctor_set(v_reuseFailAlloc_1707_, 2, v_nodeMap_1695_);
lean_ctor_set(v_reuseFailAlloc_1707_, 3, v_cnstrs_1696_);
lean_ctor_set(v_reuseFailAlloc_1707_, 4, v_cnstrsOf_1697_);
lean_ctor_set(v_reuseFailAlloc_1707_, 5, v_sources_1698_);
lean_ctor_set(v_reuseFailAlloc_1707_, 6, v_targets_1699_);
lean_ctor_set(v_reuseFailAlloc_1707_, 7, v_proofs_1700_);
lean_ctor_set(v_reuseFailAlloc_1707_, 8, v___x_1704_);
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
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg(lean_object* v_as_x27_1719_, lean_object* v_b_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_){
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
lean_dec_ref_known(v___x_1743_, 1);
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
lean_dec_ref_known(v___x_1751_, 1);
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
v___x_1755_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_u_1753_, v___y_1721_, v___y_1722_, v___y_1730_);
if (lean_obj_tag(v___x_1755_) == 0)
{
lean_object* v_a_1756_; lean_object* v___x_1757_; 
v_a_1756_ = lean_ctor_get(v___x_1755_, 0);
lean_inc(v_a_1756_);
lean_dec_ref_known(v___x_1755_, 1);
v___x_1757_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_v_1754_, v___y_1721_, v___y_1722_, v___y_1730_);
if (lean_obj_tag(v___x_1757_) == 0)
{
lean_object* v_a_1758_; lean_object* v___y_1760_; lean_object* v___y_1761_; lean_object* v___y_1762_; lean_object* v___y_1763_; lean_object* v___y_1764_; lean_object* v___y_1765_; lean_object* v___y_1766_; lean_object* v___y_1767_; lean_object* v___y_1768_; lean_object* v___y_1769_; lean_object* v___y_1770_; lean_object* v___y_1771_; lean_object* v___y_1772_; lean_object* v___y_1773_; lean_object* v___y_1774_; lean_object* v___y_1775_; lean_object* v___y_1848_; lean_object* v___y_1849_; lean_object* v___y_1850_; lean_object* v___y_1851_; lean_object* v___y_1852_; lean_object* v___y_1853_; lean_object* v___y_1854_; lean_object* v___y_1855_; lean_object* v___y_1856_; lean_object* v___y_1857_; lean_object* v___y_1858_; lean_object* v___y_1892_; lean_object* v___x_1946_; 
v_a_1758_ = lean_ctor_get(v___x_1757_, 0);
lean_inc(v_a_1758_);
lean_dec_ref_known(v___x_1757_, 1);
v___x_1946_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_a_1756_, v___y_1722_);
if (lean_obj_tag(v___x_1946_) == 0)
{
lean_object* v_a_1947_; uint8_t v___x_1948_; 
v_a_1947_ = lean_ctor_get(v___x_1946_, 0);
v___x_1948_ = lean_unbox(v_a_1947_);
if (v___x_1948_ == 0)
{
v___y_1892_ = v___x_1946_;
goto v___jp_1891_;
}
else
{
lean_object* v___x_1949_; 
lean_dec_ref_known(v___x_1946_, 1);
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
lean_dec_ref_known(v___y_1775_, 1);
v___x_1777_ = lean_unbox(v_a_1776_);
lean_dec(v_a_1776_);
if (v___x_1777_ == 0)
{
lean_dec_ref(v___y_1773_);
lean_dec_ref(v___y_1769_);
lean_dec_ref(v___y_1765_);
lean_dec_ref(v___y_1761_);
lean_dec(v_a_1758_);
lean_dec(v_a_1756_);
v_as_x27_1719_ = v_tail_1735_;
v_b_1720_ = v___x_1736_;
goto _start;
}
else
{
lean_object* v___x_1779_; 
v___x_1779_ = l_Lean_Meta_Grind_isEqv___redArg(v___y_1773_, v___y_1761_, v___y_1771_);
if (lean_obj_tag(v___x_1779_) == 0)
{
lean_object* v_a_1780_; uint8_t v___x_1781_; 
v_a_1780_ = lean_ctor_get(v___x_1779_, 0);
lean_inc(v_a_1780_);
lean_dec_ref_known(v___x_1779_, 1);
v___x_1781_ = lean_unbox(v_a_1780_);
if (v___x_1781_ == 0)
{
lean_object* v___x_1782_; 
v___x_1782_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath(v_u_1753_, v_v_1754_, v___y_1764_, v___y_1771_, v___y_1772_, v___y_1760_, v___y_1762_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1774_, v___y_1770_, v___y_1763_);
if (lean_obj_tag(v___x_1782_) == 0)
{
lean_object* v_a_1783_; lean_object* v___x_1784_; 
v_a_1783_ = lean_ctor_get(v___x_1782_, 0);
lean_inc(v_a_1783_);
lean_dec_ref_known(v___x_1782_, 1);
v___x_1784_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath(v_v_1754_, v_u_1753_, v___y_1764_, v___y_1771_, v___y_1772_, v___y_1760_, v___y_1762_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1774_, v___y_1770_, v___y_1763_);
if (lean_obj_tag(v___x_1784_) == 0)
{
lean_object* v_a_1785_; lean_object* v___x_1786_; 
v_a_1785_ = lean_ctor_get(v___x_1784_, 0);
lean_inc(v_a_1785_);
lean_dec_ref_known(v___x_1784_, 1);
lean_inc(v_a_1758_);
lean_inc(v_a_1756_);
v___x_1786_ = l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLe(v_a_1756_, v_a_1758_, v_a_1783_, v_a_1785_, v___y_1764_, v___y_1771_, v___y_1772_, v___y_1760_, v___y_1762_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1774_, v___y_1770_, v___y_1763_);
if (lean_obj_tag(v___x_1786_) == 0)
{
lean_object* v_a_1787_; lean_object* v___x_1788_; 
v_a_1787_ = lean_ctor_get(v___x_1786_, 0);
lean_inc(v_a_1787_);
lean_dec_ref_known(v___x_1786_, 1);
lean_inc(v___y_1763_);
lean_inc_ref(v___y_1770_);
lean_inc(v___y_1774_);
lean_inc_ref(v___y_1768_);
lean_inc(v_a_1756_);
v___x_1788_ = lean_infer_type(v_a_1756_, v___y_1768_, v___y_1774_, v___y_1770_, v___y_1763_);
if (lean_obj_tag(v___x_1788_) == 0)
{
lean_object* v_a_1789_; lean_object* v___x_1790_; uint8_t v___x_1791_; 
v_a_1789_ = lean_ctor_get(v___x_1788_, 0);
lean_inc(v_a_1789_);
lean_dec_ref_known(v___x_1788_, 1);
v___x_1790_ = l_Lean_Int_mkType;
v___x_1791_ = lean_expr_eqv(v_a_1789_, v___x_1790_);
lean_dec(v_a_1789_);
if (v___x_1791_ == 0)
{
lean_dec(v_a_1787_);
lean_dec(v_a_1780_);
lean_dec_ref(v___y_1773_);
lean_dec_ref(v___y_1769_);
lean_dec_ref(v___y_1765_);
lean_dec_ref(v___y_1761_);
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
lean_inc_ref(v___y_1761_);
lean_inc_ref(v___y_1773_);
v___x_1794_ = l_Lean_mkApp7(v___x_1793_, v___y_1773_, v___y_1761_, v_a_1756_, v_a_1758_, v___y_1769_, v___y_1765_, v_a_1787_);
v___x_1795_ = lean_unbox(v_a_1780_);
lean_dec(v_a_1780_);
v___x_1796_ = l_Lean_Meta_Grind_pushEqCore___redArg(v___y_1773_, v___y_1761_, v___x_1794_, v___x_1795_, v___y_1771_, v___y_1760_, v___y_1768_, v___y_1774_, v___y_1770_, v___y_1763_);
if (lean_obj_tag(v___x_1796_) == 0)
{
lean_dec_ref_known(v___x_1796_, 1);
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
lean_dec_ref(v___y_1773_);
lean_dec_ref(v___y_1769_);
lean_dec_ref(v___y_1765_);
lean_dec_ref(v___y_1761_);
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
lean_dec_ref(v___y_1773_);
lean_dec_ref(v___y_1769_);
lean_dec_ref(v___y_1765_);
lean_dec_ref(v___y_1761_);
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
lean_dec_ref(v___y_1773_);
lean_dec_ref(v___y_1769_);
lean_dec_ref(v___y_1765_);
lean_dec_ref(v___y_1761_);
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
lean_dec_ref(v___y_1773_);
lean_dec_ref(v___y_1769_);
lean_dec_ref(v___y_1765_);
lean_dec_ref(v___y_1761_);
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
lean_dec_ref(v___y_1773_);
lean_dec_ref(v___y_1769_);
lean_dec_ref(v___y_1765_);
lean_dec_ref(v___y_1761_);
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
lean_dec_ref(v___y_1773_);
lean_dec_ref(v___y_1769_);
lean_dec_ref(v___y_1765_);
lean_dec_ref(v___y_1761_);
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
lean_dec_ref(v___y_1773_);
lean_dec_ref(v___y_1769_);
lean_dec_ref(v___y_1765_);
lean_dec_ref(v___y_1761_);
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
lean_dec_ref_known(v___x_1859_, 1);
if (lean_obj_tag(v_a_1860_) == 1)
{
lean_object* v_val_1861_; lean_object* v_fst_1862_; lean_object* v_snd_1863_; lean_object* v___x_1864_; 
v_val_1861_ = lean_ctor_get(v_a_1860_, 0);
lean_inc(v_val_1861_);
lean_dec_ref_known(v_a_1860_, 1);
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
lean_dec_ref_known(v___x_1864_, 1);
if (lean_obj_tag(v_a_1865_) == 1)
{
lean_object* v_val_1866_; lean_object* v_fst_1867_; lean_object* v_snd_1868_; lean_object* v___x_1869_; 
v_val_1866_ = lean_ctor_get(v_a_1865_, 0);
lean_inc(v_val_1866_);
lean_dec_ref_known(v_a_1865_, 1);
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
v___x_1871_ = lean_unbox(v_a_1870_);
if (v___x_1871_ == 0)
{
v___y_1760_ = v___y_1851_;
v___y_1761_ = v_fst_1867_;
v___y_1762_ = v___y_1852_;
v___y_1763_ = v___y_1858_;
v___y_1764_ = v___y_1848_;
v___y_1765_ = v_snd_1868_;
v___y_1766_ = v___y_1853_;
v___y_1767_ = v___y_1854_;
v___y_1768_ = v___y_1855_;
v___y_1769_ = v_snd_1863_;
v___y_1770_ = v___y_1857_;
v___y_1771_ = v___y_1849_;
v___y_1772_ = v___y_1850_;
v___y_1773_ = v_fst_1862_;
v___y_1774_ = v___y_1856_;
v___y_1775_ = v___x_1869_;
goto v___jp_1759_;
}
else
{
lean_object* v___x_1872_; 
lean_dec_ref_known(v___x_1869_, 1);
v___x_1872_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_fst_1867_, v___y_1849_);
v___y_1760_ = v___y_1851_;
v___y_1761_ = v_fst_1867_;
v___y_1762_ = v___y_1852_;
v___y_1763_ = v___y_1858_;
v___y_1764_ = v___y_1848_;
v___y_1765_ = v_snd_1868_;
v___y_1766_ = v___y_1853_;
v___y_1767_ = v___y_1854_;
v___y_1768_ = v___y_1855_;
v___y_1769_ = v_snd_1863_;
v___y_1770_ = v___y_1857_;
v___y_1771_ = v___y_1849_;
v___y_1772_ = v___y_1850_;
v___y_1773_ = v_fst_1862_;
v___y_1774_ = v___y_1856_;
v___y_1775_ = v___x_1872_;
goto v___jp_1759_;
}
}
else
{
v___y_1760_ = v___y_1851_;
v___y_1761_ = v_fst_1867_;
v___y_1762_ = v___y_1852_;
v___y_1763_ = v___y_1858_;
v___y_1764_ = v___y_1848_;
v___y_1765_ = v_snd_1868_;
v___y_1766_ = v___y_1853_;
v___y_1767_ = v___y_1854_;
v___y_1768_ = v___y_1855_;
v___y_1769_ = v_snd_1863_;
v___y_1770_ = v___y_1857_;
v___y_1771_ = v___y_1849_;
v___y_1772_ = v___y_1850_;
v___y_1773_ = v_fst_1862_;
v___y_1774_ = v___y_1856_;
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
lean_dec_ref_known(v___y_1892_, 1);
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
lean_dec_ref_known(v___x_1895_, 1);
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
lean_dec_ref_known(v___x_1898_, 1);
v___x_1900_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath(v_v_1754_, v_u_1753_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_);
if (lean_obj_tag(v___x_1900_) == 0)
{
lean_object* v_a_1901_; lean_object* v___x_1902_; 
v_a_1901_ = lean_ctor_get(v___x_1900_, 0);
lean_inc(v_a_1901_);
lean_dec_ref_known(v___x_1900_, 1);
lean_inc(v_a_1758_);
lean_inc(v_a_1756_);
v___x_1902_ = l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLe(v_a_1756_, v_a_1758_, v_a_1899_, v_a_1901_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_);
if (lean_obj_tag(v___x_1902_) == 0)
{
lean_object* v_a_1903_; uint8_t v___x_1904_; lean_object* v___x_1905_; 
v_a_1903_ = lean_ctor_get(v___x_1902_, 0);
lean_inc(v_a_1903_);
lean_dec_ref_known(v___x_1902_, 1);
v___x_1904_ = lean_unbox(v_a_1896_);
lean_dec(v_a_1896_);
lean_inc(v_a_1758_);
lean_inc(v_a_1756_);
v___x_1905_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_a_1756_, v_a_1758_, v_a_1903_, v___x_1904_, v___y_1722_, v___y_1724_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_);
if (lean_obj_tag(v___x_1905_) == 0)
{
lean_dec_ref_known(v___x_1905_, 1);
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
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_x27_1719_ = stack[0].m_obj;
lean_object* v_b_1720_ = stack[1].m_obj;
lean_object* v___y_1721_ = stack[2].m_obj;
lean_object* v___y_1722_ = stack[3].m_obj;
lean_object* v___y_1723_ = stack[4].m_obj;
lean_object* v___y_1724_ = stack[5].m_obj;
lean_object* v___y_1725_ = stack[6].m_obj;
lean_object* v___y_1726_ = stack[7].m_obj;
lean_object* v___y_1727_ = stack[8].m_obj;
lean_object* v___y_1728_ = stack[9].m_obj;
lean_object* v___y_1729_ = stack[10].m_obj;
lean_object* v___y_1730_ = stack[11].m_obj;
lean_object* v___y_1731_ = stack[12].m_obj;
lean_object* v_res_1966_;
v_res_1966_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg(v_as_x27_1719_, v_b_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_);
stack->m_obj
 = v_res_1966_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg___boxed(lean_object* v_as_x27_1967_, lean_object* v_b_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_){
_start:
{
lean_object* v_res_1981_; 
v_res_1981_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg(v_as_x27_1967_, v_b_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_);
lean_dec(v___y_1979_);
lean_dec_ref(v___y_1978_);
lean_dec(v___y_1977_);
lean_dec_ref(v___y_1976_);
lean_dec(v___y_1975_);
lean_dec_ref(v___y_1974_);
lean_dec(v___y_1973_);
lean_dec_ref(v___y_1972_);
lean_dec(v___y_1971_);
lean_dec(v___y_1970_);
lean_dec(v___y_1969_);
lean_dec(v_as_x27_1967_);
return v_res_1981_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending(lean_object* v_a_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_){
_start:
{
lean_object* v___f_1995_; lean_object* v___x_1996_; 
v___f_1995_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending___closed__0));
v___x_1996_ = l_Lean_Meta_Grind_Order_getStruct___redArg(v_a_1983_, v_a_1984_, v_a_1992_);
if (lean_obj_tag(v___x_1996_) == 0)
{
lean_object* v_a_1997_; lean_object* v_propagate_1998_; lean_object* v___x_1999_; 
v_a_1997_ = lean_ctor_get(v___x_1996_, 0);
lean_inc(v_a_1997_);
lean_dec_ref_known(v___x_1996_, 1);
v_propagate_1998_ = lean_ctor_get(v_a_1997_, 8);
lean_inc(v_propagate_1998_);
lean_dec(v_a_1997_);
v___x_1999_ = l_Lean_Meta_Grind_Order_modifyStruct___redArg(v___f_1995_, v_a_1983_, v_a_1984_);
if (lean_obj_tag(v___x_1999_) == 0)
{
lean_object* v___x_2000_; lean_object* v___x_2001_; 
lean_dec_ref_known(v___x_1999_, 1);
v___x_2000_ = lean_box(0);
v___x_2001_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg(v_propagate_1998_, v___x_2000_, v_a_1983_, v_a_1984_, v_a_1985_, v_a_1986_, v_a_1987_, v_a_1988_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_);
lean_dec(v_propagate_1998_);
if (lean_obj_tag(v___x_2001_) == 0)
{
lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2008_; 
v_isSharedCheck_2008_ = !lean_is_exclusive(v___x_2001_);
if (v_isSharedCheck_2008_ == 0)
{
lean_object* v_unused_2009_; 
v_unused_2009_ = lean_ctor_get(v___x_2001_, 0);
lean_dec(v_unused_2009_);
v___x_2003_ = v___x_2001_;
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
else
{
lean_dec(v___x_2001_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2006_; 
if (v_isShared_2004_ == 0)
{
lean_ctor_set(v___x_2003_, 0, v___x_2000_);
v___x_2006_ = v___x_2003_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v___x_2000_);
v___x_2006_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
return v___x_2006_;
}
}
}
else
{
return v___x_2001_;
}
}
else
{
lean_dec(v_propagate_1998_);
return v___x_1999_;
}
}
else
{
lean_object* v_a_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2017_; 
v_a_2010_ = lean_ctor_get(v___x_1996_, 0);
v_isSharedCheck_2017_ = !lean_is_exclusive(v___x_1996_);
if (v_isSharedCheck_2017_ == 0)
{
v___x_2012_ = v___x_1996_;
v_isShared_2013_ = v_isSharedCheck_2017_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_a_2010_);
lean_dec(v___x_1996_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2017_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v___x_2015_; 
if (v_isShared_2013_ == 0)
{
v___x_2015_ = v___x_2012_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v_a_2010_);
v___x_2015_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
return v___x_2015_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1983_ = stack[0].m_obj;
lean_object* v_a_1984_ = stack[1].m_obj;
lean_object* v_a_1985_ = stack[2].m_obj;
lean_object* v_a_1986_ = stack[3].m_obj;
lean_object* v_a_1987_ = stack[4].m_obj;
lean_object* v_a_1988_ = stack[5].m_obj;
lean_object* v_a_1989_ = stack[6].m_obj;
lean_object* v_a_1990_ = stack[7].m_obj;
lean_object* v_a_1991_ = stack[8].m_obj;
lean_object* v_a_1992_ = stack[9].m_obj;
lean_object* v_a_1993_ = stack[10].m_obj;
lean_object* v_res_2018_;
v_res_2018_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending(v_a_1983_, v_a_1984_, v_a_1985_, v_a_1986_, v_a_1987_, v_a_1988_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_);
stack->m_obj
 = v_res_2018_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending___boxed(lean_object* v_a_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_, lean_object* v_a_2023_, lean_object* v_a_2024_, lean_object* v_a_2025_, lean_object* v_a_2026_, lean_object* v_a_2027_, lean_object* v_a_2028_, lean_object* v_a_2029_, lean_object* v_a_2030_){
_start:
{
lean_object* v_res_2031_; 
v_res_2031_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending(v_a_2019_, v_a_2020_, v_a_2021_, v_a_2022_, v_a_2023_, v_a_2024_, v_a_2025_, v_a_2026_, v_a_2027_, v_a_2028_, v_a_2029_);
lean_dec(v_a_2029_);
lean_dec_ref(v_a_2028_);
lean_dec(v_a_2027_);
lean_dec_ref(v_a_2026_);
lean_dec(v_a_2025_);
lean_dec_ref(v_a_2024_);
lean_dec(v_a_2023_);
lean_dec_ref(v_a_2022_);
lean_dec(v_a_2021_);
lean_dec(v_a_2020_);
lean_dec(v_a_2019_);
return v_res_2031_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0(lean_object* v_as_2032_, lean_object* v_as_x27_2033_, lean_object* v_b_2034_, lean_object* v_a_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_){
_start:
{
lean_object* v___x_2048_; 
v___x_2048_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg(v_as_x27_2033_, v_b_2034_, v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_);
return v___x_2048_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2032_ = stack[0].m_obj;
lean_object* v_as_x27_2033_ = stack[1].m_obj;
lean_object* v_b_2034_ = stack[2].m_obj;
lean_object* v___y_2036_ = stack[4].m_obj;
lean_object* v___y_2037_ = stack[5].m_obj;
lean_object* v___y_2038_ = stack[6].m_obj;
lean_object* v___y_2039_ = stack[7].m_obj;
lean_object* v___y_2040_ = stack[8].m_obj;
lean_object* v___y_2041_ = stack[9].m_obj;
lean_object* v___y_2042_ = stack[10].m_obj;
lean_object* v___y_2043_ = stack[11].m_obj;
lean_object* v___y_2044_ = stack[12].m_obj;
lean_object* v___y_2045_ = stack[13].m_obj;
lean_object* v___y_2046_ = stack[14].m_obj;
lean_object* v_res_2049_;
v_res_2049_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0(v_as_2032_, v_as_x27_2033_, v_b_2034_, lean_box(0), v___y_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_);
stack->m_obj
 = v_res_2049_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___boxed(lean_object* v_as_2050_, lean_object* v_as_x27_2051_, lean_object* v_b_2052_, lean_object* v_a_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_){
_start:
{
lean_object* v_res_2066_; 
v_res_2066_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0(v_as_2050_, v_as_x27_2051_, v_b_2052_, v_a_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_, v___y_2064_);
lean_dec(v___y_2064_);
lean_dec_ref(v___y_2063_);
lean_dec(v___y_2062_);
lean_dec_ref(v___y_2061_);
lean_dec(v___y_2060_);
lean_dec_ref(v___y_2059_);
lean_dec(v___y_2058_);
lean_dec_ref(v___y_2057_);
lean_dec(v___y_2056_);
lean_dec(v___y_2055_);
lean_dec(v___y_2054_);
lean_dec(v_as_x27_2051_);
lean_dec(v_as_2050_);
return v_res_2066_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue___redArg(lean_object* v_e_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_, lean_object* v_a_2073_){
_start:
{
lean_object* v___x_2075_; 
v___x_2075_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_2068_, v_a_2072_);
if (lean_obj_tag(v___x_2075_) == 0)
{
lean_object* v_a_2076_; lean_object* v_termMapInv_2077_; lean_object* v___x_2078_; 
v_a_2076_ = lean_ctor_get(v___x_2075_, 0);
lean_inc(v_a_2076_);
lean_dec_ref_known(v___x_2075_, 1);
v_termMapInv_2077_ = lean_ctor_get(v_a_2076_, 4);
lean_inc_ref(v_termMapInv_2077_);
lean_dec(v_a_2076_);
v___x_2078_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMapInv_2077_, v_e_2067_);
lean_dec_ref(v_termMapInv_2077_);
if (lean_obj_tag(v___x_2078_) == 1)
{
lean_object* v_val_2079_; lean_object* v_fst_2080_; lean_object* v___x_2081_; 
lean_dec_ref(v_e_2067_);
v_val_2079_ = lean_ctor_get(v___x_2078_, 0);
lean_inc(v_val_2079_);
lean_dec_ref_known(v___x_2078_, 1);
v_fst_2080_ = lean_ctor_get(v_val_2079_, 0);
lean_inc(v_fst_2080_);
lean_dec(v_val_2079_);
v___x_2081_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_fst_2080_, v_a_2068_);
if (lean_obj_tag(v___x_2081_) == 0)
{
lean_object* v_a_2082_; uint8_t v___x_2083_; 
v_a_2082_ = lean_ctor_get(v___x_2081_, 0);
v___x_2083_ = lean_unbox(v_a_2082_);
if (v___x_2083_ == 0)
{
lean_dec(v_fst_2080_);
return v___x_2081_;
}
else
{
lean_object* v___x_2084_; 
lean_dec_ref_known(v___x_2081_, 1);
v___x_2084_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_fst_2080_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_, v_a_2073_);
return v___x_2084_;
}
}
else
{
lean_dec(v_fst_2080_);
return v___x_2081_;
}
}
else
{
lean_object* v___x_2085_; 
lean_dec(v___x_2078_);
v___x_2085_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_e_2067_, v_a_2068_);
if (lean_obj_tag(v___x_2085_) == 0)
{
lean_object* v_a_2086_; uint8_t v___x_2087_; 
v_a_2086_ = lean_ctor_get(v___x_2085_, 0);
v___x_2087_ = lean_unbox(v_a_2086_);
if (v___x_2087_ == 0)
{
lean_dec_ref(v_e_2067_);
return v___x_2085_;
}
else
{
lean_object* v___x_2088_; 
lean_dec_ref_known(v___x_2085_, 1);
v___x_2088_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_2067_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_, v_a_2073_);
return v___x_2088_;
}
}
else
{
lean_dec_ref(v_e_2067_);
return v___x_2085_;
}
}
}
else
{
lean_object* v_a_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2096_; 
lean_dec_ref(v_e_2067_);
v_a_2089_ = lean_ctor_get(v___x_2075_, 0);
v_isSharedCheck_2096_ = !lean_is_exclusive(v___x_2075_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2091_ = v___x_2075_;
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_a_2089_);
lean_dec(v___x_2075_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v___x_2094_; 
if (v_isShared_2092_ == 0)
{
v___x_2094_ = v___x_2091_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v_a_2089_);
v___x_2094_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
return v___x_2094_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2067_ = stack[0].m_obj;
lean_object* v_a_2068_ = stack[1].m_obj;
lean_object* v_a_2069_ = stack[2].m_obj;
lean_object* v_a_2070_ = stack[3].m_obj;
lean_object* v_a_2071_ = stack[4].m_obj;
lean_object* v_a_2072_ = stack[5].m_obj;
lean_object* v_a_2073_ = stack[6].m_obj;
lean_object* v_res_2097_;
v_res_2097_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue___redArg(v_e_2067_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_, v_a_2073_);
stack->m_obj
 = v_res_2097_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue___redArg___boxed(lean_object* v_e_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_){
_start:
{
lean_object* v_res_2106_; 
v_res_2106_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue___redArg(v_e_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_, v_a_2103_, v_a_2104_);
lean_dec(v_a_2104_);
lean_dec_ref(v_a_2103_);
lean_dec(v_a_2102_);
lean_dec_ref(v_a_2101_);
lean_dec_ref(v_a_2100_);
lean_dec(v_a_2099_);
return v_res_2106_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue(lean_object* v_e_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_){
_start:
{
lean_object* v___x_2120_; 
v___x_2120_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue___redArg(v_e_2107_, v_a_2109_, v_a_2113_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_);
return v___x_2120_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2107_ = stack[0].m_obj;
lean_object* v_a_2108_ = stack[1].m_obj;
lean_object* v_a_2109_ = stack[2].m_obj;
lean_object* v_a_2110_ = stack[3].m_obj;
lean_object* v_a_2111_ = stack[4].m_obj;
lean_object* v_a_2112_ = stack[5].m_obj;
lean_object* v_a_2113_ = stack[6].m_obj;
lean_object* v_a_2114_ = stack[7].m_obj;
lean_object* v_a_2115_ = stack[8].m_obj;
lean_object* v_a_2116_ = stack[9].m_obj;
lean_object* v_a_2117_ = stack[10].m_obj;
lean_object* v_a_2118_ = stack[11].m_obj;
lean_object* v_res_2121_;
v_res_2121_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue(v_e_2107_, v_a_2108_, v_a_2109_, v_a_2110_, v_a_2111_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_);
stack->m_obj
 = v_res_2121_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue___boxed(lean_object* v_e_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_){
_start:
{
lean_object* v_res_2135_; 
v_res_2135_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue(v_e_2122_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_, v_a_2130_, v_a_2131_, v_a_2132_, v_a_2133_);
lean_dec(v_a_2133_);
lean_dec_ref(v_a_2132_);
lean_dec(v_a_2131_);
lean_dec_ref(v_a_2130_);
lean_dec(v_a_2129_);
lean_dec_ref(v_a_2128_);
lean_dec(v_a_2127_);
lean_dec_ref(v_a_2126_);
lean_dec(v_a_2125_);
lean_dec(v_a_2124_);
lean_dec(v_a_2123_);
return v_res_2135_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__2(void){
_start:
{
lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; 
v___x_2142_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__1));
v___x_2143_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__6));
v___x_2144_ = l_Lean_Name_append(v___x_2143_, v___x_2142_);
return v___x_2144_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4(void){
_start:
{
lean_object* v___x_2146_; lean_object* v___x_2147_; 
v___x_2146_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__3));
v___x_2147_ = l_Lean_stringToMessageData(v___x_2146_);
return v___x_2147_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue(lean_object* v_u_2149_, lean_object* v_v_2150_, lean_object* v_k_2151_, lean_object* v_c_2152_, lean_object* v_e_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_){
_start:
{
lean_object* v___x_2166_; 
lean_inc_ref(v_e_2153_);
v___x_2166_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue___redArg(v_e_2153_, v_a_2155_, v_a_2159_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_);
if (lean_obj_tag(v___x_2166_) == 0)
{
lean_object* v_a_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2266_; 
v_a_2167_ = lean_ctor_get(v___x_2166_, 0);
v_isSharedCheck_2266_ = !lean_is_exclusive(v___x_2166_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_2169_ = v___x_2166_;
v_isShared_2170_ = v_isSharedCheck_2266_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_a_2167_);
lean_dec(v___x_2166_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2266_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
uint8_t v___x_2171_; 
v___x_2171_ = lean_unbox(v_a_2167_);
lean_dec(v_a_2167_);
if (v___x_2171_ == 0)
{
lean_object* v_toCold_2172_; lean_object* v_options_2173_; lean_object* v_inheritedTraceOptions_2174_; uint8_t v_hasTrace_2175_; lean_object* v___x_2176_; lean_object* v___y_2178_; lean_object* v___y_2179_; lean_object* v___y_2180_; lean_object* v___y_2181_; lean_object* v___y_2182_; lean_object* v___y_2183_; lean_object* v___y_2184_; lean_object* v___y_2185_; lean_object* v___y_2186_; lean_object* v___y_2187_; lean_object* v___y_2188_; 
v_toCold_2172_ = lean_ctor_get(v_a_2163_, 0);
v_options_2173_ = lean_ctor_get(v_toCold_2172_, 2);
v_inheritedTraceOptions_2174_ = lean_ctor_get(v_toCold_2172_, 11);
v_hasTrace_2175_ = lean_ctor_get_uint8(v_options_2173_, sizeof(void*)*1);
v___x_2176_ = l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(v_c_2152_);
if (v_hasTrace_2175_ == 0)
{
v___y_2178_ = v_a_2154_;
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
goto v___jp_2177_;
}
else
{
lean_object* v___x_2196_; lean_object* v___x_2197_; uint8_t v___x_2198_; 
v___x_2196_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__1));
v___x_2197_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__2, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__2);
v___x_2198_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2174_, v_options_2173_, v___x_2197_);
if (v___x_2198_ == 0)
{
v___y_2178_ = v_a_2154_;
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
goto v___jp_2177_;
}
else
{
lean_object* v___x_2199_; 
v___x_2199_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_u_2149_, v_a_2154_, v_a_2155_, v_a_2163_);
if (lean_obj_tag(v___x_2199_) == 0)
{
lean_object* v_a_2200_; lean_object* v___x_2201_; 
v_a_2200_ = lean_ctor_get(v___x_2199_, 0);
lean_inc(v_a_2200_);
lean_dec_ref_known(v___x_2199_, 1);
v___x_2201_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_v_2150_, v_a_2154_, v_a_2155_, v_a_2163_);
if (lean_obj_tag(v___x_2201_) == 0)
{
lean_object* v_a_2202_; lean_object* v___x_2203_; 
v_a_2202_ = lean_ctor_get(v___x_2201_, 0);
lean_inc(v_a_2202_);
lean_dec_ref_known(v___x_2201_, 1);
v___x_2203_ = l_Lean_Meta_Grind_Order_Cnstr_pp___redArg(v_c_2152_, v_a_2154_, v_a_2155_, v_a_2163_);
if (lean_obj_tag(v___x_2203_) == 0)
{
lean_object* v_a_2204_; lean_object* v_k_2205_; uint8_t v_strict_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___y_2210_; lean_object* v___y_2211_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___y_2223_; 
v_a_2204_ = lean_ctor_get(v___x_2203_, 0);
lean_inc(v_a_2204_);
lean_dec_ref_known(v___x_2203_, 1);
v_k_2205_ = lean_ctor_get(v_k_2151_, 0);
v_strict_2206_ = lean_ctor_get_uint8(v_k_2151_, sizeof(void*)*1);
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
v___x_2217_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(v___x_2196_, v___x_2216_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_);
if (lean_obj_tag(v___x_2217_) == 0)
{
lean_dec_ref_known(v___x_2217_, 1);
v___y_2178_ = v_a_2154_;
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
goto v___jp_2177_;
}
else
{
lean_dec_ref(v___x_2176_);
lean_del_object(v___x_2169_);
lean_dec_ref(v_e_2153_);
lean_dec_ref(v_c_2152_);
lean_dec_ref(v_k_2151_);
lean_dec(v_v_2150_);
lean_dec(v_u_2149_);
return v___x_2217_;
}
}
v___jp_2222_:
{
lean_object* v_k_2224_; uint8_t v_strict_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; 
v_k_2224_ = lean_ctor_get(v___x_2176_, 0);
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
v___y_2210_ = v___x_2229_;
v___y_2211_ = v___x_2230_;
goto v___jp_2209_;
}
else
{
lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; 
v___x_2231_ = l_Int_repr(v_k_2224_);
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
lean_del_object(v___x_2169_);
lean_dec_ref(v_e_2153_);
lean_dec_ref(v_c_2152_);
lean_dec_ref(v_k_2151_);
lean_dec(v_v_2150_);
lean_dec(v_u_2149_);
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
lean_del_object(v___x_2169_);
lean_dec_ref(v_e_2153_);
lean_dec_ref(v_c_2152_);
lean_dec_ref(v_k_2151_);
lean_dec(v_v_2150_);
lean_dec(v_u_2149_);
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
lean_del_object(v___x_2169_);
lean_dec_ref(v_e_2153_);
lean_dec_ref(v_c_2152_);
lean_dec_ref(v_k_2151_);
lean_dec(v_v_2150_);
lean_dec(v_u_2149_);
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
v___jp_2177_:
{
uint8_t v___x_2189_; 
v___x_2189_ = l_Lean_Meta_Grind_Order_instDecidableLEWeight(v_k_2151_, v___x_2176_);
if (v___x_2189_ == 0)
{
lean_object* v___x_2190_; lean_object* v___x_2192_; 
lean_dec_ref(v___x_2176_);
lean_dec_ref(v_e_2153_);
lean_dec_ref(v_c_2152_);
lean_dec_ref(v_k_2151_);
lean_dec(v_v_2150_);
lean_dec(v_u_2149_);
v___x_2190_ = lean_box(0);
if (v_isShared_2170_ == 0)
{
lean_ctor_set(v___x_2169_, 0, v___x_2190_);
v___x_2192_ = v___x_2169_;
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
lean_del_object(v___x_2169_);
v___x_2194_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2194_, 0, v_c_2152_);
lean_ctor_set(v___x_2194_, 1, v_e_2153_);
lean_ctor_set(v___x_2194_, 2, v_u_2149_);
lean_ctor_set(v___x_2194_, 3, v_v_2150_);
lean_ctor_set(v___x_2194_, 4, v_k_2151_);
lean_ctor_set(v___x_2194_, 5, v___x_2176_);
v___x_2195_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate(v___x_2194_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_);
return v___x_2195_;
}
}
}
else
{
lean_object* v___x_2262_; lean_object* v___x_2264_; 
lean_dec_ref(v_e_2153_);
lean_dec_ref(v_c_2152_);
lean_dec_ref(v_k_2151_);
lean_dec(v_v_2150_);
lean_dec(v_u_2149_);
v___x_2262_ = lean_box(0);
if (v_isShared_2170_ == 0)
{
lean_ctor_set(v___x_2169_, 0, v___x_2262_);
v___x_2264_ = v___x_2169_;
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
lean_dec_ref(v_e_2153_);
lean_dec_ref(v_c_2152_);
lean_dec_ref(v_k_2151_);
lean_dec(v_v_2150_);
lean_dec(v_u_2149_);
v_a_2267_ = lean_ctor_get(v___x_2166_, 0);
v_isSharedCheck_2274_ = !lean_is_exclusive(v___x_2166_);
if (v_isSharedCheck_2274_ == 0)
{
v___x_2269_ = v___x_2166_;
v_isShared_2270_ = v_isSharedCheck_2274_;
goto v_resetjp_2268_;
}
else
{
lean_inc(v_a_2267_);
lean_dec(v___x_2166_);
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
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_2149_ = stack[0].m_obj;
lean_object* v_v_2150_ = stack[1].m_obj;
lean_object* v_k_2151_ = stack[2].m_obj;
lean_object* v_c_2152_ = stack[3].m_obj;
lean_object* v_e_2153_ = stack[4].m_obj;
lean_object* v_a_2154_ = stack[5].m_obj;
lean_object* v_a_2155_ = stack[6].m_obj;
lean_object* v_a_2156_ = stack[7].m_obj;
lean_object* v_a_2157_ = stack[8].m_obj;
lean_object* v_a_2158_ = stack[9].m_obj;
lean_object* v_a_2159_ = stack[10].m_obj;
lean_object* v_a_2160_ = stack[11].m_obj;
lean_object* v_a_2161_ = stack[12].m_obj;
lean_object* v_a_2162_ = stack[13].m_obj;
lean_object* v_a_2163_ = stack[14].m_obj;
lean_object* v_a_2164_ = stack[15].m_obj;
lean_object* v_res_2275_;
v_res_2275_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue(v_u_2149_, v_v_2150_, v_k_2151_, v_c_2152_, v_e_2153_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_);
stack->m_obj
 = v_res_2275_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___boxed(lean_object** _args){
lean_object* v_u_2276_ = _args[0];
lean_object* v_v_2277_ = _args[1];
lean_object* v_k_2278_ = _args[2];
lean_object* v_c_2279_ = _args[3];
lean_object* v_e_2280_ = _args[4];
lean_object* v_a_2281_ = _args[5];
lean_object* v_a_2282_ = _args[6];
lean_object* v_a_2283_ = _args[7];
lean_object* v_a_2284_ = _args[8];
lean_object* v_a_2285_ = _args[9];
lean_object* v_a_2286_ = _args[10];
lean_object* v_a_2287_ = _args[11];
lean_object* v_a_2288_ = _args[12];
lean_object* v_a_2289_ = _args[13];
lean_object* v_a_2290_ = _args[14];
lean_object* v_a_2291_ = _args[15];
lean_object* v_a_2292_ = _args[16];
_start:
{
lean_object* v_res_2293_; 
v_res_2293_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue(v_u_2276_, v_v_2277_, v_k_2278_, v_c_2279_, v_e_2280_, v_a_2281_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_);
lean_dec(v_a_2291_);
lean_dec_ref(v_a_2290_);
lean_dec(v_a_2289_);
lean_dec_ref(v_a_2288_);
lean_dec(v_a_2287_);
lean_dec_ref(v_a_2286_);
lean_dec(v_a_2285_);
lean_dec_ref(v_a_2284_);
lean_dec(v_a_2283_);
lean_dec(v_a_2282_);
lean_dec(v_a_2281_);
return v_res_2293_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse___redArg(lean_object* v_e_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_){
_start:
{
lean_object* v___x_2302_; 
v___x_2302_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_2295_, v_a_2299_);
if (lean_obj_tag(v___x_2302_) == 0)
{
lean_object* v_a_2303_; lean_object* v_termMapInv_2304_; lean_object* v___x_2305_; 
v_a_2303_ = lean_ctor_get(v___x_2302_, 0);
lean_inc(v_a_2303_);
lean_dec_ref_known(v___x_2302_, 1);
v_termMapInv_2304_ = lean_ctor_get(v_a_2303_, 4);
lean_inc_ref(v_termMapInv_2304_);
lean_dec(v_a_2303_);
v___x_2305_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMapInv_2304_, v_e_2294_);
lean_dec_ref(v_termMapInv_2304_);
if (lean_obj_tag(v___x_2305_) == 1)
{
lean_object* v_val_2306_; lean_object* v_fst_2307_; lean_object* v___x_2308_; 
lean_dec_ref(v_e_2294_);
v_val_2306_ = lean_ctor_get(v___x_2305_, 0);
lean_inc(v_val_2306_);
lean_dec_ref_known(v___x_2305_, 1);
v_fst_2307_ = lean_ctor_get(v_val_2306_, 0);
lean_inc(v_fst_2307_);
lean_dec(v_val_2306_);
v___x_2308_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_fst_2307_, v_a_2295_);
if (lean_obj_tag(v___x_2308_) == 0)
{
lean_object* v_a_2309_; uint8_t v___x_2310_; 
v_a_2309_ = lean_ctor_get(v___x_2308_, 0);
v___x_2310_ = lean_unbox(v_a_2309_);
if (v___x_2310_ == 0)
{
lean_dec(v_fst_2307_);
return v___x_2308_;
}
else
{
lean_object* v___x_2311_; 
lean_dec_ref_known(v___x_2308_, 1);
v___x_2311_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_fst_2307_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
return v___x_2311_;
}
}
else
{
lean_dec(v_fst_2307_);
return v___x_2308_;
}
}
else
{
lean_object* v___x_2312_; 
lean_dec(v___x_2305_);
v___x_2312_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_e_2294_, v_a_2295_);
if (lean_obj_tag(v___x_2312_) == 0)
{
lean_object* v_a_2313_; uint8_t v___x_2314_; 
v_a_2313_ = lean_ctor_get(v___x_2312_, 0);
v___x_2314_ = lean_unbox(v_a_2313_);
if (v___x_2314_ == 0)
{
lean_dec_ref(v_e_2294_);
return v___x_2312_;
}
else
{
lean_object* v___x_2315_; 
lean_dec_ref_known(v___x_2312_, 1);
v___x_2315_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
return v___x_2315_;
}
}
else
{
lean_dec_ref(v_e_2294_);
return v___x_2312_;
}
}
}
else
{
lean_object* v_a_2316_; lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2323_; 
lean_dec_ref(v_e_2294_);
v_a_2316_ = lean_ctor_get(v___x_2302_, 0);
v_isSharedCheck_2323_ = !lean_is_exclusive(v___x_2302_);
if (v_isSharedCheck_2323_ == 0)
{
v___x_2318_ = v___x_2302_;
v_isShared_2319_ = v_isSharedCheck_2323_;
goto v_resetjp_2317_;
}
else
{
lean_inc(v_a_2316_);
lean_dec(v___x_2302_);
v___x_2318_ = lean_box(0);
v_isShared_2319_ = v_isSharedCheck_2323_;
goto v_resetjp_2317_;
}
v_resetjp_2317_:
{
lean_object* v___x_2321_; 
if (v_isShared_2319_ == 0)
{
v___x_2321_ = v___x_2318_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v_a_2316_);
v___x_2321_ = v_reuseFailAlloc_2322_;
goto v_reusejp_2320_;
}
v_reusejp_2320_:
{
return v___x_2321_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2294_ = stack[0].m_obj;
lean_object* v_a_2295_ = stack[1].m_obj;
lean_object* v_a_2296_ = stack[2].m_obj;
lean_object* v_a_2297_ = stack[3].m_obj;
lean_object* v_a_2298_ = stack[4].m_obj;
lean_object* v_a_2299_ = stack[5].m_obj;
lean_object* v_a_2300_ = stack[6].m_obj;
lean_object* v_res_2324_;
v_res_2324_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse___redArg(v_e_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_);
stack->m_obj
 = v_res_2324_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse___redArg___boxed(lean_object* v_e_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_){
_start:
{
lean_object* v_res_2333_; 
v_res_2333_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse___redArg(v_e_2325_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_);
lean_dec(v_a_2331_);
lean_dec_ref(v_a_2330_);
lean_dec(v_a_2329_);
lean_dec_ref(v_a_2328_);
lean_dec_ref(v_a_2327_);
lean_dec(v_a_2326_);
return v_res_2333_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse(lean_object* v_e_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_){
_start:
{
lean_object* v___x_2347_; 
v___x_2347_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse___redArg(v_e_2334_, v_a_2336_, v_a_2340_, v_a_2342_, v_a_2343_, v_a_2344_, v_a_2345_);
return v___x_2347_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2334_ = stack[0].m_obj;
lean_object* v_a_2335_ = stack[1].m_obj;
lean_object* v_a_2336_ = stack[2].m_obj;
lean_object* v_a_2337_ = stack[3].m_obj;
lean_object* v_a_2338_ = stack[4].m_obj;
lean_object* v_a_2339_ = stack[5].m_obj;
lean_object* v_a_2340_ = stack[6].m_obj;
lean_object* v_a_2341_ = stack[7].m_obj;
lean_object* v_a_2342_ = stack[8].m_obj;
lean_object* v_a_2343_ = stack[9].m_obj;
lean_object* v_a_2344_ = stack[10].m_obj;
lean_object* v_a_2345_ = stack[11].m_obj;
lean_object* v_res_2348_;
v_res_2348_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse(v_e_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_, v_a_2345_);
stack->m_obj
 = v_res_2348_;
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
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse(lean_object* v_u_2375_, lean_object* v_v_2376_, lean_object* v_k_2377_, lean_object* v_c_2378_, lean_object* v_e_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_){
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
v___x_2426_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_u_2375_, v_a_2380_, v_a_2381_, v_a_2389_);
if (lean_obj_tag(v___x_2426_) == 0)
{
lean_object* v_a_2427_; lean_object* v___x_2428_; 
v_a_2427_ = lean_ctor_get(v___x_2426_, 0);
lean_inc(v_a_2427_);
lean_dec_ref_known(v___x_2426_, 1);
v___x_2428_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_v_2376_, v_a_2380_, v_a_2381_, v_a_2389_);
if (lean_obj_tag(v___x_2428_) == 0)
{
lean_object* v_a_2429_; lean_object* v___x_2430_; 
v_a_2429_ = lean_ctor_get(v___x_2428_, 0);
lean_inc(v_a_2429_);
lean_dec_ref_known(v___x_2428_, 1);
v___x_2430_ = l_Lean_Meta_Grind_Order_Cnstr_pp___redArg(v_c_2378_, v_a_2380_, v_a_2381_, v_a_2389_);
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
v___y_2433_ = v___x_2457_;
v___y_2434_ = v___x_2458_;
goto v___jp_2432_;
}
else
{
lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; 
v___x_2459_ = l_Int_repr(v_k_2452_);
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
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_2375_ = stack[0].m_obj;
lean_object* v_v_2376_ = stack[1].m_obj;
lean_object* v_k_2377_ = stack[2].m_obj;
lean_object* v_c_2378_ = stack[3].m_obj;
lean_object* v_e_2379_ = stack[4].m_obj;
lean_object* v_a_2380_ = stack[5].m_obj;
lean_object* v_a_2381_ = stack[6].m_obj;
lean_object* v_a_2382_ = stack[7].m_obj;
lean_object* v_a_2383_ = stack[8].m_obj;
lean_object* v_a_2384_ = stack[9].m_obj;
lean_object* v_a_2385_ = stack[10].m_obj;
lean_object* v_a_2386_ = stack[11].m_obj;
lean_object* v_a_2387_ = stack[12].m_obj;
lean_object* v_a_2388_ = stack[13].m_obj;
lean_object* v_a_2389_ = stack[14].m_obj;
lean_object* v_a_2390_ = stack[15].m_obj;
lean_object* v_res_2503_;
v_res_2503_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse(v_u_2375_, v_v_2376_, v_k_2377_, v_c_2378_, v_e_2379_, v_a_2380_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_);
stack->m_obj
 = v_res_2503_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___boxed(lean_object** _args){
lean_object* v_u_2504_ = _args[0];
lean_object* v_v_2505_ = _args[1];
lean_object* v_k_2506_ = _args[2];
lean_object* v_c_2507_ = _args[3];
lean_object* v_e_2508_ = _args[4];
lean_object* v_a_2509_ = _args[5];
lean_object* v_a_2510_ = _args[6];
lean_object* v_a_2511_ = _args[7];
lean_object* v_a_2512_ = _args[8];
lean_object* v_a_2513_ = _args[9];
lean_object* v_a_2514_ = _args[10];
lean_object* v_a_2515_ = _args[11];
lean_object* v_a_2516_ = _args[12];
lean_object* v_a_2517_ = _args[13];
lean_object* v_a_2518_ = _args[14];
lean_object* v_a_2519_ = _args[15];
lean_object* v_a_2520_ = _args[16];
_start:
{
lean_object* v_res_2521_; 
v_res_2521_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse(v_u_2504_, v_v_2505_, v_k_2506_, v_c_2507_, v_e_2508_, v_a_2509_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_);
lean_dec(v_a_2519_);
lean_dec_ref(v_a_2518_);
lean_dec(v_a_2517_);
lean_dec_ref(v_a_2516_);
lean_dec(v_a_2515_);
lean_dec_ref(v_a_2514_);
lean_dec(v_a_2513_);
lean_dec_ref(v_a_2512_);
lean_dec(v_a_2511_);
lean_dec(v_a_2510_);
lean_dec(v_a_2509_);
return v_res_2521_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___lam__0(lean_object* v_f_2522_, lean_object* v_x_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_){
_start:
{
lean_object* v_fst_2536_; lean_object* v_snd_2537_; lean_object* v___x_2538_; 
v_fst_2536_ = lean_ctor_get(v_x_2523_, 0);
lean_inc(v_fst_2536_);
v_snd_2537_ = lean_ctor_get(v_x_2523_, 1);
lean_inc(v_snd_2537_);
lean_dec_ref(v_x_2523_);
lean_inc(v___y_2534_);
lean_inc_ref(v___y_2533_);
lean_inc(v___y_2532_);
lean_inc_ref(v___y_2531_);
lean_inc(v___y_2530_);
lean_inc_ref(v___y_2529_);
lean_inc(v___y_2528_);
lean_inc_ref(v___y_2527_);
lean_inc(v___y_2526_);
lean_inc(v___y_2525_);
lean_inc(v___y_2524_);
v___x_2538_ = lean_apply_14(v_f_2522_, v_fst_2536_, v_snd_2537_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, lean_box(0));
return v___x_2538_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2522_ = stack[0].m_obj;
lean_object* v_x_2523_ = stack[1].m_obj;
lean_object* v___y_2524_ = stack[2].m_obj;
lean_object* v___y_2525_ = stack[3].m_obj;
lean_object* v___y_2526_ = stack[4].m_obj;
lean_object* v___y_2527_ = stack[5].m_obj;
lean_object* v___y_2528_ = stack[6].m_obj;
lean_object* v___y_2529_ = stack[7].m_obj;
lean_object* v___y_2530_ = stack[8].m_obj;
lean_object* v___y_2531_ = stack[9].m_obj;
lean_object* v___y_2532_ = stack[10].m_obj;
lean_object* v___y_2533_ = stack[11].m_obj;
lean_object* v___y_2534_ = stack[12].m_obj;
lean_object* v_res_2539_;
v_res_2539_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___lam__0(v_f_2522_, v_x_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_);
stack->m_obj
 = v_res_2539_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___lam__0___boxed(lean_object* v_f_2540_, lean_object* v_x_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_){
_start:
{
lean_object* v_res_2554_; 
v_res_2554_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___lam__0(v_f_2540_, v_x_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_);
lean_dec(v___y_2552_);
lean_dec_ref(v___y_2551_);
lean_dec(v___y_2550_);
lean_dec_ref(v___y_2549_);
lean_dec(v___y_2548_);
lean_dec_ref(v___y_2547_);
lean_dec(v___y_2546_);
lean_dec_ref(v___y_2545_);
lean_dec(v___y_2544_);
lean_dec(v___y_2543_);
lean_dec(v___y_2542_);
return v_res_2554_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__2(void){
_start:
{
lean_object* v___x_2558_; lean_object* v___f_2559_; 
v___x_2558_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___f_2559_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2559_, 0, v___x_2558_);
return v___f_2559_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__3(void){
_start:
{
lean_object* v___f_2560_; lean_object* v___f_2561_; 
v___f_2560_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__2, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__2);
v___f_2561_ = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2561_, 0, v___f_2560_);
lean_closure_set(v___f_2561_, 1, v___f_2560_);
return v___f_2561_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf(lean_object* v_u_2562_, lean_object* v_v_2563_, lean_object* v_f_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_){
_start:
{
lean_object* v___x_2577_; lean_object* v_toApplicative_2578_; lean_object* v_toFunctor_2579_; lean_object* v_toSeq_2580_; lean_object* v_toSeqLeft_2581_; lean_object* v_toSeqRight_2582_; lean_object* v___f_2583_; lean_object* v___f_2584_; lean_object* v___f_2585_; lean_object* v___f_2586_; lean_object* v___x_2587_; lean_object* v___f_2588_; lean_object* v___f_2589_; lean_object* v___f_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v_toApplicative_2594_; lean_object* v___x_2596_; uint8_t v_isShared_2597_; uint8_t v_isSharedCheck_2655_; 
v___x_2577_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__1, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__1);
v_toApplicative_2578_ = lean_ctor_get(v___x_2577_, 0);
v_toFunctor_2579_ = lean_ctor_get(v_toApplicative_2578_, 0);
v_toSeq_2580_ = lean_ctor_get(v_toApplicative_2578_, 2);
v_toSeqLeft_2581_ = lean_ctor_get(v_toApplicative_2578_, 3);
v_toSeqRight_2582_ = lean_ctor_get(v_toApplicative_2578_, 4);
v___f_2583_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__2));
v___f_2584_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__3));
lean_inc_ref_n(v_toFunctor_2579_, 2);
v___f_2585_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2585_, 0, v_toFunctor_2579_);
v___f_2586_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2586_, 0, v_toFunctor_2579_);
v___x_2587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2587_, 0, v___f_2585_);
lean_ctor_set(v___x_2587_, 1, v___f_2586_);
lean_inc(v_toSeqRight_2582_);
v___f_2588_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2588_, 0, v_toSeqRight_2582_);
lean_inc(v_toSeqLeft_2581_);
v___f_2589_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2589_, 0, v_toSeqLeft_2581_);
lean_inc(v_toSeq_2580_);
v___f_2590_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2590_, 0, v_toSeq_2580_);
v___x_2591_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2591_, 0, v___x_2587_);
lean_ctor_set(v___x_2591_, 1, v___f_2583_);
lean_ctor_set(v___x_2591_, 2, v___f_2590_);
lean_ctor_set(v___x_2591_, 3, v___f_2589_);
lean_ctor_set(v___x_2591_, 4, v___f_2588_);
v___x_2592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2592_, 0, v___x_2591_);
lean_ctor_set(v___x_2592_, 1, v___f_2584_);
v___x_2593_ = l_StateRefT_x27_instMonad___redArg(v___x_2592_);
v_toApplicative_2594_ = lean_ctor_get(v___x_2593_, 0);
v_isSharedCheck_2655_ = !lean_is_exclusive(v___x_2593_);
if (v_isSharedCheck_2655_ == 0)
{
lean_object* v_unused_2656_; 
v_unused_2656_ = lean_ctor_get(v___x_2593_, 1);
lean_dec(v_unused_2656_);
v___x_2596_ = v___x_2593_;
v_isShared_2597_ = v_isSharedCheck_2655_;
goto v_resetjp_2595_;
}
else
{
lean_inc(v_toApplicative_2594_);
lean_dec(v___x_2593_);
v___x_2596_ = lean_box(0);
v_isShared_2597_ = v_isSharedCheck_2655_;
goto v_resetjp_2595_;
}
v_resetjp_2595_:
{
lean_object* v_toFunctor_2598_; lean_object* v_toSeq_2599_; lean_object* v_toSeqLeft_2600_; lean_object* v_toSeqRight_2601_; lean_object* v___x_2603_; uint8_t v_isShared_2604_; uint8_t v_isSharedCheck_2653_; 
v_toFunctor_2598_ = lean_ctor_get(v_toApplicative_2594_, 0);
v_toSeq_2599_ = lean_ctor_get(v_toApplicative_2594_, 2);
v_toSeqLeft_2600_ = lean_ctor_get(v_toApplicative_2594_, 3);
v_toSeqRight_2601_ = lean_ctor_get(v_toApplicative_2594_, 4);
v_isSharedCheck_2653_ = !lean_is_exclusive(v_toApplicative_2594_);
if (v_isSharedCheck_2653_ == 0)
{
lean_object* v_unused_2654_; 
v_unused_2654_ = lean_ctor_get(v_toApplicative_2594_, 1);
lean_dec(v_unused_2654_);
v___x_2603_ = v_toApplicative_2594_;
v_isShared_2604_ = v_isSharedCheck_2653_;
goto v_resetjp_2602_;
}
else
{
lean_inc(v_toSeqRight_2601_);
lean_inc(v_toSeqLeft_2600_);
lean_inc(v_toSeq_2599_);
lean_inc(v_toFunctor_2598_);
lean_dec(v_toApplicative_2594_);
v___x_2603_ = lean_box(0);
v_isShared_2604_ = v_isSharedCheck_2653_;
goto v_resetjp_2602_;
}
v_resetjp_2602_:
{
lean_object* v___f_2605_; lean_object* v___f_2606_; lean_object* v___f_2607_; lean_object* v___f_2608_; lean_object* v___f_2609_; lean_object* v___x_2610_; lean_object* v___f_2611_; lean_object* v___f_2612_; lean_object* v___f_2613_; lean_object* v___x_2615_; 
v___f_2605_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___lam__0___boxed), 14, 1);
lean_closure_set(v___f_2605_, 0, v_f_2564_);
v___f_2606_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__4));
v___f_2607_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__5));
lean_inc_ref(v_toFunctor_2598_);
v___f_2608_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2608_, 0, v_toFunctor_2598_);
v___f_2609_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2609_, 0, v_toFunctor_2598_);
v___x_2610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2610_, 0, v___f_2608_);
lean_ctor_set(v___x_2610_, 1, v___f_2609_);
v___f_2611_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2611_, 0, v_toSeqRight_2601_);
v___f_2612_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2612_, 0, v_toSeqLeft_2600_);
v___f_2613_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2613_, 0, v_toSeq_2599_);
if (v_isShared_2604_ == 0)
{
lean_ctor_set(v___x_2603_, 4, v___f_2611_);
lean_ctor_set(v___x_2603_, 3, v___f_2612_);
lean_ctor_set(v___x_2603_, 2, v___f_2613_);
lean_ctor_set(v___x_2603_, 1, v___f_2606_);
lean_ctor_set(v___x_2603_, 0, v___x_2610_);
v___x_2615_ = v___x_2603_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v___x_2610_);
lean_ctor_set(v_reuseFailAlloc_2652_, 1, v___f_2606_);
lean_ctor_set(v_reuseFailAlloc_2652_, 2, v___f_2613_);
lean_ctor_set(v_reuseFailAlloc_2652_, 3, v___f_2612_);
lean_ctor_set(v_reuseFailAlloc_2652_, 4, v___f_2611_);
v___x_2615_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2614_;
}
v_reusejp_2614_:
{
lean_object* v___x_2617_; 
if (v_isShared_2597_ == 0)
{
lean_ctor_set(v___x_2596_, 1, v___f_2607_);
lean_ctor_set(v___x_2596_, 0, v___x_2615_);
v___x_2617_ = v___x_2596_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v___x_2615_);
lean_ctor_set(v_reuseFailAlloc_2651_, 1, v___f_2607_);
v___x_2617_ = v_reuseFailAlloc_2651_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___f_2625_; lean_object* v___x_2626_; 
v___x_2618_ = l_StateRefT_x27_instMonad___redArg(v___x_2617_);
v___x_2619_ = l_ReaderT_instMonad___redArg(v___x_2618_);
v___x_2620_ = l_StateRefT_x27_instMonad___redArg(v___x_2619_);
v___x_2621_ = l_ReaderT_instMonad___redArg(v___x_2620_);
v___x_2622_ = l_ReaderT_instMonad___redArg(v___x_2621_);
v___x_2623_ = l_StateRefT_x27_instMonad___redArg(v___x_2622_);
v___x_2624_ = l_ReaderT_instMonad___redArg(v___x_2623_);
v___f_2625_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__1));
v___x_2626_ = l_Lean_Meta_Grind_Order_getStruct___redArg(v_a_2565_, v_a_2566_, v_a_2574_);
if (lean_obj_tag(v___x_2626_) == 0)
{
lean_object* v_a_2627_; lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2642_; 
v_a_2627_ = lean_ctor_get(v___x_2626_, 0);
v_isSharedCheck_2642_ = !lean_is_exclusive(v___x_2626_);
if (v_isSharedCheck_2642_ == 0)
{
v___x_2629_ = v___x_2626_;
v_isShared_2630_ = v_isSharedCheck_2642_;
goto v_resetjp_2628_;
}
else
{
lean_inc(v_a_2627_);
lean_dec(v___x_2626_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2642_;
goto v_resetjp_2628_;
}
v_resetjp_2628_:
{
lean_object* v___f_2631_; lean_object* v_cnstrsOf_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; 
v___f_2631_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__3);
v_cnstrsOf_2632_ = lean_ctor_get(v_a_2627_, 4);
lean_inc_ref(v_cnstrsOf_2632_);
lean_dec(v_a_2627_);
v___x_2633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2633_, 0, v_u_2562_);
lean_ctor_set(v___x_2633_, 1, v_v_2563_);
v___x_2634_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_2631_, v___f_2625_, v_cnstrsOf_2632_, v___x_2633_);
lean_dec_ref(v_cnstrsOf_2632_);
if (lean_obj_tag(v___x_2634_) == 1)
{
lean_object* v_val_2635_; lean_object* v___x_1500__overap_2636_; lean_object* v___x_2637_; 
lean_del_object(v___x_2629_);
v_val_2635_ = lean_ctor_get(v___x_2634_, 0);
lean_inc(v_val_2635_);
lean_dec_ref_known(v___x_2634_, 1);
v___x_1500__overap_2636_ = l_List_forM___redArg(v___x_2624_, v_val_2635_, v___f_2605_);
lean_inc(v_a_2575_);
lean_inc_ref(v_a_2574_);
lean_inc(v_a_2573_);
lean_inc_ref(v_a_2572_);
lean_inc(v_a_2571_);
lean_inc_ref(v_a_2570_);
lean_inc(v_a_2569_);
lean_inc_ref(v_a_2568_);
lean_inc(v_a_2567_);
lean_inc(v_a_2566_);
lean_inc(v_a_2565_);
v___x_2637_ = lean_apply_12(v___x_1500__overap_2636_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_, v_a_2573_, v_a_2574_, v_a_2575_, lean_box(0));
return v___x_2637_;
}
else
{
lean_object* v___x_2638_; lean_object* v___x_2640_; 
lean_dec(v___x_2634_);
lean_dec_ref(v___x_2624_);
lean_dec_ref(v___f_2605_);
v___x_2638_ = lean_box(0);
if (v_isShared_2630_ == 0)
{
lean_ctor_set(v___x_2629_, 0, v___x_2638_);
v___x_2640_ = v___x_2629_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v___x_2638_);
v___x_2640_ = v_reuseFailAlloc_2641_;
goto v_reusejp_2639_;
}
v_reusejp_2639_:
{
return v___x_2640_;
}
}
}
}
else
{
lean_object* v_a_2643_; lean_object* v___x_2645_; uint8_t v_isShared_2646_; uint8_t v_isSharedCheck_2650_; 
lean_dec_ref(v___x_2624_);
lean_dec_ref(v___f_2605_);
lean_dec(v_v_2563_);
lean_dec(v_u_2562_);
v_a_2643_ = lean_ctor_get(v___x_2626_, 0);
v_isSharedCheck_2650_ = !lean_is_exclusive(v___x_2626_);
if (v_isSharedCheck_2650_ == 0)
{
v___x_2645_ = v___x_2626_;
v_isShared_2646_ = v_isSharedCheck_2650_;
goto v_resetjp_2644_;
}
else
{
lean_inc(v_a_2643_);
lean_dec(v___x_2626_);
v___x_2645_ = lean_box(0);
v_isShared_2646_ = v_isSharedCheck_2650_;
goto v_resetjp_2644_;
}
v_resetjp_2644_:
{
lean_object* v___x_2648_; 
if (v_isShared_2646_ == 0)
{
v___x_2648_ = v___x_2645_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v_a_2643_);
v___x_2648_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
return v___x_2648_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_2562_ = stack[0].m_obj;
lean_object* v_v_2563_ = stack[1].m_obj;
lean_object* v_f_2564_ = stack[2].m_obj;
lean_object* v_a_2565_ = stack[3].m_obj;
lean_object* v_a_2566_ = stack[4].m_obj;
lean_object* v_a_2567_ = stack[5].m_obj;
lean_object* v_a_2568_ = stack[6].m_obj;
lean_object* v_a_2569_ = stack[7].m_obj;
lean_object* v_a_2570_ = stack[8].m_obj;
lean_object* v_a_2571_ = stack[9].m_obj;
lean_object* v_a_2572_ = stack[10].m_obj;
lean_object* v_a_2573_ = stack[11].m_obj;
lean_object* v_a_2574_ = stack[12].m_obj;
lean_object* v_a_2575_ = stack[13].m_obj;
lean_object* v_res_2657_;
v_res_2657_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf(v_u_2562_, v_v_2563_, v_f_2564_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_, v_a_2573_, v_a_2574_, v_a_2575_);
stack->m_obj
 = v_res_2657_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___boxed(lean_object* v_u_2658_, lean_object* v_v_2659_, lean_object* v_f_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_, lean_object* v_a_2672_){
_start:
{
lean_object* v_res_2673_; 
v_res_2673_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf(v_u_2658_, v_v_2659_, v_f_2660_, v_a_2661_, v_a_2662_, v_a_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_);
lean_dec(v_a_2671_);
lean_dec_ref(v_a_2670_);
lean_dec(v_a_2669_);
lean_dec_ref(v_a_2668_);
lean_dec(v_a_2667_);
lean_dec_ref(v_a_2666_);
lean_dec(v_a_2665_);
lean_dec_ref(v_a_2664_);
lean_dec(v_a_2663_);
lean_dec(v_a_2662_);
lean_dec(v_a_2661_);
return v_res_2673_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___redArg(lean_object* v_e_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_){
_start:
{
lean_object* v___x_2678_; 
v___x_2678_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_2675_, v_a_2676_);
if (lean_obj_tag(v___x_2678_) == 0)
{
lean_object* v_a_2679_; lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2701_; 
v_a_2679_ = lean_ctor_get(v___x_2678_, 0);
v_isSharedCheck_2701_ = !lean_is_exclusive(v___x_2678_);
if (v_isSharedCheck_2701_ == 0)
{
v___x_2681_ = v___x_2678_;
v_isShared_2682_ = v_isSharedCheck_2701_;
goto v_resetjp_2680_;
}
else
{
lean_inc(v_a_2679_);
lean_dec(v___x_2678_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2701_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
lean_object* v_termMapInv_2683_; lean_object* v___x_2684_; 
v_termMapInv_2683_ = lean_ctor_get(v_a_2679_, 4);
lean_inc_ref(v_termMapInv_2683_);
lean_dec(v_a_2679_);
v___x_2684_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMapInv_2683_, v_e_2674_);
lean_dec_ref(v_termMapInv_2683_);
if (lean_obj_tag(v___x_2684_) == 1)
{
lean_object* v_val_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2696_; 
v_val_2685_ = lean_ctor_get(v___x_2684_, 0);
v_isSharedCheck_2696_ = !lean_is_exclusive(v___x_2684_);
if (v_isSharedCheck_2696_ == 0)
{
v___x_2687_ = v___x_2684_;
v_isShared_2688_ = v_isSharedCheck_2696_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_val_2685_);
lean_dec(v___x_2684_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2696_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
lean_object* v_fst_2689_; lean_object* v___x_2691_; 
v_fst_2689_ = lean_ctor_get(v_val_2685_, 0);
lean_inc(v_fst_2689_);
lean_dec(v_val_2685_);
if (v_isShared_2688_ == 0)
{
lean_ctor_set(v___x_2687_, 0, v_fst_2689_);
v___x_2691_ = v___x_2687_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v_fst_2689_);
v___x_2691_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
lean_object* v___x_2693_; 
if (v_isShared_2682_ == 0)
{
lean_ctor_set(v___x_2681_, 0, v___x_2691_);
v___x_2693_ = v___x_2681_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v___x_2691_);
v___x_2693_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
return v___x_2693_;
}
}
}
}
else
{
lean_object* v___x_2697_; lean_object* v___x_2699_; 
lean_dec(v___x_2684_);
v___x_2697_ = lean_box(0);
if (v_isShared_2682_ == 0)
{
lean_ctor_set(v___x_2681_, 0, v___x_2697_);
v___x_2699_ = v___x_2681_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v___x_2697_);
v___x_2699_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
return v___x_2699_;
}
}
}
}
else
{
lean_object* v_a_2702_; lean_object* v___x_2704_; uint8_t v_isShared_2705_; uint8_t v_isSharedCheck_2709_; 
v_a_2702_ = lean_ctor_get(v___x_2678_, 0);
v_isSharedCheck_2709_ = !lean_is_exclusive(v___x_2678_);
if (v_isSharedCheck_2709_ == 0)
{
v___x_2704_ = v___x_2678_;
v_isShared_2705_ = v_isSharedCheck_2709_;
goto v_resetjp_2703_;
}
else
{
lean_inc(v_a_2702_);
lean_dec(v___x_2678_);
v___x_2704_ = lean_box(0);
v_isShared_2705_ = v_isSharedCheck_2709_;
goto v_resetjp_2703_;
}
v_resetjp_2703_:
{
lean_object* v___x_2707_; 
if (v_isShared_2705_ == 0)
{
v___x_2707_ = v___x_2704_;
goto v_reusejp_2706_;
}
else
{
lean_object* v_reuseFailAlloc_2708_; 
v_reuseFailAlloc_2708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2708_, 0, v_a_2702_);
v___x_2707_ = v_reuseFailAlloc_2708_;
goto v_reusejp_2706_;
}
v_reusejp_2706_:
{
return v___x_2707_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2674_ = stack[0].m_obj;
lean_object* v_a_2675_ = stack[1].m_obj;
lean_object* v_a_2676_ = stack[2].m_obj;
lean_object* v_res_2710_;
v_res_2710_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___redArg(v_e_2674_, v_a_2675_, v_a_2676_);
stack->m_obj
 = v_res_2710_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___redArg___boxed(lean_object* v_e_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_){
_start:
{
lean_object* v_res_2715_; 
v_res_2715_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___redArg(v_e_2711_, v_a_2712_, v_a_2713_);
lean_dec_ref(v_a_2713_);
lean_dec(v_a_2712_);
lean_dec_ref(v_e_2711_);
return v_res_2715_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f(lean_object* v_e_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_){
_start:
{
lean_object* v___x_2728_; 
v___x_2728_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___redArg(v_e_2716_, v_a_2717_, v_a_2725_);
return v___x_2728_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2716_ = stack[0].m_obj;
lean_object* v_a_2717_ = stack[1].m_obj;
lean_object* v_a_2718_ = stack[2].m_obj;
lean_object* v_a_2719_ = stack[3].m_obj;
lean_object* v_a_2720_ = stack[4].m_obj;
lean_object* v_a_2721_ = stack[5].m_obj;
lean_object* v_a_2722_ = stack[6].m_obj;
lean_object* v_a_2723_ = stack[7].m_obj;
lean_object* v_a_2724_ = stack[8].m_obj;
lean_object* v_a_2725_ = stack[9].m_obj;
lean_object* v_a_2726_ = stack[10].m_obj;
lean_object* v_res_2729_;
v_res_2729_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f(v_e_2716_, v_a_2717_, v_a_2718_, v_a_2719_, v_a_2720_, v_a_2721_, v_a_2722_, v_a_2723_, v_a_2724_, v_a_2725_, v_a_2726_);
stack->m_obj
 = v_res_2729_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___boxed(lean_object* v_e_2730_, lean_object* v_a_2731_, lean_object* v_a_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_, lean_object* v_a_2738_, lean_object* v_a_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_){
_start:
{
lean_object* v_res_2742_; 
v_res_2742_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f(v_e_2730_, v_a_2731_, v_a_2732_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_, v_a_2737_, v_a_2738_, v_a_2739_, v_a_2740_);
lean_dec(v_a_2740_);
lean_dec_ref(v_a_2739_);
lean_dec(v_a_2738_);
lean_dec_ref(v_a_2737_);
lean_dec(v_a_2736_);
lean_dec_ref(v_a_2735_);
lean_dec(v_a_2734_);
lean_dec_ref(v_a_2733_);
lean_dec(v_a_2732_);
lean_dec(v_a_2731_);
lean_dec_ref(v_e_2730_);
return v_res_2742_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq(lean_object* v_u_2743_, lean_object* v_v_2744_, lean_object* v_k_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_){
_start:
{
lean_object* v___y_2759_; lean_object* v___y_2760_; lean_object* v___y_2761_; uint8_t v___x_2801_; 
v___x_2801_ = lean_nat_dec_eq(v_u_2743_, v_v_2744_);
if (v___x_2801_ == 0)
{
lean_object* v___x_2802_; 
v___x_2802_ = l_Lean_Meta_Grind_Order_isPartialOrder(v_a_2746_, v_a_2747_, v_a_2748_, v_a_2749_, v_a_2750_, v_a_2751_, v_a_2752_, v_a_2753_, v_a_2754_, v_a_2755_, v_a_2756_);
if (lean_obj_tag(v___x_2802_) == 0)
{
lean_object* v_a_2803_; lean_object* v___x_2805_; uint8_t v_isShared_2806_; uint8_t v_isSharedCheck_2940_; 
v_a_2803_ = lean_ctor_get(v___x_2802_, 0);
v_isSharedCheck_2940_ = !lean_is_exclusive(v___x_2802_);
if (v_isSharedCheck_2940_ == 0)
{
v___x_2805_ = v___x_2802_;
v_isShared_2806_ = v_isSharedCheck_2940_;
goto v_resetjp_2804_;
}
else
{
lean_inc(v_a_2803_);
lean_dec(v___x_2802_);
v___x_2805_ = lean_box(0);
v_isShared_2806_ = v_isSharedCheck_2940_;
goto v_resetjp_2804_;
}
v_resetjp_2804_:
{
uint8_t v___x_2807_; 
v___x_2807_ = lean_unbox(v_a_2803_);
lean_dec(v_a_2803_);
if (v___x_2807_ == 0)
{
lean_object* v___x_2808_; lean_object* v___x_2810_; 
lean_dec(v_v_2744_);
lean_dec(v_u_2743_);
v___x_2808_ = lean_box(0);
if (v_isShared_2806_ == 0)
{
lean_ctor_set(v___x_2805_, 0, v___x_2808_);
v___x_2810_ = v___x_2805_;
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
uint8_t v___x_2812_; 
v___x_2812_ = l_Lean_Meta_Grind_Order_Weight_isZero(v_k_2745_);
if (v___x_2812_ == 0)
{
lean_object* v___x_2813_; lean_object* v___x_2815_; 
lean_dec(v_v_2744_);
lean_dec(v_u_2743_);
v___x_2813_ = lean_box(0);
if (v_isShared_2806_ == 0)
{
lean_ctor_set(v___x_2805_, 0, v___x_2813_);
v___x_2815_ = v___x_2805_;
goto v_reusejp_2814_;
}
else
{
lean_object* v_reuseFailAlloc_2816_; 
v_reuseFailAlloc_2816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2816_, 0, v___x_2813_);
v___x_2815_ = v_reuseFailAlloc_2816_;
goto v_reusejp_2814_;
}
v_reusejp_2814_:
{
return v___x_2815_;
}
}
else
{
lean_object* v___x_2817_; 
lean_del_object(v___x_2805_);
v___x_2817_ = l_Lean_Meta_Grind_Order_getDist_x3f___redArg(v_v_2744_, v_u_2743_, v_a_2746_, v_a_2747_, v_a_2755_);
if (lean_obj_tag(v___x_2817_) == 0)
{
lean_object* v_a_2818_; lean_object* v___x_2820_; uint8_t v_isShared_2821_; uint8_t v_isSharedCheck_2931_; 
v_a_2818_ = lean_ctor_get(v___x_2817_, 0);
v_isSharedCheck_2931_ = !lean_is_exclusive(v___x_2817_);
if (v_isSharedCheck_2931_ == 0)
{
v___x_2820_ = v___x_2817_;
v_isShared_2821_ = v_isSharedCheck_2931_;
goto v_resetjp_2819_;
}
else
{
lean_inc(v_a_2818_);
lean_dec(v___x_2817_);
v___x_2820_ = lean_box(0);
v_isShared_2821_ = v_isSharedCheck_2931_;
goto v_resetjp_2819_;
}
v_resetjp_2819_:
{
if (lean_obj_tag(v_a_2818_) == 1)
{
lean_object* v_val_2822_; uint8_t v___x_2823_; 
v_val_2822_ = lean_ctor_get(v_a_2818_, 0);
lean_inc(v_val_2822_);
lean_dec_ref_known(v_a_2818_, 1);
v___x_2823_ = l_Lean_Meta_Grind_Order_Weight_isZero(v_val_2822_);
lean_dec(v_val_2822_);
if (v___x_2823_ == 0)
{
lean_object* v___x_2824_; lean_object* v___x_2826_; 
lean_dec(v_v_2744_);
lean_dec(v_u_2743_);
v___x_2824_ = lean_box(0);
if (v_isShared_2821_ == 0)
{
lean_ctor_set(v___x_2820_, 0, v___x_2824_);
v___x_2826_ = v___x_2820_;
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
else
{
lean_object* v___x_2828_; 
lean_del_object(v___x_2820_);
v___x_2828_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_u_2743_, v_a_2746_, v_a_2747_, v_a_2755_);
if (lean_obj_tag(v___x_2828_) == 0)
{
lean_object* v_a_2829_; lean_object* v___x_2830_; 
v_a_2829_ = lean_ctor_get(v___x_2828_, 0);
lean_inc(v_a_2829_);
lean_dec_ref_known(v___x_2828_, 1);
v___x_2830_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_v_2744_, v_a_2746_, v_a_2747_, v_a_2755_);
if (lean_obj_tag(v___x_2830_) == 0)
{
lean_object* v_a_2831_; lean_object* v___y_2833_; lean_object* v___x_2907_; 
v_a_2831_ = lean_ctor_get(v___x_2830_, 0);
lean_inc(v_a_2831_);
lean_dec_ref_known(v___x_2830_, 1);
v___x_2907_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_a_2829_, v_a_2747_);
if (lean_obj_tag(v___x_2907_) == 0)
{
lean_object* v_a_2908_; uint8_t v___x_2909_; 
v_a_2908_ = lean_ctor_get(v___x_2907_, 0);
v___x_2909_ = lean_unbox(v_a_2908_);
if (v___x_2909_ == 0)
{
v___y_2833_ = v___x_2907_;
goto v___jp_2832_;
}
else
{
lean_object* v___x_2910_; 
lean_dec_ref_known(v___x_2907_, 1);
v___x_2910_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_a_2831_, v_a_2747_);
v___y_2833_ = v___x_2910_;
goto v___jp_2832_;
}
}
else
{
v___y_2833_ = v___x_2907_;
goto v___jp_2832_;
}
v___jp_2832_:
{
if (lean_obj_tag(v___y_2833_) == 0)
{
lean_object* v_a_2834_; uint8_t v___x_2835_; 
v_a_2834_ = lean_ctor_get(v___y_2833_, 0);
lean_inc(v_a_2834_);
lean_dec_ref_known(v___y_2833_, 1);
v___x_2835_ = lean_unbox(v_a_2834_);
lean_dec(v_a_2834_);
if (v___x_2835_ == 0)
{
lean_object* v___x_2836_; 
v___x_2836_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___redArg(v_a_2829_, v_a_2747_, v_a_2755_);
lean_dec(v_a_2829_);
if (lean_obj_tag(v___x_2836_) == 0)
{
lean_object* v_a_2837_; lean_object* v___x_2839_; uint8_t v_isShared_2840_; uint8_t v_isSharedCheck_2869_; 
v_a_2837_ = lean_ctor_get(v___x_2836_, 0);
v_isSharedCheck_2869_ = !lean_is_exclusive(v___x_2836_);
if (v_isSharedCheck_2869_ == 0)
{
v___x_2839_ = v___x_2836_;
v_isShared_2840_ = v_isSharedCheck_2869_;
goto v_resetjp_2838_;
}
else
{
lean_inc(v_a_2837_);
lean_dec(v___x_2836_);
v___x_2839_ = lean_box(0);
v_isShared_2840_ = v_isSharedCheck_2869_;
goto v_resetjp_2838_;
}
v_resetjp_2838_:
{
if (lean_obj_tag(v_a_2837_) == 1)
{
lean_object* v_val_2841_; lean_object* v___x_2842_; 
lean_del_object(v___x_2839_);
v_val_2841_ = lean_ctor_get(v_a_2837_, 0);
lean_inc(v_val_2841_);
lean_dec_ref_known(v_a_2837_, 1);
v___x_2842_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___redArg(v_a_2831_, v_a_2747_, v_a_2755_);
lean_dec(v_a_2831_);
if (lean_obj_tag(v___x_2842_) == 0)
{
lean_object* v_a_2843_; lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_2856_; 
v_a_2843_ = lean_ctor_get(v___x_2842_, 0);
v_isSharedCheck_2856_ = !lean_is_exclusive(v___x_2842_);
if (v_isSharedCheck_2856_ == 0)
{
v___x_2845_ = v___x_2842_;
v_isShared_2846_ = v_isSharedCheck_2856_;
goto v_resetjp_2844_;
}
else
{
lean_inc(v_a_2843_);
lean_dec(v___x_2842_);
v___x_2845_ = lean_box(0);
v_isShared_2846_ = v_isSharedCheck_2856_;
goto v_resetjp_2844_;
}
v_resetjp_2844_:
{
if (lean_obj_tag(v_a_2843_) == 1)
{
lean_object* v_val_2847_; lean_object* v___x_2848_; 
lean_del_object(v___x_2845_);
v_val_2847_ = lean_ctor_get(v_a_2843_, 0);
lean_inc(v_val_2847_);
lean_dec_ref_known(v_a_2843_, 1);
v___x_2848_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_val_2841_, v_a_2747_);
if (lean_obj_tag(v___x_2848_) == 0)
{
lean_object* v_a_2849_; uint8_t v___x_2850_; 
v_a_2849_ = lean_ctor_get(v___x_2848_, 0);
v___x_2850_ = lean_unbox(v_a_2849_);
if (v___x_2850_ == 0)
{
v___y_2759_ = v_val_2847_;
v___y_2760_ = v_val_2841_;
v___y_2761_ = v___x_2848_;
goto v___jp_2758_;
}
else
{
lean_object* v___x_2851_; 
lean_dec_ref_known(v___x_2848_, 1);
v___x_2851_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_val_2847_, v_a_2747_);
v___y_2759_ = v_val_2847_;
v___y_2760_ = v_val_2841_;
v___y_2761_ = v___x_2851_;
goto v___jp_2758_;
}
}
else
{
v___y_2759_ = v_val_2847_;
v___y_2760_ = v_val_2841_;
v___y_2761_ = v___x_2848_;
goto v___jp_2758_;
}
}
else
{
lean_object* v___x_2852_; lean_object* v___x_2854_; 
lean_dec(v_a_2843_);
lean_dec(v_val_2841_);
lean_dec(v_v_2744_);
lean_dec(v_u_2743_);
v___x_2852_ = lean_box(0);
if (v_isShared_2846_ == 0)
{
lean_ctor_set(v___x_2845_, 0, v___x_2852_);
v___x_2854_ = v___x_2845_;
goto v_reusejp_2853_;
}
else
{
lean_object* v_reuseFailAlloc_2855_; 
v_reuseFailAlloc_2855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2855_, 0, v___x_2852_);
v___x_2854_ = v_reuseFailAlloc_2855_;
goto v_reusejp_2853_;
}
v_reusejp_2853_:
{
return v___x_2854_;
}
}
}
}
else
{
lean_object* v_a_2857_; lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2864_; 
lean_dec(v_val_2841_);
lean_dec(v_v_2744_);
lean_dec(v_u_2743_);
v_a_2857_ = lean_ctor_get(v___x_2842_, 0);
v_isSharedCheck_2864_ = !lean_is_exclusive(v___x_2842_);
if (v_isSharedCheck_2864_ == 0)
{
v___x_2859_ = v___x_2842_;
v_isShared_2860_ = v_isSharedCheck_2864_;
goto v_resetjp_2858_;
}
else
{
lean_inc(v_a_2857_);
lean_dec(v___x_2842_);
v___x_2859_ = lean_box(0);
v_isShared_2860_ = v_isSharedCheck_2864_;
goto v_resetjp_2858_;
}
v_resetjp_2858_:
{
lean_object* v___x_2862_; 
if (v_isShared_2860_ == 0)
{
v___x_2862_ = v___x_2859_;
goto v_reusejp_2861_;
}
else
{
lean_object* v_reuseFailAlloc_2863_; 
v_reuseFailAlloc_2863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2863_, 0, v_a_2857_);
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
lean_object* v___x_2865_; lean_object* v___x_2867_; 
lean_dec(v_a_2837_);
lean_dec(v_a_2831_);
lean_dec(v_v_2744_);
lean_dec(v_u_2743_);
v___x_2865_ = lean_box(0);
if (v_isShared_2840_ == 0)
{
lean_ctor_set(v___x_2839_, 0, v___x_2865_);
v___x_2867_ = v___x_2839_;
goto v_reusejp_2866_;
}
else
{
lean_object* v_reuseFailAlloc_2868_; 
v_reuseFailAlloc_2868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2868_, 0, v___x_2865_);
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
else
{
lean_object* v_a_2870_; lean_object* v___x_2872_; uint8_t v_isShared_2873_; uint8_t v_isSharedCheck_2877_; 
lean_dec(v_a_2831_);
lean_dec(v_v_2744_);
lean_dec(v_u_2743_);
v_a_2870_ = lean_ctor_get(v___x_2836_, 0);
v_isSharedCheck_2877_ = !lean_is_exclusive(v___x_2836_);
if (v_isSharedCheck_2877_ == 0)
{
v___x_2872_ = v___x_2836_;
v_isShared_2873_ = v_isSharedCheck_2877_;
goto v_resetjp_2871_;
}
else
{
lean_inc(v_a_2870_);
lean_dec(v___x_2836_);
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
lean_object* v___x_2878_; 
v___x_2878_ = l_Lean_Meta_Grind_isEqv___redArg(v_a_2829_, v_a_2831_, v_a_2747_);
lean_dec(v_a_2831_);
lean_dec(v_a_2829_);
if (lean_obj_tag(v___x_2878_) == 0)
{
lean_object* v_a_2879_; lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_2890_; 
v_a_2879_ = lean_ctor_get(v___x_2878_, 0);
v_isSharedCheck_2890_ = !lean_is_exclusive(v___x_2878_);
if (v_isSharedCheck_2890_ == 0)
{
v___x_2881_ = v___x_2878_;
v_isShared_2882_ = v_isSharedCheck_2890_;
goto v_resetjp_2880_;
}
else
{
lean_inc(v_a_2879_);
lean_dec(v___x_2878_);
v___x_2881_ = lean_box(0);
v_isShared_2882_ = v_isSharedCheck_2890_;
goto v_resetjp_2880_;
}
v_resetjp_2880_:
{
uint8_t v___x_2883_; 
v___x_2883_ = lean_unbox(v_a_2879_);
lean_dec(v_a_2879_);
if (v___x_2883_ == 0)
{
lean_object* v___x_2884_; lean_object* v___x_2885_; 
lean_del_object(v___x_2881_);
v___x_2884_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2884_, 0, v_u_2743_);
lean_ctor_set(v___x_2884_, 1, v_v_2744_);
v___x_2885_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate(v___x_2884_, v_a_2746_, v_a_2747_, v_a_2748_, v_a_2749_, v_a_2750_, v_a_2751_, v_a_2752_, v_a_2753_, v_a_2754_, v_a_2755_, v_a_2756_);
return v___x_2885_;
}
else
{
lean_object* v___x_2886_; lean_object* v___x_2888_; 
lean_dec(v_v_2744_);
lean_dec(v_u_2743_);
v___x_2886_ = lean_box(0);
if (v_isShared_2882_ == 0)
{
lean_ctor_set(v___x_2881_, 0, v___x_2886_);
v___x_2888_ = v___x_2881_;
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
lean_dec(v_v_2744_);
lean_dec(v_u_2743_);
v_a_2891_ = lean_ctor_get(v___x_2878_, 0);
v_isSharedCheck_2898_ = !lean_is_exclusive(v___x_2878_);
if (v_isSharedCheck_2898_ == 0)
{
v___x_2893_ = v___x_2878_;
v_isShared_2894_ = v_isSharedCheck_2898_;
goto v_resetjp_2892_;
}
else
{
lean_inc(v_a_2891_);
lean_dec(v___x_2878_);
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
else
{
lean_object* v_a_2899_; lean_object* v___x_2901_; uint8_t v_isShared_2902_; uint8_t v_isSharedCheck_2906_; 
lean_dec(v_a_2831_);
lean_dec(v_a_2829_);
lean_dec(v_v_2744_);
lean_dec(v_u_2743_);
v_a_2899_ = lean_ctor_get(v___y_2833_, 0);
v_isSharedCheck_2906_ = !lean_is_exclusive(v___y_2833_);
if (v_isSharedCheck_2906_ == 0)
{
v___x_2901_ = v___y_2833_;
v_isShared_2902_ = v_isSharedCheck_2906_;
goto v_resetjp_2900_;
}
else
{
lean_inc(v_a_2899_);
lean_dec(v___y_2833_);
v___x_2901_ = lean_box(0);
v_isShared_2902_ = v_isSharedCheck_2906_;
goto v_resetjp_2900_;
}
v_resetjp_2900_:
{
lean_object* v___x_2904_; 
if (v_isShared_2902_ == 0)
{
v___x_2904_ = v___x_2901_;
goto v_reusejp_2903_;
}
else
{
lean_object* v_reuseFailAlloc_2905_; 
v_reuseFailAlloc_2905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2905_, 0, v_a_2899_);
v___x_2904_ = v_reuseFailAlloc_2905_;
goto v_reusejp_2903_;
}
v_reusejp_2903_:
{
return v___x_2904_;
}
}
}
}
}
else
{
lean_object* v_a_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_2918_; 
lean_dec(v_a_2829_);
lean_dec(v_v_2744_);
lean_dec(v_u_2743_);
v_a_2911_ = lean_ctor_get(v___x_2830_, 0);
v_isSharedCheck_2918_ = !lean_is_exclusive(v___x_2830_);
if (v_isSharedCheck_2918_ == 0)
{
v___x_2913_ = v___x_2830_;
v_isShared_2914_ = v_isSharedCheck_2918_;
goto v_resetjp_2912_;
}
else
{
lean_inc(v_a_2911_);
lean_dec(v___x_2830_);
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_2918_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
lean_object* v___x_2916_; 
if (v_isShared_2914_ == 0)
{
v___x_2916_ = v___x_2913_;
goto v_reusejp_2915_;
}
else
{
lean_object* v_reuseFailAlloc_2917_; 
v_reuseFailAlloc_2917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2917_, 0, v_a_2911_);
v___x_2916_ = v_reuseFailAlloc_2917_;
goto v_reusejp_2915_;
}
v_reusejp_2915_:
{
return v___x_2916_;
}
}
}
}
else
{
lean_object* v_a_2919_; lean_object* v___x_2921_; uint8_t v_isShared_2922_; uint8_t v_isSharedCheck_2926_; 
lean_dec(v_v_2744_);
lean_dec(v_u_2743_);
v_a_2919_ = lean_ctor_get(v___x_2828_, 0);
v_isSharedCheck_2926_ = !lean_is_exclusive(v___x_2828_);
if (v_isSharedCheck_2926_ == 0)
{
v___x_2921_ = v___x_2828_;
v_isShared_2922_ = v_isSharedCheck_2926_;
goto v_resetjp_2920_;
}
else
{
lean_inc(v_a_2919_);
lean_dec(v___x_2828_);
v___x_2921_ = lean_box(0);
v_isShared_2922_ = v_isSharedCheck_2926_;
goto v_resetjp_2920_;
}
v_resetjp_2920_:
{
lean_object* v___x_2924_; 
if (v_isShared_2922_ == 0)
{
v___x_2924_ = v___x_2921_;
goto v_reusejp_2923_;
}
else
{
lean_object* v_reuseFailAlloc_2925_; 
v_reuseFailAlloc_2925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2925_, 0, v_a_2919_);
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
}
else
{
lean_object* v___x_2927_; lean_object* v___x_2929_; 
lean_dec(v_a_2818_);
lean_dec(v_v_2744_);
lean_dec(v_u_2743_);
v___x_2927_ = lean_box(0);
if (v_isShared_2821_ == 0)
{
lean_ctor_set(v___x_2820_, 0, v___x_2927_);
v___x_2929_ = v___x_2820_;
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
}
}
else
{
lean_object* v_a_2932_; lean_object* v___x_2934_; uint8_t v_isShared_2935_; uint8_t v_isSharedCheck_2939_; 
lean_dec(v_v_2744_);
lean_dec(v_u_2743_);
v_a_2932_ = lean_ctor_get(v___x_2817_, 0);
v_isSharedCheck_2939_ = !lean_is_exclusive(v___x_2817_);
if (v_isSharedCheck_2939_ == 0)
{
v___x_2934_ = v___x_2817_;
v_isShared_2935_ = v_isSharedCheck_2939_;
goto v_resetjp_2933_;
}
else
{
lean_inc(v_a_2932_);
lean_dec(v___x_2817_);
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
}
}
}
else
{
lean_object* v_a_2941_; lean_object* v___x_2943_; uint8_t v_isShared_2944_; uint8_t v_isSharedCheck_2948_; 
lean_dec(v_v_2744_);
lean_dec(v_u_2743_);
v_a_2941_ = lean_ctor_get(v___x_2802_, 0);
v_isSharedCheck_2948_ = !lean_is_exclusive(v___x_2802_);
if (v_isSharedCheck_2948_ == 0)
{
v___x_2943_ = v___x_2802_;
v_isShared_2944_ = v_isSharedCheck_2948_;
goto v_resetjp_2942_;
}
else
{
lean_inc(v_a_2941_);
lean_dec(v___x_2802_);
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
else
{
lean_object* v___x_2949_; lean_object* v___x_2950_; 
lean_dec(v_v_2744_);
lean_dec(v_u_2743_);
v___x_2949_ = lean_box(0);
v___x_2950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2950_, 0, v___x_2949_);
return v___x_2950_;
}
v___jp_2758_:
{
if (lean_obj_tag(v___y_2761_) == 0)
{
lean_object* v_a_2762_; lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2792_; 
v_a_2762_ = lean_ctor_get(v___y_2761_, 0);
v_isSharedCheck_2792_ = !lean_is_exclusive(v___y_2761_);
if (v_isSharedCheck_2792_ == 0)
{
v___x_2764_ = v___y_2761_;
v_isShared_2765_ = v_isSharedCheck_2792_;
goto v_resetjp_2763_;
}
else
{
lean_inc(v_a_2762_);
lean_dec(v___y_2761_);
v___x_2764_ = lean_box(0);
v_isShared_2765_ = v_isSharedCheck_2792_;
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
lean_dec_ref(v___y_2760_);
lean_dec_ref(v___y_2759_);
lean_dec(v_v_2744_);
lean_dec(v_u_2743_);
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
lean_object* v___x_2771_; 
lean_del_object(v___x_2764_);
v___x_2771_ = l_Lean_Meta_Grind_isEqv___redArg(v___y_2760_, v___y_2759_, v_a_2747_);
lean_dec_ref(v___y_2759_);
lean_dec_ref(v___y_2760_);
if (lean_obj_tag(v___x_2771_) == 0)
{
lean_object* v_a_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2783_; 
v_a_2772_ = lean_ctor_get(v___x_2771_, 0);
v_isSharedCheck_2783_ = !lean_is_exclusive(v___x_2771_);
if (v_isSharedCheck_2783_ == 0)
{
v___x_2774_ = v___x_2771_;
v_isShared_2775_ = v_isSharedCheck_2783_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_a_2772_);
lean_dec(v___x_2771_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2783_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
uint8_t v___x_2776_; 
v___x_2776_ = lean_unbox(v_a_2772_);
lean_dec(v_a_2772_);
if (v___x_2776_ == 0)
{
lean_object* v___x_2777_; lean_object* v___x_2778_; 
lean_del_object(v___x_2774_);
v___x_2777_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2777_, 0, v_u_2743_);
lean_ctor_set(v___x_2777_, 1, v_v_2744_);
v___x_2778_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate(v___x_2777_, v_a_2746_, v_a_2747_, v_a_2748_, v_a_2749_, v_a_2750_, v_a_2751_, v_a_2752_, v_a_2753_, v_a_2754_, v_a_2755_, v_a_2756_);
return v___x_2778_;
}
else
{
lean_object* v___x_2779_; lean_object* v___x_2781_; 
lean_dec(v_v_2744_);
lean_dec(v_u_2743_);
v___x_2779_ = lean_box(0);
if (v_isShared_2775_ == 0)
{
lean_ctor_set(v___x_2774_, 0, v___x_2779_);
v___x_2781_ = v___x_2774_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2782_; 
v_reuseFailAlloc_2782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2782_, 0, v___x_2779_);
v___x_2781_ = v_reuseFailAlloc_2782_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
return v___x_2781_;
}
}
}
}
else
{
lean_object* v_a_2784_; lean_object* v___x_2786_; uint8_t v_isShared_2787_; uint8_t v_isSharedCheck_2791_; 
lean_dec(v_v_2744_);
lean_dec(v_u_2743_);
v_a_2784_ = lean_ctor_get(v___x_2771_, 0);
v_isSharedCheck_2791_ = !lean_is_exclusive(v___x_2771_);
if (v_isSharedCheck_2791_ == 0)
{
v___x_2786_ = v___x_2771_;
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
else
{
lean_inc(v_a_2784_);
lean_dec(v___x_2771_);
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
else
{
lean_object* v_a_2793_; lean_object* v___x_2795_; uint8_t v_isShared_2796_; uint8_t v_isSharedCheck_2800_; 
lean_dec_ref(v___y_2760_);
lean_dec_ref(v___y_2759_);
lean_dec(v_v_2744_);
lean_dec(v_u_2743_);
v_a_2793_ = lean_ctor_get(v___y_2761_, 0);
v_isSharedCheck_2800_ = !lean_is_exclusive(v___y_2761_);
if (v_isSharedCheck_2800_ == 0)
{
v___x_2795_ = v___y_2761_;
v_isShared_2796_ = v_isSharedCheck_2800_;
goto v_resetjp_2794_;
}
else
{
lean_inc(v_a_2793_);
lean_dec(v___y_2761_);
v___x_2795_ = lean_box(0);
v_isShared_2796_ = v_isSharedCheck_2800_;
goto v_resetjp_2794_;
}
v_resetjp_2794_:
{
lean_object* v___x_2798_; 
if (v_isShared_2796_ == 0)
{
v___x_2798_ = v___x_2795_;
goto v_reusejp_2797_;
}
else
{
lean_object* v_reuseFailAlloc_2799_; 
v_reuseFailAlloc_2799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2799_, 0, v_a_2793_);
v___x_2798_ = v_reuseFailAlloc_2799_;
goto v_reusejp_2797_;
}
v_reusejp_2797_:
{
return v___x_2798_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_2743_ = stack[0].m_obj;
lean_object* v_v_2744_ = stack[1].m_obj;
lean_object* v_k_2745_ = stack[2].m_obj;
lean_object* v_a_2746_ = stack[3].m_obj;
lean_object* v_a_2747_ = stack[4].m_obj;
lean_object* v_a_2748_ = stack[5].m_obj;
lean_object* v_a_2749_ = stack[6].m_obj;
lean_object* v_a_2750_ = stack[7].m_obj;
lean_object* v_a_2751_ = stack[8].m_obj;
lean_object* v_a_2752_ = stack[9].m_obj;
lean_object* v_a_2753_ = stack[10].m_obj;
lean_object* v_a_2754_ = stack[11].m_obj;
lean_object* v_a_2755_ = stack[12].m_obj;
lean_object* v_a_2756_ = stack[13].m_obj;
lean_object* v_res_2951_;
v_res_2951_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq(v_u_2743_, v_v_2744_, v_k_2745_, v_a_2746_, v_a_2747_, v_a_2748_, v_a_2749_, v_a_2750_, v_a_2751_, v_a_2752_, v_a_2753_, v_a_2754_, v_a_2755_, v_a_2756_);
stack->m_obj
 = v_res_2951_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq___boxed(lean_object* v_u_2952_, lean_object* v_v_2953_, lean_object* v_k_2954_, lean_object* v_a_2955_, lean_object* v_a_2956_, lean_object* v_a_2957_, lean_object* v_a_2958_, lean_object* v_a_2959_, lean_object* v_a_2960_, lean_object* v_a_2961_, lean_object* v_a_2962_, lean_object* v_a_2963_, lean_object* v_a_2964_, lean_object* v_a_2965_, lean_object* v_a_2966_){
_start:
{
lean_object* v_res_2967_; 
v_res_2967_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq(v_u_2952_, v_v_2953_, v_k_2954_, v_a_2955_, v_a_2956_, v_a_2957_, v_a_2958_, v_a_2959_, v_a_2960_, v_a_2961_, v_a_2962_, v_a_2963_, v_a_2964_, v_a_2965_);
lean_dec(v_a_2965_);
lean_dec_ref(v_a_2964_);
lean_dec(v_a_2963_);
lean_dec_ref(v_a_2962_);
lean_dec(v_a_2961_);
lean_dec_ref(v_a_2960_);
lean_dec(v_a_2959_);
lean_dec_ref(v_a_2958_);
lean_dec(v_a_2957_);
lean_dec(v_a_2956_);
lean_dec(v_a_2955_);
lean_dec_ref(v_k_2954_);
return v_res_2967_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_2968_, lean_object* v_vals_2969_, lean_object* v_i_2970_, lean_object* v_k_2971_){
_start:
{
lean_object* v___x_2976_; uint8_t v___x_2977_; 
v___x_2976_ = lean_array_get_size(v_keys_2968_);
v___x_2977_ = lean_nat_dec_lt(v_i_2970_, v___x_2976_);
if (v___x_2977_ == 0)
{
lean_object* v___x_2978_; 
lean_dec(v_i_2970_);
v___x_2978_ = lean_box(0);
return v___x_2978_;
}
else
{
lean_object* v_fst_2979_; lean_object* v_snd_2980_; lean_object* v_k_x27_2981_; lean_object* v_fst_2982_; lean_object* v_snd_2983_; uint8_t v___x_2984_; 
v_fst_2979_ = lean_ctor_get(v_k_2971_, 0);
v_snd_2980_ = lean_ctor_get(v_k_2971_, 1);
v_k_x27_2981_ = lean_array_fget_borrowed(v_keys_2968_, v_i_2970_);
v_fst_2982_ = lean_ctor_get(v_k_x27_2981_, 0);
v_snd_2983_ = lean_ctor_get(v_k_x27_2981_, 1);
v___x_2984_ = lean_nat_dec_eq(v_fst_2979_, v_fst_2982_);
if (v___x_2984_ == 0)
{
goto v___jp_2972_;
}
else
{
uint8_t v___x_2985_; 
v___x_2985_ = lean_nat_dec_eq(v_snd_2980_, v_snd_2983_);
if (v___x_2985_ == 0)
{
goto v___jp_2972_;
}
else
{
lean_object* v___x_2986_; lean_object* v___x_2987_; 
v___x_2986_ = lean_array_fget_borrowed(v_vals_2969_, v_i_2970_);
lean_dec(v_i_2970_);
lean_inc(v___x_2986_);
v___x_2987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2987_, 0, v___x_2986_);
return v___x_2987_;
}
}
}
v___jp_2972_:
{
lean_object* v___x_2973_; lean_object* v___x_2974_; 
v___x_2973_ = lean_unsigned_to_nat(1u);
v___x_2974_ = lean_nat_add(v_i_2970_, v___x_2973_);
lean_dec(v_i_2970_);
v_i_2970_ = v___x_2974_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_2988_, lean_object* v_vals_2989_, lean_object* v_i_2990_, lean_object* v_k_2991_){
_start:
{
lean_object* v_res_2992_; 
v_res_2992_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1___redArg(v_keys_2988_, v_vals_2989_, v_i_2990_, v_k_2991_);
lean_dec_ref(v_k_2991_);
lean_dec_ref(v_vals_2989_);
lean_dec_ref(v_keys_2988_);
return v_res_2992_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0___redArg(lean_object* v_x_2993_, size_t v_x_2994_, lean_object* v_x_2995_){
_start:
{
if (lean_obj_tag(v_x_2993_) == 0)
{
lean_object* v_es_2996_; lean_object* v___x_2997_; size_t v___x_2998_; size_t v___x_2999_; lean_object* v_j_3000_; lean_object* v___x_3001_; 
v_es_2996_ = lean_ctor_get(v_x_2993_, 0);
v___x_2997_ = lean_box(2);
v___x_2998_ = ((size_t)31ULL);
v___x_2999_ = lean_usize_land(v_x_2994_, v___x_2998_);
v_j_3000_ = lean_usize_to_nat(v___x_2999_);
v___x_3001_ = lean_array_get_borrowed(v___x_2997_, v_es_2996_, v_j_3000_);
lean_dec(v_j_3000_);
switch(lean_obj_tag(v___x_3001_))
{
case 0:
{
lean_object* v_key_3002_; lean_object* v_val_3003_; lean_object* v_fst_3004_; lean_object* v_snd_3005_; lean_object* v_fst_3006_; lean_object* v_snd_3007_; uint8_t v___x_3008_; 
v_key_3002_ = lean_ctor_get(v___x_3001_, 0);
v_val_3003_ = lean_ctor_get(v___x_3001_, 1);
v_fst_3004_ = lean_ctor_get(v_x_2995_, 0);
v_snd_3005_ = lean_ctor_get(v_x_2995_, 1);
v_fst_3006_ = lean_ctor_get(v_key_3002_, 0);
v_snd_3007_ = lean_ctor_get(v_key_3002_, 1);
v___x_3008_ = lean_nat_dec_eq(v_fst_3004_, v_fst_3006_);
if (v___x_3008_ == 0)
{
lean_object* v___x_3009_; 
v___x_3009_ = lean_box(0);
return v___x_3009_;
}
else
{
uint8_t v___x_3010_; 
v___x_3010_ = lean_nat_dec_eq(v_snd_3005_, v_snd_3007_);
if (v___x_3010_ == 0)
{
lean_object* v___x_3011_; 
v___x_3011_ = lean_box(0);
return v___x_3011_;
}
else
{
lean_object* v___x_3012_; 
lean_inc(v_val_3003_);
v___x_3012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3012_, 0, v_val_3003_);
return v___x_3012_;
}
}
}
case 1:
{
lean_object* v_node_3013_; size_t v___x_3014_; size_t v___x_3015_; 
v_node_3013_ = lean_ctor_get(v___x_3001_, 0);
v___x_3014_ = ((size_t)5ULL);
v___x_3015_ = lean_usize_shift_right(v_x_2994_, v___x_3014_);
v_x_2993_ = v_node_3013_;
v_x_2994_ = v___x_3015_;
goto _start;
}
default: 
{
lean_object* v___x_3017_; 
v___x_3017_ = lean_box(0);
return v___x_3017_;
}
}
}
else
{
lean_object* v_ks_3018_; lean_object* v_vs_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; 
v_ks_3018_ = lean_ctor_get(v_x_2993_, 0);
v_vs_3019_ = lean_ctor_get(v_x_2993_, 1);
v___x_3020_ = lean_unsigned_to_nat(0u);
v___x_3021_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1___redArg(v_ks_3018_, v_vs_3019_, v___x_3020_, v_x_2995_);
return v___x_3021_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2993_ = stack[0].m_obj;
size_t v_x_2994_ = stack[1].m_num;
lean_object* v_x_2995_ = stack[2].m_obj;
lean_object* v_res_3022_;
v_res_3022_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0___redArg(v_x_2993_, v_x_2994_, v_x_2995_);
stack->m_obj
 = v_res_3022_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0___redArg___boxed(lean_object* v_x_3023_, lean_object* v_x_3024_, lean_object* v_x_3025_){
_start:
{
size_t v_x_4004__boxed_3026_; lean_object* v_res_3027_; 
v_x_4004__boxed_3026_ = lean_unbox_usize(v_x_3024_);
lean_dec(v_x_3024_);
v_res_3027_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0___redArg(v_x_3023_, v_x_4004__boxed_3026_, v_x_3025_);
lean_dec_ref(v_x_3025_);
lean_dec_ref(v_x_3023_);
return v_res_3027_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0___redArg(lean_object* v_x_3028_, lean_object* v_x_3029_){
_start:
{
lean_object* v_fst_3030_; lean_object* v_snd_3031_; uint64_t v___x_3032_; uint64_t v___x_3033_; uint64_t v___x_3034_; size_t v___x_3035_; lean_object* v___x_3036_; 
v_fst_3030_ = lean_ctor_get(v_x_3029_, 0);
v_snd_3031_ = lean_ctor_get(v_x_3029_, 1);
v___x_3032_ = lean_uint64_of_nat(v_fst_3030_);
v___x_3033_ = lean_uint64_of_nat(v_snd_3031_);
v___x_3034_ = lean_uint64_mix_hash(v___x_3032_, v___x_3033_);
v___x_3035_ = lean_uint64_to_usize(v___x_3034_);
v___x_3036_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0___redArg(v_x_3028_, v___x_3035_, v_x_3029_);
return v___x_3036_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0___redArg___boxed(lean_object* v_x_3037_, lean_object* v_x_3038_){
_start:
{
lean_object* v_res_3039_; 
v_res_3039_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0___redArg(v_x_3037_, v_x_3038_);
lean_dec_ref(v_x_3038_);
lean_dec_ref(v_x_3037_);
return v_res_3039_;
}
}
lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__1(lean_object* v_u_3040_, lean_object* v_v_3041_, lean_object* v_k_3042_, lean_object* v_as_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_){
_start:
{
if (lean_obj_tag(v_as_3043_) == 0)
{
lean_object* v___x_3056_; lean_object* v___x_3057_; 
lean_dec_ref(v_k_3042_);
lean_dec(v_v_3041_);
lean_dec(v_u_3040_);
v___x_3056_ = lean_box(0);
v___x_3057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3057_, 0, v___x_3056_);
return v___x_3057_;
}
else
{
lean_object* v_head_3058_; lean_object* v_tail_3059_; lean_object* v_fst_3060_; lean_object* v_snd_3061_; lean_object* v___x_3062_; 
v_head_3058_ = lean_ctor_get(v_as_3043_, 0);
lean_inc(v_head_3058_);
v_tail_3059_ = lean_ctor_get(v_as_3043_, 1);
lean_inc(v_tail_3059_);
lean_dec_ref_known(v_as_3043_, 2);
v_fst_3060_ = lean_ctor_get(v_head_3058_, 0);
lean_inc(v_fst_3060_);
v_snd_3061_ = lean_ctor_get(v_head_3058_, 1);
lean_inc(v_snd_3061_);
lean_dec(v_head_3058_);
lean_inc_ref(v_k_3042_);
lean_inc(v_v_3041_);
lean_inc(v_u_3040_);
v___x_3062_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse(v_u_3040_, v_v_3041_, v_k_3042_, v_fst_3060_, v_snd_3061_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_);
if (lean_obj_tag(v___x_3062_) == 0)
{
lean_dec_ref_known(v___x_3062_, 1);
v_as_3043_ = v_tail_3059_;
goto _start;
}
else
{
lean_dec(v_tail_3059_);
lean_dec_ref(v_k_3042_);
lean_dec(v_v_3041_);
lean_dec(v_u_3040_);
return v___x_3062_;
}
}
}
}
LEAN_EXPORT void l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_3040_ = stack[0].m_obj;
lean_object* v_v_3041_ = stack[1].m_obj;
lean_object* v_k_3042_ = stack[2].m_obj;
lean_object* v_as_3043_ = stack[3].m_obj;
lean_object* v___y_3044_ = stack[4].m_obj;
lean_object* v___y_3045_ = stack[5].m_obj;
lean_object* v___y_3046_ = stack[6].m_obj;
lean_object* v___y_3047_ = stack[7].m_obj;
lean_object* v___y_3048_ = stack[8].m_obj;
lean_object* v___y_3049_ = stack[9].m_obj;
lean_object* v___y_3050_ = stack[10].m_obj;
lean_object* v___y_3051_ = stack[11].m_obj;
lean_object* v___y_3052_ = stack[12].m_obj;
lean_object* v___y_3053_ = stack[13].m_obj;
lean_object* v___y_3054_ = stack[14].m_obj;
lean_object* v_res_3064_;
v_res_3064_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__1(v_u_3040_, v_v_3041_, v_k_3042_, v_as_3043_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_);
stack->m_obj
 = v_res_3064_;
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__1___boxed(lean_object* v_u_3065_, lean_object* v_v_3066_, lean_object* v_k_3067_, lean_object* v_as_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_){
_start:
{
lean_object* v_res_3081_; 
v_res_3081_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__1(v_u_3065_, v_v_3066_, v_k_3067_, v_as_3068_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_);
lean_dec(v___y_3079_);
lean_dec_ref(v___y_3078_);
lean_dec(v___y_3077_);
lean_dec_ref(v___y_3076_);
lean_dec(v___y_3075_);
lean_dec_ref(v___y_3074_);
lean_dec(v___y_3073_);
lean_dec_ref(v___y_3072_);
lean_dec(v___y_3071_);
lean_dec(v___y_3070_);
lean_dec(v___y_3069_);
return v_res_3081_;
}
}
lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__2(lean_object* v_u_3082_, lean_object* v_v_3083_, lean_object* v_k_3084_, lean_object* v_as_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_){
_start:
{
if (lean_obj_tag(v_as_3085_) == 0)
{
lean_object* v___x_3098_; lean_object* v___x_3099_; 
lean_dec_ref(v_k_3084_);
lean_dec(v_v_3083_);
lean_dec(v_u_3082_);
v___x_3098_ = lean_box(0);
v___x_3099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3099_, 0, v___x_3098_);
return v___x_3099_;
}
else
{
lean_object* v_head_3100_; lean_object* v_tail_3101_; lean_object* v_fst_3102_; lean_object* v_snd_3103_; lean_object* v___x_3104_; 
v_head_3100_ = lean_ctor_get(v_as_3085_, 0);
lean_inc(v_head_3100_);
v_tail_3101_ = lean_ctor_get(v_as_3085_, 1);
lean_inc(v_tail_3101_);
lean_dec_ref_known(v_as_3085_, 2);
v_fst_3102_ = lean_ctor_get(v_head_3100_, 0);
lean_inc(v_fst_3102_);
v_snd_3103_ = lean_ctor_get(v_head_3100_, 1);
lean_inc(v_snd_3103_);
lean_dec(v_head_3100_);
lean_inc_ref(v_k_3084_);
lean_inc(v_v_3083_);
lean_inc(v_u_3082_);
v___x_3104_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue(v_u_3082_, v_v_3083_, v_k_3084_, v_fst_3102_, v_snd_3103_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_);
if (lean_obj_tag(v___x_3104_) == 0)
{
lean_dec_ref_known(v___x_3104_, 1);
v_as_3085_ = v_tail_3101_;
goto _start;
}
else
{
lean_dec(v_tail_3101_);
lean_dec_ref(v_k_3084_);
lean_dec(v_v_3083_);
lean_dec(v_u_3082_);
return v___x_3104_;
}
}
}
}
LEAN_EXPORT void l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_3082_ = stack[0].m_obj;
lean_object* v_v_3083_ = stack[1].m_obj;
lean_object* v_k_3084_ = stack[2].m_obj;
lean_object* v_as_3085_ = stack[3].m_obj;
lean_object* v___y_3086_ = stack[4].m_obj;
lean_object* v___y_3087_ = stack[5].m_obj;
lean_object* v___y_3088_ = stack[6].m_obj;
lean_object* v___y_3089_ = stack[7].m_obj;
lean_object* v___y_3090_ = stack[8].m_obj;
lean_object* v___y_3091_ = stack[9].m_obj;
lean_object* v___y_3092_ = stack[10].m_obj;
lean_object* v___y_3093_ = stack[11].m_obj;
lean_object* v___y_3094_ = stack[12].m_obj;
lean_object* v___y_3095_ = stack[13].m_obj;
lean_object* v___y_3096_ = stack[14].m_obj;
lean_object* v_res_3106_;
v_res_3106_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__2(v_u_3082_, v_v_3083_, v_k_3084_, v_as_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_);
stack->m_obj
 = v_res_3106_;
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__2___boxed(lean_object* v_u_3107_, lean_object* v_v_3108_, lean_object* v_k_3109_, lean_object* v_as_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_){
_start:
{
lean_object* v_res_3123_; 
v_res_3123_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__2(v_u_3107_, v_v_3108_, v_k_3109_, v_as_3110_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_);
lean_dec(v___y_3121_);
lean_dec_ref(v___y_3120_);
lean_dec(v___y_3119_);
lean_dec_ref(v___y_3118_);
lean_dec(v___y_3117_);
lean_dec_ref(v___y_3116_);
lean_dec(v___y_3115_);
lean_dec_ref(v___y_3114_);
lean_dec(v___y_3113_);
lean_dec(v___y_3112_);
lean_dec(v___y_3111_);
return v_res_3123_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate(lean_object* v_u_3124_, lean_object* v_v_3125_, lean_object* v_k_3126_, lean_object* v_a_3127_, lean_object* v_a_3128_, lean_object* v_a_3129_, lean_object* v_a_3130_, lean_object* v_a_3131_, lean_object* v_a_3132_, lean_object* v_a_3133_, lean_object* v_a_3134_, lean_object* v_a_3135_, lean_object* v_a_3136_, lean_object* v_a_3137_){
_start:
{
lean_object* v___x_3157_; 
v___x_3157_ = l_Lean_Meta_Grind_Order_getStruct___redArg(v_a_3127_, v_a_3128_, v_a_3136_);
if (lean_obj_tag(v___x_3157_) == 0)
{
lean_object* v_a_3158_; lean_object* v_cnstrsOf_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; 
v_a_3158_ = lean_ctor_get(v___x_3157_, 0);
lean_inc(v_a_3158_);
lean_dec_ref_known(v___x_3157_, 1);
v_cnstrsOf_3159_ = lean_ctor_get(v_a_3158_, 4);
lean_inc_ref(v_cnstrsOf_3159_);
lean_dec(v_a_3158_);
lean_inc(v_v_3125_);
lean_inc(v_u_3124_);
v___x_3160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3160_, 0, v_u_3124_);
lean_ctor_set(v___x_3160_, 1, v_v_3125_);
v___x_3161_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0___redArg(v_cnstrsOf_3159_, v___x_3160_);
lean_dec_ref_known(v___x_3160_, 2);
lean_dec_ref(v_cnstrsOf_3159_);
if (lean_obj_tag(v___x_3161_) == 1)
{
lean_object* v_val_3162_; lean_object* v___x_3163_; 
v_val_3162_ = lean_ctor_get(v___x_3161_, 0);
lean_inc(v_val_3162_);
lean_dec_ref_known(v___x_3161_, 1);
lean_inc_ref(v_k_3126_);
lean_inc(v_v_3125_);
lean_inc(v_u_3124_);
v___x_3163_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__2(v_u_3124_, v_v_3125_, v_k_3126_, v_val_3162_, v_a_3127_, v_a_3128_, v_a_3129_, v_a_3130_, v_a_3131_, v_a_3132_, v_a_3133_, v_a_3134_, v_a_3135_, v_a_3136_, v_a_3137_);
if (lean_obj_tag(v___x_3163_) == 0)
{
lean_dec_ref_known(v___x_3163_, 1);
goto v___jp_3139_;
}
else
{
lean_dec_ref(v_k_3126_);
lean_dec(v_v_3125_);
lean_dec(v_u_3124_);
return v___x_3163_;
}
}
else
{
lean_dec(v___x_3161_);
goto v___jp_3139_;
}
}
else
{
lean_object* v_a_3164_; lean_object* v___x_3166_; uint8_t v_isShared_3167_; uint8_t v_isSharedCheck_3171_; 
lean_dec_ref(v_k_3126_);
lean_dec(v_v_3125_);
lean_dec(v_u_3124_);
v_a_3164_ = lean_ctor_get(v___x_3157_, 0);
v_isSharedCheck_3171_ = !lean_is_exclusive(v___x_3157_);
if (v_isSharedCheck_3171_ == 0)
{
v___x_3166_ = v___x_3157_;
v_isShared_3167_ = v_isSharedCheck_3171_;
goto v_resetjp_3165_;
}
else
{
lean_inc(v_a_3164_);
lean_dec(v___x_3157_);
v___x_3166_ = lean_box(0);
v_isShared_3167_ = v_isSharedCheck_3171_;
goto v_resetjp_3165_;
}
v_resetjp_3165_:
{
lean_object* v___x_3169_; 
if (v_isShared_3167_ == 0)
{
v___x_3169_ = v___x_3166_;
goto v_reusejp_3168_;
}
else
{
lean_object* v_reuseFailAlloc_3170_; 
v_reuseFailAlloc_3170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3170_, 0, v_a_3164_);
v___x_3169_ = v_reuseFailAlloc_3170_;
goto v_reusejp_3168_;
}
v_reusejp_3168_:
{
return v___x_3169_;
}
}
}
v___jp_3139_:
{
lean_object* v___x_3140_; 
v___x_3140_ = l_Lean_Meta_Grind_Order_getStruct___redArg(v_a_3127_, v_a_3128_, v_a_3136_);
if (lean_obj_tag(v___x_3140_) == 0)
{
lean_object* v_a_3141_; lean_object* v_cnstrsOf_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; 
v_a_3141_ = lean_ctor_get(v___x_3140_, 0);
lean_inc(v_a_3141_);
lean_dec_ref_known(v___x_3140_, 1);
v_cnstrsOf_3142_ = lean_ctor_get(v_a_3141_, 4);
lean_inc_ref(v_cnstrsOf_3142_);
lean_dec(v_a_3141_);
lean_inc(v_u_3124_);
lean_inc(v_v_3125_);
v___x_3143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3143_, 0, v_v_3125_);
lean_ctor_set(v___x_3143_, 1, v_u_3124_);
v___x_3144_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0___redArg(v_cnstrsOf_3142_, v___x_3143_);
lean_dec_ref_known(v___x_3143_, 2);
lean_dec_ref(v_cnstrsOf_3142_);
if (lean_obj_tag(v___x_3144_) == 1)
{
lean_object* v_val_3145_; lean_object* v___x_3146_; 
v_val_3145_ = lean_ctor_get(v___x_3144_, 0);
lean_inc(v_val_3145_);
lean_dec_ref_known(v___x_3144_, 1);
lean_inc_ref(v_k_3126_);
lean_inc(v_v_3125_);
lean_inc(v_u_3124_);
v___x_3146_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__1(v_u_3124_, v_v_3125_, v_k_3126_, v_val_3145_, v_a_3127_, v_a_3128_, v_a_3129_, v_a_3130_, v_a_3131_, v_a_3132_, v_a_3133_, v_a_3134_, v_a_3135_, v_a_3136_, v_a_3137_);
if (lean_obj_tag(v___x_3146_) == 0)
{
lean_object* v___x_3147_; 
lean_dec_ref_known(v___x_3146_, 1);
v___x_3147_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq(v_u_3124_, v_v_3125_, v_k_3126_, v_a_3127_, v_a_3128_, v_a_3129_, v_a_3130_, v_a_3131_, v_a_3132_, v_a_3133_, v_a_3134_, v_a_3135_, v_a_3136_, v_a_3137_);
lean_dec_ref(v_k_3126_);
return v___x_3147_;
}
else
{
lean_dec_ref(v_k_3126_);
lean_dec(v_v_3125_);
lean_dec(v_u_3124_);
return v___x_3146_;
}
}
else
{
lean_object* v___x_3148_; 
lean_dec(v___x_3144_);
v___x_3148_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq(v_u_3124_, v_v_3125_, v_k_3126_, v_a_3127_, v_a_3128_, v_a_3129_, v_a_3130_, v_a_3131_, v_a_3132_, v_a_3133_, v_a_3134_, v_a_3135_, v_a_3136_, v_a_3137_);
lean_dec_ref(v_k_3126_);
return v___x_3148_;
}
}
else
{
lean_object* v_a_3149_; lean_object* v___x_3151_; uint8_t v_isShared_3152_; uint8_t v_isSharedCheck_3156_; 
lean_dec_ref(v_k_3126_);
lean_dec(v_v_3125_);
lean_dec(v_u_3124_);
v_a_3149_ = lean_ctor_get(v___x_3140_, 0);
v_isSharedCheck_3156_ = !lean_is_exclusive(v___x_3140_);
if (v_isSharedCheck_3156_ == 0)
{
v___x_3151_ = v___x_3140_;
v_isShared_3152_ = v_isSharedCheck_3156_;
goto v_resetjp_3150_;
}
else
{
lean_inc(v_a_3149_);
lean_dec(v___x_3140_);
v___x_3151_ = lean_box(0);
v_isShared_3152_ = v_isSharedCheck_3156_;
goto v_resetjp_3150_;
}
v_resetjp_3150_:
{
lean_object* v___x_3154_; 
if (v_isShared_3152_ == 0)
{
v___x_3154_ = v___x_3151_;
goto v_reusejp_3153_;
}
else
{
lean_object* v_reuseFailAlloc_3155_; 
v_reuseFailAlloc_3155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3155_, 0, v_a_3149_);
v___x_3154_ = v_reuseFailAlloc_3155_;
goto v_reusejp_3153_;
}
v_reusejp_3153_:
{
return v___x_3154_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_3124_ = stack[0].m_obj;
lean_object* v_v_3125_ = stack[1].m_obj;
lean_object* v_k_3126_ = stack[2].m_obj;
lean_object* v_a_3127_ = stack[3].m_obj;
lean_object* v_a_3128_ = stack[4].m_obj;
lean_object* v_a_3129_ = stack[5].m_obj;
lean_object* v_a_3130_ = stack[6].m_obj;
lean_object* v_a_3131_ = stack[7].m_obj;
lean_object* v_a_3132_ = stack[8].m_obj;
lean_object* v_a_3133_ = stack[9].m_obj;
lean_object* v_a_3134_ = stack[10].m_obj;
lean_object* v_a_3135_ = stack[11].m_obj;
lean_object* v_a_3136_ = stack[12].m_obj;
lean_object* v_a_3137_ = stack[13].m_obj;
lean_object* v_res_3172_;
v_res_3172_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate(v_u_3124_, v_v_3125_, v_k_3126_, v_a_3127_, v_a_3128_, v_a_3129_, v_a_3130_, v_a_3131_, v_a_3132_, v_a_3133_, v_a_3134_, v_a_3135_, v_a_3136_, v_a_3137_);
stack->m_obj
 = v_res_3172_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate___boxed(lean_object* v_u_3173_, lean_object* v_v_3174_, lean_object* v_k_3175_, lean_object* v_a_3176_, lean_object* v_a_3177_, lean_object* v_a_3178_, lean_object* v_a_3179_, lean_object* v_a_3180_, lean_object* v_a_3181_, lean_object* v_a_3182_, lean_object* v_a_3183_, lean_object* v_a_3184_, lean_object* v_a_3185_, lean_object* v_a_3186_, lean_object* v_a_3187_){
_start:
{
lean_object* v_res_3188_; 
v_res_3188_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate(v_u_3173_, v_v_3174_, v_k_3175_, v_a_3176_, v_a_3177_, v_a_3178_, v_a_3179_, v_a_3180_, v_a_3181_, v_a_3182_, v_a_3183_, v_a_3184_, v_a_3185_, v_a_3186_);
lean_dec(v_a_3186_);
lean_dec_ref(v_a_3185_);
lean_dec(v_a_3184_);
lean_dec_ref(v_a_3183_);
lean_dec(v_a_3182_);
lean_dec_ref(v_a_3181_);
lean_dec(v_a_3180_);
lean_dec_ref(v_a_3179_);
lean_dec(v_a_3178_);
lean_dec(v_a_3177_);
lean_dec(v_a_3176_);
return v_res_3188_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0(lean_object* v_00_u03b2_3189_, lean_object* v_x_3190_, lean_object* v_x_3191_){
_start:
{
lean_object* v___x_3192_; 
v___x_3192_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0___redArg(v_x_3190_, v_x_3191_);
return v___x_3192_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0___boxed(lean_object* v_00_u03b2_3193_, lean_object* v_x_3194_, lean_object* v_x_3195_){
_start:
{
lean_object* v_res_3196_; 
v_res_3196_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0(v_00_u03b2_3193_, v_x_3194_, v_x_3195_);
lean_dec_ref(v_x_3195_);
lean_dec_ref(v_x_3194_);
return v_res_3196_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0(lean_object* v_00_u03b2_3197_, lean_object* v_x_3198_, size_t v_x_3199_, lean_object* v_x_3200_){
_start:
{
lean_object* v___x_3201_; 
v___x_3201_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0___redArg(v_x_3198_, v_x_3199_, v_x_3200_);
return v___x_3201_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3198_ = stack[1].m_obj;
size_t v_x_3199_ = stack[2].m_num;
lean_object* v_x_3200_ = stack[3].m_obj;
lean_object* v_res_3202_;
v_res_3202_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0(lean_box(0), v_x_3198_, v_x_3199_, v_x_3200_);
stack->m_obj
 = v_res_3202_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3203_, lean_object* v_x_3204_, lean_object* v_x_3205_, lean_object* v_x_3206_){
_start:
{
size_t v_x_4412__boxed_3207_; lean_object* v_res_3208_; 
v_x_4412__boxed_3207_ = lean_unbox_usize(v_x_3205_);
lean_dec(v_x_3205_);
v_res_3208_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0(v_00_u03b2_3203_, v_x_3204_, v_x_4412__boxed_3207_, v_x_3206_);
lean_dec_ref(v_x_3206_);
lean_dec_ref(v_x_3204_);
return v_res_3208_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3209_, lean_object* v_keys_3210_, lean_object* v_vals_3211_, lean_object* v_heq_3212_, lean_object* v_i_3213_, lean_object* v_k_3214_){
_start:
{
lean_object* v___x_3215_; 
v___x_3215_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1___redArg(v_keys_3210_, v_vals_3211_, v_i_3213_, v_k_3214_);
return v___x_3215_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_3216_, lean_object* v_keys_3217_, lean_object* v_vals_3218_, lean_object* v_heq_3219_, lean_object* v_i_3220_, lean_object* v_k_3221_){
_start:
{
lean_object* v_res_3222_; 
v_res_3222_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1(v_00_u03b2_3216_, v_keys_3217_, v_vals_3218_, v_heq_3219_, v_i_3220_, v_k_3221_);
lean_dec_ref(v_k_3221_);
lean_dec_ref(v_vals_3218_);
lean_dec_ref(v_keys_3217_);
return v_res_3222_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_updateIfShorter(lean_object* v_u_3223_, lean_object* v_v_3224_, lean_object* v_k_3225_, lean_object* v_w_3226_, lean_object* v_a_3227_, lean_object* v_a_3228_, lean_object* v_a_3229_, lean_object* v_a_3230_, lean_object* v_a_3231_, lean_object* v_a_3232_, lean_object* v_a_3233_, lean_object* v_a_3234_, lean_object* v_a_3235_, lean_object* v_a_3236_, lean_object* v_a_3237_){
_start:
{
lean_object* v___x_3239_; 
v___x_3239_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isShorter___redArg(v_u_3223_, v_v_3224_, v_k_3225_, v_a_3227_, v_a_3228_, v_a_3236_);
if (lean_obj_tag(v___x_3239_) == 0)
{
lean_object* v_a_3240_; lean_object* v___x_3242_; uint8_t v_isShared_3243_; uint8_t v_isSharedCheck_3262_; 
v_a_3240_ = lean_ctor_get(v___x_3239_, 0);
v_isSharedCheck_3262_ = !lean_is_exclusive(v___x_3239_);
if (v_isSharedCheck_3262_ == 0)
{
v___x_3242_ = v___x_3239_;
v_isShared_3243_ = v_isSharedCheck_3262_;
goto v_resetjp_3241_;
}
else
{
lean_inc(v_a_3240_);
lean_dec(v___x_3239_);
v___x_3242_ = lean_box(0);
v_isShared_3243_ = v_isSharedCheck_3262_;
goto v_resetjp_3241_;
}
v_resetjp_3241_:
{
uint8_t v___x_3244_; 
v___x_3244_ = lean_unbox(v_a_3240_);
lean_dec(v_a_3240_);
if (v___x_3244_ == 0)
{
lean_object* v___x_3245_; lean_object* v___x_3247_; 
lean_dec_ref(v_k_3225_);
lean_dec(v_v_3224_);
lean_dec(v_u_3223_);
v___x_3245_ = lean_box(0);
if (v_isShared_3243_ == 0)
{
lean_ctor_set(v___x_3242_, 0, v___x_3245_);
v___x_3247_ = v___x_3242_;
goto v_reusejp_3246_;
}
else
{
lean_object* v_reuseFailAlloc_3248_; 
v_reuseFailAlloc_3248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3248_, 0, v___x_3245_);
v___x_3247_ = v_reuseFailAlloc_3248_;
goto v_reusejp_3246_;
}
v_reusejp_3246_:
{
return v___x_3247_;
}
}
else
{
lean_object* v___x_3249_; 
lean_del_object(v___x_3242_);
lean_inc_ref(v_k_3225_);
lean_inc(v_v_3224_);
lean_inc(v_u_3223_);
v___x_3249_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist___redArg(v_u_3223_, v_v_3224_, v_k_3225_, v_a_3227_, v_a_3228_);
if (lean_obj_tag(v___x_3249_) == 0)
{
lean_object* v___x_3250_; 
lean_dec_ref_known(v___x_3249_, 1);
v___x_3250_ = l_Lean_Meta_Grind_Order_getProof___redArg(v_w_3226_, v_v_3224_, v_a_3227_, v_a_3228_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_);
if (lean_obj_tag(v___x_3250_) == 0)
{
lean_object* v_a_3251_; lean_object* v___x_3252_; 
v_a_3251_ = lean_ctor_get(v___x_3250_, 0);
lean_inc(v_a_3251_);
lean_dec_ref_known(v___x_3250_, 1);
lean_inc(v_v_3224_);
lean_inc(v_u_3223_);
v___x_3252_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___redArg(v_u_3223_, v_v_3224_, v_a_3251_, v_a_3227_, v_a_3228_);
if (lean_obj_tag(v___x_3252_) == 0)
{
lean_object* v___x_3253_; 
lean_dec_ref_known(v___x_3252_, 1);
v___x_3253_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate(v_u_3223_, v_v_3224_, v_k_3225_, v_a_3227_, v_a_3228_, v_a_3229_, v_a_3230_, v_a_3231_, v_a_3232_, v_a_3233_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_);
return v___x_3253_;
}
else
{
lean_dec_ref(v_k_3225_);
lean_dec(v_v_3224_);
lean_dec(v_u_3223_);
return v___x_3252_;
}
}
else
{
lean_object* v_a_3254_; lean_object* v___x_3256_; uint8_t v_isShared_3257_; uint8_t v_isSharedCheck_3261_; 
lean_dec_ref(v_k_3225_);
lean_dec(v_v_3224_);
lean_dec(v_u_3223_);
v_a_3254_ = lean_ctor_get(v___x_3250_, 0);
v_isSharedCheck_3261_ = !lean_is_exclusive(v___x_3250_);
if (v_isSharedCheck_3261_ == 0)
{
v___x_3256_ = v___x_3250_;
v_isShared_3257_ = v_isSharedCheck_3261_;
goto v_resetjp_3255_;
}
else
{
lean_inc(v_a_3254_);
lean_dec(v___x_3250_);
v___x_3256_ = lean_box(0);
v_isShared_3257_ = v_isSharedCheck_3261_;
goto v_resetjp_3255_;
}
v_resetjp_3255_:
{
lean_object* v___x_3259_; 
if (v_isShared_3257_ == 0)
{
v___x_3259_ = v___x_3256_;
goto v_reusejp_3258_;
}
else
{
lean_object* v_reuseFailAlloc_3260_; 
v_reuseFailAlloc_3260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3260_, 0, v_a_3254_);
v___x_3259_ = v_reuseFailAlloc_3260_;
goto v_reusejp_3258_;
}
v_reusejp_3258_:
{
return v___x_3259_;
}
}
}
}
else
{
lean_dec_ref(v_k_3225_);
lean_dec(v_v_3224_);
lean_dec(v_u_3223_);
return v___x_3249_;
}
}
}
}
else
{
lean_object* v_a_3263_; lean_object* v___x_3265_; uint8_t v_isShared_3266_; uint8_t v_isSharedCheck_3270_; 
lean_dec_ref(v_k_3225_);
lean_dec(v_v_3224_);
lean_dec(v_u_3223_);
v_a_3263_ = lean_ctor_get(v___x_3239_, 0);
v_isSharedCheck_3270_ = !lean_is_exclusive(v___x_3239_);
if (v_isSharedCheck_3270_ == 0)
{
v___x_3265_ = v___x_3239_;
v_isShared_3266_ = v_isSharedCheck_3270_;
goto v_resetjp_3264_;
}
else
{
lean_inc(v_a_3263_);
lean_dec(v___x_3239_);
v___x_3265_ = lean_box(0);
v_isShared_3266_ = v_isSharedCheck_3270_;
goto v_resetjp_3264_;
}
v_resetjp_3264_:
{
lean_object* v___x_3268_; 
if (v_isShared_3266_ == 0)
{
v___x_3268_ = v___x_3265_;
goto v_reusejp_3267_;
}
else
{
lean_object* v_reuseFailAlloc_3269_; 
v_reuseFailAlloc_3269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3269_, 0, v_a_3263_);
v___x_3268_ = v_reuseFailAlloc_3269_;
goto v_reusejp_3267_;
}
v_reusejp_3267_:
{
return v___x_3268_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_updateIfShorter_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_3223_ = stack[0].m_obj;
lean_object* v_v_3224_ = stack[1].m_obj;
lean_object* v_k_3225_ = stack[2].m_obj;
lean_object* v_w_3226_ = stack[3].m_obj;
lean_object* v_a_3227_ = stack[4].m_obj;
lean_object* v_a_3228_ = stack[5].m_obj;
lean_object* v_a_3229_ = stack[6].m_obj;
lean_object* v_a_3230_ = stack[7].m_obj;
lean_object* v_a_3231_ = stack[8].m_obj;
lean_object* v_a_3232_ = stack[9].m_obj;
lean_object* v_a_3233_ = stack[10].m_obj;
lean_object* v_a_3234_ = stack[11].m_obj;
lean_object* v_a_3235_ = stack[12].m_obj;
lean_object* v_a_3236_ = stack[13].m_obj;
lean_object* v_a_3237_ = stack[14].m_obj;
lean_object* v_res_3271_;
v_res_3271_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_updateIfShorter(v_u_3223_, v_v_3224_, v_k_3225_, v_w_3226_, v_a_3227_, v_a_3228_, v_a_3229_, v_a_3230_, v_a_3231_, v_a_3232_, v_a_3233_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_);
stack->m_obj
 = v_res_3271_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_updateIfShorter___boxed(lean_object* v_u_3272_, lean_object* v_v_3273_, lean_object* v_k_3274_, lean_object* v_w_3275_, lean_object* v_a_3276_, lean_object* v_a_3277_, lean_object* v_a_3278_, lean_object* v_a_3279_, lean_object* v_a_3280_, lean_object* v_a_3281_, lean_object* v_a_3282_, lean_object* v_a_3283_, lean_object* v_a_3284_, lean_object* v_a_3285_, lean_object* v_a_3286_, lean_object* v_a_3287_){
_start:
{
lean_object* v_res_3288_; 
v_res_3288_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_updateIfShorter(v_u_3272_, v_v_3273_, v_k_3274_, v_w_3275_, v_a_3276_, v_a_3277_, v_a_3278_, v_a_3279_, v_a_3280_, v_a_3281_, v_a_3282_, v_a_3283_, v_a_3284_, v_a_3285_, v_a_3286_);
lean_dec(v_a_3286_);
lean_dec_ref(v_a_3285_);
lean_dec(v_a_3284_);
lean_dec_ref(v_a_3283_);
lean_dec(v_a_3282_);
lean_dec_ref(v_a_3281_);
lean_dec(v_a_3280_);
lean_dec_ref(v_a_3279_);
lean_dec(v_a_3278_);
lean_dec(v_a_3277_);
lean_dec(v_a_3276_);
lean_dec(v_w_3275_);
return v_res_3288_;
}
}
lean_object* l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0(lean_object* v___x_3289_, lean_object* v_i_3290_, lean_object* v_v_3291_, lean_object* v_x_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_){
_start:
{
if (lean_obj_tag(v_x_3292_) == 0)
{
lean_object* v___x_3305_; lean_object* v___x_3306_; 
lean_dec(v_i_3290_);
v___x_3305_ = lean_box(0);
v___x_3306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3306_, 0, v___x_3305_);
return v___x_3306_;
}
else
{
lean_object* v_key_3307_; lean_object* v_value_3308_; lean_object* v_tail_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; 
v_key_3307_ = lean_ctor_get(v_x_3292_, 0);
lean_inc(v_key_3307_);
v_value_3308_ = lean_ctor_get(v_x_3292_, 1);
lean_inc(v_value_3308_);
v_tail_3309_ = lean_ctor_get(v_x_3292_, 2);
lean_inc(v_tail_3309_);
lean_dec_ref_known(v_x_3292_, 3);
v___x_3310_ = l_Lean_Meta_Grind_Order_Weight_add(v___x_3289_, v_value_3308_);
lean_inc(v_i_3290_);
v___x_3311_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_updateIfShorter(v_i_3290_, v_key_3307_, v___x_3310_, v_v_3291_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_, v___y_3303_);
if (lean_obj_tag(v___x_3311_) == 0)
{
lean_dec_ref_known(v___x_3311_, 1);
v_x_3292_ = v_tail_3309_;
goto _start;
}
else
{
lean_dec(v_tail_3309_);
lean_dec(v_i_3290_);
return v___x_3311_;
}
}
}
}
LEAN_EXPORT void l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3289_ = stack[0].m_obj;
lean_object* v_i_3290_ = stack[1].m_obj;
lean_object* v_v_3291_ = stack[2].m_obj;
lean_object* v_x_3292_ = stack[3].m_obj;
lean_object* v___y_3293_ = stack[4].m_obj;
lean_object* v___y_3294_ = stack[5].m_obj;
lean_object* v___y_3295_ = stack[6].m_obj;
lean_object* v___y_3296_ = stack[7].m_obj;
lean_object* v___y_3297_ = stack[8].m_obj;
lean_object* v___y_3298_ = stack[9].m_obj;
lean_object* v___y_3299_ = stack[10].m_obj;
lean_object* v___y_3300_ = stack[11].m_obj;
lean_object* v___y_3301_ = stack[12].m_obj;
lean_object* v___y_3302_ = stack[13].m_obj;
lean_object* v___y_3303_ = stack[14].m_obj;
lean_object* v_res_3313_;
v_res_3313_ = l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0(v___x_3289_, v_i_3290_, v_v_3291_, v_x_3292_, v___y_3293_, v___y_3294_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_, v___y_3303_);
stack->m_obj
 = v_res_3313_;
}
LEAN_EXPORT lean_object* l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0___boxed(lean_object* v___x_3314_, lean_object* v_i_3315_, lean_object* v_v_3316_, lean_object* v_x_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_){
_start:
{
lean_object* v_res_3330_; 
v_res_3330_ = l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0(v___x_3314_, v_i_3315_, v_v_3316_, v_x_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_);
lean_dec(v___y_3328_);
lean_dec_ref(v___y_3327_);
lean_dec(v___y_3326_);
lean_dec_ref(v___y_3325_);
lean_dec(v___y_3324_);
lean_dec_ref(v___y_3323_);
lean_dec(v___y_3322_);
lean_dec_ref(v___y_3321_);
lean_dec(v___y_3320_);
lean_dec(v___y_3319_);
lean_dec(v___y_3318_);
lean_dec(v_v_3316_);
lean_dec_ref(v___x_3314_);
return v_res_3330_;
}
}
lean_object* l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__1(lean_object* v_k_3331_, lean_object* v_v_3332_, lean_object* v_u_3333_, lean_object* v_x_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_){
_start:
{
if (lean_obj_tag(v_x_3334_) == 0)
{
lean_object* v___x_3347_; lean_object* v___x_3348_; 
lean_dec(v_v_3332_);
lean_dec_ref(v_k_3331_);
v___x_3347_ = lean_box(0);
v___x_3348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3348_, 0, v___x_3347_);
return v___x_3348_;
}
else
{
lean_object* v_key_3349_; lean_object* v_value_3350_; lean_object* v_tail_3351_; lean_object* v___y_3353_; lean_object* v___x_3355_; lean_object* v___x_3356_; 
v_key_3349_ = lean_ctor_get(v_x_3334_, 0);
lean_inc_n(v_key_3349_, 2);
v_value_3350_ = lean_ctor_get(v_x_3334_, 1);
lean_inc(v_value_3350_);
v_tail_3351_ = lean_ctor_get(v_x_3334_, 2);
lean_inc(v_tail_3351_);
lean_dec_ref_known(v_x_3334_, 3);
lean_inc_ref(v_k_3331_);
v___x_3355_ = l_Lean_Meta_Grind_Order_Weight_add(v_value_3350_, v_k_3331_);
lean_dec(v_value_3350_);
lean_inc_ref(v___x_3355_);
lean_inc(v_v_3332_);
v___x_3356_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_updateIfShorter(v_key_3349_, v_v_3332_, v___x_3355_, v_u_3333_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_);
if (lean_obj_tag(v___x_3356_) == 0)
{
lean_object* v___x_3357_; lean_object* v___x_3358_; 
lean_dec_ref_known(v___x_3356_, 1);
v___x_3357_ = lean_box(0);
v___x_3358_ = l_Lean_Meta_Grind_Order_getStruct___redArg(v___y_3335_, v___y_3336_, v___y_3344_);
if (lean_obj_tag(v___x_3358_) == 0)
{
lean_object* v_a_3359_; lean_object* v_targets_3360_; lean_object* v_size_3361_; uint8_t v___x_3362_; 
v_a_3359_ = lean_ctor_get(v___x_3358_, 0);
lean_inc(v_a_3359_);
lean_dec_ref_known(v___x_3358_, 1);
v_targets_3360_ = lean_ctor_get(v_a_3359_, 6);
lean_inc_ref(v_targets_3360_);
lean_dec(v_a_3359_);
v_size_3361_ = lean_ctor_get(v_targets_3360_, 2);
v___x_3362_ = lean_nat_dec_lt(v_v_3332_, v_size_3361_);
if (v___x_3362_ == 0)
{
lean_object* v___x_3363_; lean_object* v___x_3364_; 
lean_dec_ref(v_targets_3360_);
v___x_3363_ = l_outOfBounds___redArg(v___x_3357_);
v___x_3364_ = l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0(v___x_3355_, v_key_3349_, v_v_3332_, v___x_3363_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_);
lean_dec_ref(v___x_3355_);
v___y_3353_ = v___x_3364_;
goto v___jp_3352_;
}
else
{
lean_object* v___x_3365_; lean_object* v___x_3366_; 
v___x_3365_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3357_, v_targets_3360_, v_v_3332_);
lean_dec_ref(v_targets_3360_);
v___x_3366_ = l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0(v___x_3355_, v_key_3349_, v_v_3332_, v___x_3365_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_);
lean_dec_ref(v___x_3355_);
v___y_3353_ = v___x_3366_;
goto v___jp_3352_;
}
}
else
{
lean_object* v_a_3367_; lean_object* v___x_3369_; uint8_t v_isShared_3370_; uint8_t v_isSharedCheck_3374_; 
lean_dec_ref(v___x_3355_);
lean_dec(v_tail_3351_);
lean_dec(v_key_3349_);
lean_dec(v_v_3332_);
lean_dec_ref(v_k_3331_);
v_a_3367_ = lean_ctor_get(v___x_3358_, 0);
v_isSharedCheck_3374_ = !lean_is_exclusive(v___x_3358_);
if (v_isSharedCheck_3374_ == 0)
{
v___x_3369_ = v___x_3358_;
v_isShared_3370_ = v_isSharedCheck_3374_;
goto v_resetjp_3368_;
}
else
{
lean_inc(v_a_3367_);
lean_dec(v___x_3358_);
v___x_3369_ = lean_box(0);
v_isShared_3370_ = v_isSharedCheck_3374_;
goto v_resetjp_3368_;
}
v_resetjp_3368_:
{
lean_object* v___x_3372_; 
if (v_isShared_3370_ == 0)
{
v___x_3372_ = v___x_3369_;
goto v_reusejp_3371_;
}
else
{
lean_object* v_reuseFailAlloc_3373_; 
v_reuseFailAlloc_3373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3373_, 0, v_a_3367_);
v___x_3372_ = v_reuseFailAlloc_3373_;
goto v_reusejp_3371_;
}
v_reusejp_3371_:
{
return v___x_3372_;
}
}
}
}
else
{
lean_dec_ref(v___x_3355_);
lean_dec(v_key_3349_);
v___y_3353_ = v___x_3356_;
goto v___jp_3352_;
}
v___jp_3352_:
{
if (lean_obj_tag(v___y_3353_) == 0)
{
lean_dec_ref_known(v___y_3353_, 1);
v_x_3334_ = v_tail_3351_;
goto _start;
}
else
{
lean_dec(v_tail_3351_);
lean_dec(v_v_3332_);
lean_dec_ref(v_k_3331_);
return v___y_3353_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_3331_ = stack[0].m_obj;
lean_object* v_v_3332_ = stack[1].m_obj;
lean_object* v_u_3333_ = stack[2].m_obj;
lean_object* v_x_3334_ = stack[3].m_obj;
lean_object* v___y_3335_ = stack[4].m_obj;
lean_object* v___y_3336_ = stack[5].m_obj;
lean_object* v___y_3337_ = stack[6].m_obj;
lean_object* v___y_3338_ = stack[7].m_obj;
lean_object* v___y_3339_ = stack[8].m_obj;
lean_object* v___y_3340_ = stack[9].m_obj;
lean_object* v___y_3341_ = stack[10].m_obj;
lean_object* v___y_3342_ = stack[11].m_obj;
lean_object* v___y_3343_ = stack[12].m_obj;
lean_object* v___y_3344_ = stack[13].m_obj;
lean_object* v___y_3345_ = stack[14].m_obj;
lean_object* v_res_3375_;
v_res_3375_ = l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__1(v_k_3331_, v_v_3332_, v_u_3333_, v_x_3334_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_);
stack->m_obj
 = v_res_3375_;
}
LEAN_EXPORT lean_object* l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__1___boxed(lean_object* v_k_3376_, lean_object* v_v_3377_, lean_object* v_u_3378_, lean_object* v_x_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_){
_start:
{
lean_object* v_res_3392_; 
v_res_3392_ = l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__1(v_k_3376_, v_v_3377_, v_u_3378_, v_x_3379_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_);
lean_dec(v___y_3390_);
lean_dec_ref(v___y_3389_);
lean_dec(v___y_3388_);
lean_dec_ref(v___y_3387_);
lean_dec(v___y_3386_);
lean_dec_ref(v___y_3385_);
lean_dec(v___y_3384_);
lean_dec_ref(v___y_3383_);
lean_dec(v___y_3382_);
lean_dec(v___y_3381_);
lean_dec(v___y_3380_);
lean_dec(v_u_3378_);
return v_res_3392_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update(lean_object* v_u_3393_, lean_object* v_v_3394_, lean_object* v_k_3395_, lean_object* v_a_3396_, lean_object* v_a_3397_, lean_object* v_a_3398_, lean_object* v_a_3399_, lean_object* v_a_3400_, lean_object* v_a_3401_, lean_object* v_a_3402_, lean_object* v_a_3403_, lean_object* v_a_3404_, lean_object* v_a_3405_, lean_object* v_a_3406_){
_start:
{
lean_object* v___y_3409_; lean_object* v___x_3428_; lean_object* v___x_3429_; 
v___x_3428_ = lean_box(0);
v___x_3429_ = l_Lean_Meta_Grind_Order_getStruct___redArg(v_a_3396_, v_a_3397_, v_a_3405_);
if (lean_obj_tag(v___x_3429_) == 0)
{
lean_object* v_a_3430_; lean_object* v_targets_3431_; lean_object* v_size_3432_; uint8_t v___x_3433_; 
v_a_3430_ = lean_ctor_get(v___x_3429_, 0);
lean_inc(v_a_3430_);
lean_dec_ref_known(v___x_3429_, 1);
v_targets_3431_ = lean_ctor_get(v_a_3430_, 6);
lean_inc_ref(v_targets_3431_);
lean_dec(v_a_3430_);
v_size_3432_ = lean_ctor_get(v_targets_3431_, 2);
v___x_3433_ = lean_nat_dec_lt(v_v_3394_, v_size_3432_);
if (v___x_3433_ == 0)
{
lean_object* v___x_3434_; lean_object* v___x_3435_; 
lean_dec_ref(v_targets_3431_);
v___x_3434_ = l_outOfBounds___redArg(v___x_3428_);
lean_inc(v_u_3393_);
v___x_3435_ = l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0(v_k_3395_, v_u_3393_, v_v_3394_, v___x_3434_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_, v_a_3405_, v_a_3406_);
v___y_3409_ = v___x_3435_;
goto v___jp_3408_;
}
else
{
lean_object* v___x_3436_; lean_object* v___x_3437_; 
v___x_3436_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3428_, v_targets_3431_, v_v_3394_);
lean_dec_ref(v_targets_3431_);
lean_inc(v_u_3393_);
v___x_3437_ = l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0(v_k_3395_, v_u_3393_, v_v_3394_, v___x_3436_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_, v_a_3405_, v_a_3406_);
v___y_3409_ = v___x_3437_;
goto v___jp_3408_;
}
}
else
{
lean_object* v_a_3438_; lean_object* v___x_3440_; uint8_t v_isShared_3441_; uint8_t v_isSharedCheck_3445_; 
lean_dec_ref(v_k_3395_);
lean_dec(v_v_3394_);
lean_dec(v_u_3393_);
v_a_3438_ = lean_ctor_get(v___x_3429_, 0);
v_isSharedCheck_3445_ = !lean_is_exclusive(v___x_3429_);
if (v_isSharedCheck_3445_ == 0)
{
v___x_3440_ = v___x_3429_;
v_isShared_3441_ = v_isSharedCheck_3445_;
goto v_resetjp_3439_;
}
else
{
lean_inc(v_a_3438_);
lean_dec(v___x_3429_);
v___x_3440_ = lean_box(0);
v_isShared_3441_ = v_isSharedCheck_3445_;
goto v_resetjp_3439_;
}
v_resetjp_3439_:
{
lean_object* v___x_3443_; 
if (v_isShared_3441_ == 0)
{
v___x_3443_ = v___x_3440_;
goto v_reusejp_3442_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v_a_3438_);
v___x_3443_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3442_;
}
v_reusejp_3442_:
{
return v___x_3443_;
}
}
}
v___jp_3408_:
{
if (lean_obj_tag(v___y_3409_) == 0)
{
lean_object* v___x_3410_; lean_object* v___x_3411_; 
lean_dec_ref_known(v___y_3409_, 1);
v___x_3410_ = lean_box(0);
v___x_3411_ = l_Lean_Meta_Grind_Order_getStruct___redArg(v_a_3396_, v_a_3397_, v_a_3405_);
if (lean_obj_tag(v___x_3411_) == 0)
{
lean_object* v_a_3412_; lean_object* v_sources_3413_; lean_object* v_size_3414_; uint8_t v___x_3415_; 
v_a_3412_ = lean_ctor_get(v___x_3411_, 0);
lean_inc(v_a_3412_);
lean_dec_ref_known(v___x_3411_, 1);
v_sources_3413_ = lean_ctor_get(v_a_3412_, 5);
lean_inc_ref(v_sources_3413_);
lean_dec(v_a_3412_);
v_size_3414_ = lean_ctor_get(v_sources_3413_, 2);
v___x_3415_ = lean_nat_dec_lt(v_u_3393_, v_size_3414_);
if (v___x_3415_ == 0)
{
lean_object* v___x_3416_; lean_object* v___x_3417_; 
lean_dec_ref(v_sources_3413_);
v___x_3416_ = l_outOfBounds___redArg(v___x_3410_);
v___x_3417_ = l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__1(v_k_3395_, v_v_3394_, v_u_3393_, v___x_3416_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_, v_a_3405_, v_a_3406_);
lean_dec(v_u_3393_);
return v___x_3417_;
}
else
{
lean_object* v___x_3418_; lean_object* v___x_3419_; 
v___x_3418_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3410_, v_sources_3413_, v_u_3393_);
lean_dec_ref(v_sources_3413_);
v___x_3419_ = l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__1(v_k_3395_, v_v_3394_, v_u_3393_, v___x_3418_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_, v_a_3405_, v_a_3406_);
lean_dec(v_u_3393_);
return v___x_3419_;
}
}
else
{
lean_object* v_a_3420_; lean_object* v___x_3422_; uint8_t v_isShared_3423_; uint8_t v_isSharedCheck_3427_; 
lean_dec_ref(v_k_3395_);
lean_dec(v_v_3394_);
lean_dec(v_u_3393_);
v_a_3420_ = lean_ctor_get(v___x_3411_, 0);
v_isSharedCheck_3427_ = !lean_is_exclusive(v___x_3411_);
if (v_isSharedCheck_3427_ == 0)
{
v___x_3422_ = v___x_3411_;
v_isShared_3423_ = v_isSharedCheck_3427_;
goto v_resetjp_3421_;
}
else
{
lean_inc(v_a_3420_);
lean_dec(v___x_3411_);
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
}
else
{
lean_dec_ref(v_k_3395_);
lean_dec(v_v_3394_);
lean_dec(v_u_3393_);
return v___y_3409_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_3393_ = stack[0].m_obj;
lean_object* v_v_3394_ = stack[1].m_obj;
lean_object* v_k_3395_ = stack[2].m_obj;
lean_object* v_a_3396_ = stack[3].m_obj;
lean_object* v_a_3397_ = stack[4].m_obj;
lean_object* v_a_3398_ = stack[5].m_obj;
lean_object* v_a_3399_ = stack[6].m_obj;
lean_object* v_a_3400_ = stack[7].m_obj;
lean_object* v_a_3401_ = stack[8].m_obj;
lean_object* v_a_3402_ = stack[9].m_obj;
lean_object* v_a_3403_ = stack[10].m_obj;
lean_object* v_a_3404_ = stack[11].m_obj;
lean_object* v_a_3405_ = stack[12].m_obj;
lean_object* v_a_3406_ = stack[13].m_obj;
lean_object* v_res_3446_;
v_res_3446_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update(v_u_3393_, v_v_3394_, v_k_3395_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_, v_a_3405_, v_a_3406_);
stack->m_obj
 = v_res_3446_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update___boxed(lean_object* v_u_3447_, lean_object* v_v_3448_, lean_object* v_k_3449_, lean_object* v_a_3450_, lean_object* v_a_3451_, lean_object* v_a_3452_, lean_object* v_a_3453_, lean_object* v_a_3454_, lean_object* v_a_3455_, lean_object* v_a_3456_, lean_object* v_a_3457_, lean_object* v_a_3458_, lean_object* v_a_3459_, lean_object* v_a_3460_, lean_object* v_a_3461_){
_start:
{
lean_object* v_res_3462_; 
v_res_3462_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update(v_u_3447_, v_v_3448_, v_k_3449_, v_a_3450_, v_a_3451_, v_a_3452_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_);
lean_dec(v_a_3460_);
lean_dec_ref(v_a_3459_);
lean_dec(v_a_3458_);
lean_dec_ref(v_a_3457_);
lean_dec(v_a_3456_);
lean_dec_ref(v_a_3455_);
lean_dec(v_a_3454_);
lean_dec_ref(v_a_3453_);
lean_dec(v_a_3452_);
lean_dec(v_a_3451_);
lean_dec(v_a_3450_);
return v_res_3462_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_addEdge___closed__2(void){
_start:
{
lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; 
v___x_3469_ = ((lean_object*)(l_Lean_Meta_Grind_Order_addEdge___closed__1));
v___x_3470_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__6));
v___x_3471_ = l_Lean_Name_append(v___x_3470_, v___x_3469_);
return v___x_3471_;
}
}
lean_object* l_Lean_Meta_Grind_Order_addEdge(lean_object* v_u_3472_, lean_object* v_v_3473_, lean_object* v_k_3474_, lean_object* v_h_3475_, lean_object* v_a_3476_, lean_object* v_a_3477_, lean_object* v_a_3478_, lean_object* v_a_3479_, lean_object* v_a_3480_, lean_object* v_a_3481_, lean_object* v_a_3482_, lean_object* v_a_3483_, lean_object* v_a_3484_, lean_object* v_a_3485_, lean_object* v_a_3486_){
_start:
{
lean_object* v___y_3489_; lean_object* v___y_3490_; lean_object* v___y_3491_; lean_object* v___y_3492_; lean_object* v___y_3493_; lean_object* v___y_3494_; lean_object* v___y_3495_; lean_object* v___y_3496_; lean_object* v___y_3497_; lean_object* v___y_3498_; lean_object* v___y_3499_; lean_object* v___y_3526_; lean_object* v___y_3527_; lean_object* v___y_3528_; lean_object* v___y_3529_; lean_object* v___y_3530_; lean_object* v___y_3531_; lean_object* v___y_3532_; lean_object* v___y_3533_; lean_object* v___y_3534_; lean_object* v___y_3535_; lean_object* v___y_3536_; lean_object* v___x_3563_; 
v___x_3563_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_3477_);
if (lean_obj_tag(v___x_3563_) == 0)
{
lean_object* v_a_3564_; lean_object* v___x_3566_; uint8_t v_isShared_3567_; uint8_t v_isSharedCheck_3641_; 
v_a_3564_ = lean_ctor_get(v___x_3563_, 0);
v_isSharedCheck_3641_ = !lean_is_exclusive(v___x_3563_);
if (v_isSharedCheck_3641_ == 0)
{
v___x_3566_ = v___x_3563_;
v_isShared_3567_ = v_isSharedCheck_3641_;
goto v_resetjp_3565_;
}
else
{
lean_inc(v_a_3564_);
lean_dec(v___x_3563_);
v___x_3566_ = lean_box(0);
v_isShared_3567_ = v_isSharedCheck_3641_;
goto v_resetjp_3565_;
}
v_resetjp_3565_:
{
uint8_t v___x_3568_; 
v___x_3568_ = lean_unbox(v_a_3564_);
lean_dec(v_a_3564_);
if (v___x_3568_ == 0)
{
uint8_t v___x_3569_; 
lean_del_object(v___x_3566_);
v___x_3569_ = lean_nat_dec_eq(v_u_3472_, v_v_3473_);
if (v___x_3569_ == 0)
{
lean_object* v_toCold_3570_; lean_object* v_options_3571_; uint8_t v_hasTrace_3572_; 
v_toCold_3570_ = lean_ctor_get(v_a_3485_, 0);
v_options_3571_ = lean_ctor_get(v_toCold_3570_, 2);
v_hasTrace_3572_ = lean_ctor_get_uint8(v_options_3571_, sizeof(void*)*1);
if (v_hasTrace_3572_ == 0)
{
v___y_3526_ = v_a_3476_;
v___y_3527_ = v_a_3477_;
v___y_3528_ = v_a_3478_;
v___y_3529_ = v_a_3479_;
v___y_3530_ = v_a_3480_;
v___y_3531_ = v_a_3481_;
v___y_3532_ = v_a_3482_;
v___y_3533_ = v_a_3483_;
v___y_3534_ = v_a_3484_;
v___y_3535_ = v_a_3485_;
v___y_3536_ = v_a_3486_;
goto v___jp_3525_;
}
else
{
lean_object* v_inheritedTraceOptions_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; uint8_t v___x_3576_; 
v_inheritedTraceOptions_3573_ = lean_ctor_get(v_toCold_3570_, 11);
v___x_3574_ = ((lean_object*)(l_Lean_Meta_Grind_Order_addEdge___closed__1));
v___x_3575_ = lean_obj_once(&l_Lean_Meta_Grind_Order_addEdge___closed__2, &l_Lean_Meta_Grind_Order_addEdge___closed__2_once, _init_l_Lean_Meta_Grind_Order_addEdge___closed__2);
v___x_3576_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3573_, v_options_3571_, v___x_3575_);
if (v___x_3576_ == 0)
{
v___y_3526_ = v_a_3476_;
v___y_3527_ = v_a_3477_;
v___y_3528_ = v_a_3478_;
v___y_3529_ = v_a_3479_;
v___y_3530_ = v_a_3480_;
v___y_3531_ = v_a_3481_;
v___y_3532_ = v_a_3482_;
v___y_3533_ = v_a_3483_;
v___y_3534_ = v_a_3484_;
v___y_3535_ = v_a_3485_;
v___y_3536_ = v_a_3486_;
goto v___jp_3525_;
}
else
{
lean_object* v___x_3577_; 
v___x_3577_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_u_3472_, v_a_3476_, v_a_3477_, v_a_3485_);
if (lean_obj_tag(v___x_3577_) == 0)
{
lean_object* v_a_3578_; lean_object* v___x_3579_; 
v_a_3578_ = lean_ctor_get(v___x_3577_, 0);
lean_inc(v_a_3578_);
lean_dec_ref_known(v___x_3577_, 1);
v___x_3579_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_v_3473_, v_a_3476_, v_a_3477_, v_a_3485_);
if (lean_obj_tag(v___x_3579_) == 0)
{
lean_object* v_a_3580_; lean_object* v_k_3581_; uint8_t v_strict_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___y_3590_; 
v_a_3580_ = lean_ctor_get(v___x_3579_, 0);
lean_inc(v_a_3580_);
lean_dec_ref_known(v___x_3579_, 1);
v_k_3581_ = lean_ctor_get(v_k_3474_, 0);
v_strict_3582_ = lean_ctor_get_uint8(v_k_3474_, sizeof(void*)*1);
v___x_3583_ = l_Lean_MessageData_ofExpr(v_a_3578_);
v___x_3584_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4);
v___x_3585_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3585_, 0, v___x_3583_);
lean_ctor_set(v___x_3585_, 1, v___x_3584_);
v___x_3586_ = l_Lean_MessageData_ofExpr(v_a_3580_);
v___x_3587_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3587_, 0, v___x_3585_);
lean_ctor_set(v___x_3587_, 1, v___x_3586_);
v___x_3588_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3588_, 0, v___x_3587_);
lean_ctor_set(v___x_3588_, 1, v___x_3584_);
if (v_strict_3582_ == 0)
{
lean_object* v___x_3595_; 
v___x_3595_ = l_Int_repr(v_k_3581_);
v___y_3590_ = v___x_3595_;
goto v___jp_3589_;
}
else
{
lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; 
v___x_3596_ = l_Int_repr(v_k_3581_);
v___x_3597_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5));
v___x_3598_ = lean_string_append(v___x_3596_, v___x_3597_);
v___y_3590_ = v___x_3598_;
goto v___jp_3589_;
}
v___jp_3589_:
{
lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; 
v___x_3591_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3591_, 0, v___y_3590_);
v___x_3592_ = l_Lean_MessageData_ofFormat(v___x_3591_);
v___x_3593_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3593_, 0, v___x_3588_);
lean_ctor_set(v___x_3593_, 1, v___x_3592_);
v___x_3594_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(v___x_3574_, v___x_3593_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_);
if (lean_obj_tag(v___x_3594_) == 0)
{
lean_dec_ref_known(v___x_3594_, 1);
v___y_3526_ = v_a_3476_;
v___y_3527_ = v_a_3477_;
v___y_3528_ = v_a_3478_;
v___y_3529_ = v_a_3479_;
v___y_3530_ = v_a_3480_;
v___y_3531_ = v_a_3481_;
v___y_3532_ = v_a_3482_;
v___y_3533_ = v_a_3483_;
v___y_3534_ = v_a_3484_;
v___y_3535_ = v_a_3485_;
v___y_3536_ = v_a_3486_;
goto v___jp_3525_;
}
else
{
lean_dec_ref(v_h_3475_);
lean_dec_ref(v_k_3474_);
lean_dec(v_v_3473_);
lean_dec(v_u_3472_);
return v___x_3594_;
}
}
}
else
{
lean_object* v_a_3599_; lean_object* v___x_3601_; uint8_t v_isShared_3602_; uint8_t v_isSharedCheck_3606_; 
lean_dec(v_a_3578_);
lean_dec_ref(v_h_3475_);
lean_dec_ref(v_k_3474_);
lean_dec(v_v_3473_);
lean_dec(v_u_3472_);
v_a_3599_ = lean_ctor_get(v___x_3579_, 0);
v_isSharedCheck_3606_ = !lean_is_exclusive(v___x_3579_);
if (v_isSharedCheck_3606_ == 0)
{
v___x_3601_ = v___x_3579_;
v_isShared_3602_ = v_isSharedCheck_3606_;
goto v_resetjp_3600_;
}
else
{
lean_inc(v_a_3599_);
lean_dec(v___x_3579_);
v___x_3601_ = lean_box(0);
v_isShared_3602_ = v_isSharedCheck_3606_;
goto v_resetjp_3600_;
}
v_resetjp_3600_:
{
lean_object* v___x_3604_; 
if (v_isShared_3602_ == 0)
{
v___x_3604_ = v___x_3601_;
goto v_reusejp_3603_;
}
else
{
lean_object* v_reuseFailAlloc_3605_; 
v_reuseFailAlloc_3605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3605_, 0, v_a_3599_);
v___x_3604_ = v_reuseFailAlloc_3605_;
goto v_reusejp_3603_;
}
v_reusejp_3603_:
{
return v___x_3604_;
}
}
}
}
else
{
lean_object* v_a_3607_; lean_object* v___x_3609_; uint8_t v_isShared_3610_; uint8_t v_isSharedCheck_3614_; 
lean_dec_ref(v_h_3475_);
lean_dec_ref(v_k_3474_);
lean_dec(v_v_3473_);
lean_dec(v_u_3472_);
v_a_3607_ = lean_ctor_get(v___x_3577_, 0);
v_isSharedCheck_3614_ = !lean_is_exclusive(v___x_3577_);
if (v_isSharedCheck_3614_ == 0)
{
v___x_3609_ = v___x_3577_;
v_isShared_3610_ = v_isSharedCheck_3614_;
goto v_resetjp_3608_;
}
else
{
lean_inc(v_a_3607_);
lean_dec(v___x_3577_);
v___x_3609_ = lean_box(0);
v_isShared_3610_ = v_isSharedCheck_3614_;
goto v_resetjp_3608_;
}
v_resetjp_3608_:
{
lean_object* v___x_3612_; 
if (v_isShared_3610_ == 0)
{
v___x_3612_ = v___x_3609_;
goto v_reusejp_3611_;
}
else
{
lean_object* v_reuseFailAlloc_3613_; 
v_reuseFailAlloc_3613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3613_, 0, v_a_3607_);
v___x_3612_ = v_reuseFailAlloc_3613_;
goto v_reusejp_3611_;
}
v_reusejp_3611_:
{
return v___x_3612_;
}
}
}
}
}
}
else
{
uint8_t v___x_3615_; 
lean_dec(v_v_3473_);
v___x_3615_ = l_Lean_Meta_Grind_Order_Weight_isNeg(v_k_3474_);
if (v___x_3615_ == 0)
{
lean_dec_ref(v_h_3475_);
lean_dec_ref(v_k_3474_);
lean_dec(v_u_3472_);
goto v___jp_3560_;
}
else
{
lean_object* v___x_3616_; 
v___x_3616_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_u_3472_, v_a_3476_, v_a_3477_, v_a_3485_);
lean_dec(v_u_3472_);
if (lean_obj_tag(v___x_3616_) == 0)
{
lean_object* v_a_3617_; lean_object* v___x_3618_; 
v_a_3617_ = lean_ctor_get(v___x_3616_, 0);
lean_inc(v_a_3617_);
lean_dec_ref_known(v___x_3616_, 1);
v___x_3618_ = l_Lean_Meta_Grind_Order_mkSelfUnsatProof(v_a_3617_, v_k_3474_, v_h_3475_, v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_);
lean_dec_ref(v_k_3474_);
if (lean_obj_tag(v___x_3618_) == 0)
{
lean_object* v_a_3619_; lean_object* v___x_3620_; 
v_a_3619_ = lean_ctor_get(v___x_3618_, 0);
lean_inc(v_a_3619_);
lean_dec_ref_known(v___x_3618_, 1);
v___x_3620_ = l_Lean_Meta_Grind_closeGoal(v_a_3619_, v_a_3477_, v_a_3478_, v_a_3479_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_);
if (lean_obj_tag(v___x_3620_) == 0)
{
lean_dec_ref_known(v___x_3620_, 1);
goto v___jp_3560_;
}
else
{
return v___x_3620_;
}
}
else
{
lean_object* v_a_3621_; lean_object* v___x_3623_; uint8_t v_isShared_3624_; uint8_t v_isSharedCheck_3628_; 
v_a_3621_ = lean_ctor_get(v___x_3618_, 0);
v_isSharedCheck_3628_ = !lean_is_exclusive(v___x_3618_);
if (v_isSharedCheck_3628_ == 0)
{
v___x_3623_ = v___x_3618_;
v_isShared_3624_ = v_isSharedCheck_3628_;
goto v_resetjp_3622_;
}
else
{
lean_inc(v_a_3621_);
lean_dec(v___x_3618_);
v___x_3623_ = lean_box(0);
v_isShared_3624_ = v_isSharedCheck_3628_;
goto v_resetjp_3622_;
}
v_resetjp_3622_:
{
lean_object* v___x_3626_; 
if (v_isShared_3624_ == 0)
{
v___x_3626_ = v___x_3623_;
goto v_reusejp_3625_;
}
else
{
lean_object* v_reuseFailAlloc_3627_; 
v_reuseFailAlloc_3627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3627_, 0, v_a_3621_);
v___x_3626_ = v_reuseFailAlloc_3627_;
goto v_reusejp_3625_;
}
v_reusejp_3625_:
{
return v___x_3626_;
}
}
}
}
else
{
lean_object* v_a_3629_; lean_object* v___x_3631_; uint8_t v_isShared_3632_; uint8_t v_isSharedCheck_3636_; 
lean_dec_ref(v_h_3475_);
lean_dec_ref(v_k_3474_);
v_a_3629_ = lean_ctor_get(v___x_3616_, 0);
v_isSharedCheck_3636_ = !lean_is_exclusive(v___x_3616_);
if (v_isSharedCheck_3636_ == 0)
{
v___x_3631_ = v___x_3616_;
v_isShared_3632_ = v_isSharedCheck_3636_;
goto v_resetjp_3630_;
}
else
{
lean_inc(v_a_3629_);
lean_dec(v___x_3616_);
v___x_3631_ = lean_box(0);
v_isShared_3632_ = v_isSharedCheck_3636_;
goto v_resetjp_3630_;
}
v_resetjp_3630_:
{
lean_object* v___x_3634_; 
if (v_isShared_3632_ == 0)
{
v___x_3634_ = v___x_3631_;
goto v_reusejp_3633_;
}
else
{
lean_object* v_reuseFailAlloc_3635_; 
v_reuseFailAlloc_3635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3635_, 0, v_a_3629_);
v___x_3634_ = v_reuseFailAlloc_3635_;
goto v_reusejp_3633_;
}
v_reusejp_3633_:
{
return v___x_3634_;
}
}
}
}
}
}
else
{
lean_object* v___x_3637_; lean_object* v___x_3639_; 
lean_dec_ref(v_h_3475_);
lean_dec_ref(v_k_3474_);
lean_dec(v_v_3473_);
lean_dec(v_u_3472_);
v___x_3637_ = lean_box(0);
if (v_isShared_3567_ == 0)
{
lean_ctor_set(v___x_3566_, 0, v___x_3637_);
v___x_3639_ = v___x_3566_;
goto v_reusejp_3638_;
}
else
{
lean_object* v_reuseFailAlloc_3640_; 
v_reuseFailAlloc_3640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3640_, 0, v___x_3637_);
v___x_3639_ = v_reuseFailAlloc_3640_;
goto v_reusejp_3638_;
}
v_reusejp_3638_:
{
return v___x_3639_;
}
}
}
}
else
{
lean_object* v_a_3642_; lean_object* v___x_3644_; uint8_t v_isShared_3645_; uint8_t v_isSharedCheck_3649_; 
lean_dec_ref(v_h_3475_);
lean_dec_ref(v_k_3474_);
lean_dec(v_v_3473_);
lean_dec(v_u_3472_);
v_a_3642_ = lean_ctor_get(v___x_3563_, 0);
v_isSharedCheck_3649_ = !lean_is_exclusive(v___x_3563_);
if (v_isSharedCheck_3649_ == 0)
{
v___x_3644_ = v___x_3563_;
v_isShared_3645_ = v_isSharedCheck_3649_;
goto v_resetjp_3643_;
}
else
{
lean_inc(v_a_3642_);
lean_dec(v___x_3563_);
v___x_3644_ = lean_box(0);
v_isShared_3645_ = v_isSharedCheck_3649_;
goto v_resetjp_3643_;
}
v_resetjp_3643_:
{
lean_object* v___x_3647_; 
if (v_isShared_3645_ == 0)
{
v___x_3647_ = v___x_3644_;
goto v_reusejp_3646_;
}
else
{
lean_object* v_reuseFailAlloc_3648_; 
v_reuseFailAlloc_3648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3648_, 0, v_a_3642_);
v___x_3647_ = v_reuseFailAlloc_3648_;
goto v_reusejp_3646_;
}
v_reusejp_3646_:
{
return v___x_3647_;
}
}
}
v___jp_3488_:
{
lean_object* v___x_3500_; 
v___x_3500_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isShorter___redArg(v_u_3472_, v_v_3473_, v_k_3474_, v___y_3489_, v___y_3490_, v___y_3498_);
if (lean_obj_tag(v___x_3500_) == 0)
{
lean_object* v_a_3501_; lean_object* v___x_3503_; uint8_t v_isShared_3504_; uint8_t v_isSharedCheck_3516_; 
v_a_3501_ = lean_ctor_get(v___x_3500_, 0);
v_isSharedCheck_3516_ = !lean_is_exclusive(v___x_3500_);
if (v_isSharedCheck_3516_ == 0)
{
v___x_3503_ = v___x_3500_;
v_isShared_3504_ = v_isSharedCheck_3516_;
goto v_resetjp_3502_;
}
else
{
lean_inc(v_a_3501_);
lean_dec(v___x_3500_);
v___x_3503_ = lean_box(0);
v_isShared_3504_ = v_isSharedCheck_3516_;
goto v_resetjp_3502_;
}
v_resetjp_3502_:
{
uint8_t v___x_3505_; 
v___x_3505_ = lean_unbox(v_a_3501_);
lean_dec(v_a_3501_);
if (v___x_3505_ == 0)
{
lean_object* v___x_3506_; lean_object* v___x_3508_; 
lean_dec_ref(v_h_3475_);
lean_dec_ref(v_k_3474_);
lean_dec(v_v_3473_);
lean_dec(v_u_3472_);
v___x_3506_ = lean_box(0);
if (v_isShared_3504_ == 0)
{
lean_ctor_set(v___x_3503_, 0, v___x_3506_);
v___x_3508_ = v___x_3503_;
goto v_reusejp_3507_;
}
else
{
lean_object* v_reuseFailAlloc_3509_; 
v_reuseFailAlloc_3509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3509_, 0, v___x_3506_);
v___x_3508_ = v_reuseFailAlloc_3509_;
goto v_reusejp_3507_;
}
v_reusejp_3507_:
{
return v___x_3508_;
}
}
else
{
lean_object* v___x_3510_; 
lean_del_object(v___x_3503_);
lean_inc_ref(v_k_3474_);
lean_inc(v_v_3473_);
lean_inc(v_u_3472_);
v___x_3510_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist___redArg(v_u_3472_, v_v_3473_, v_k_3474_, v___y_3489_, v___y_3490_);
if (lean_obj_tag(v___x_3510_) == 0)
{
lean_object* v___x_3511_; lean_object* v___x_3512_; 
lean_dec_ref_known(v___x_3510_, 1);
lean_inc_ref(v_k_3474_);
lean_inc_n(v_u_3472_, 2);
v___x_3511_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3511_, 0, v_u_3472_);
lean_ctor_set(v___x_3511_, 1, v_k_3474_);
lean_ctor_set(v___x_3511_, 2, v_h_3475_);
lean_inc(v_v_3473_);
v___x_3512_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___redArg(v_u_3472_, v_v_3473_, v___x_3511_, v___y_3489_, v___y_3490_);
if (lean_obj_tag(v___x_3512_) == 0)
{
lean_object* v___x_3513_; 
lean_dec_ref_known(v___x_3512_, 1);
lean_inc_ref(v_k_3474_);
lean_inc(v_v_3473_);
lean_inc(v_u_3472_);
v___x_3513_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate(v_u_3472_, v_v_3473_, v_k_3474_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_, v___y_3499_);
if (lean_obj_tag(v___x_3513_) == 0)
{
lean_object* v___x_3514_; 
lean_dec_ref_known(v___x_3513_, 1);
v___x_3514_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update(v_u_3472_, v_v_3473_, v_k_3474_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_, v___y_3499_);
if (lean_obj_tag(v___x_3514_) == 0)
{
lean_object* v___x_3515_; 
lean_dec_ref_known(v___x_3514_, 1);
v___x_3515_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending(v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_, v___y_3499_);
return v___x_3515_;
}
else
{
return v___x_3514_;
}
}
else
{
lean_dec_ref(v_k_3474_);
lean_dec(v_v_3473_);
lean_dec(v_u_3472_);
return v___x_3513_;
}
}
else
{
lean_dec_ref(v_k_3474_);
lean_dec(v_v_3473_);
lean_dec(v_u_3472_);
return v___x_3512_;
}
}
else
{
lean_dec_ref(v_h_3475_);
lean_dec_ref(v_k_3474_);
lean_dec(v_v_3473_);
lean_dec(v_u_3472_);
return v___x_3510_;
}
}
}
}
else
{
lean_object* v_a_3517_; lean_object* v___x_3519_; uint8_t v_isShared_3520_; uint8_t v_isSharedCheck_3524_; 
lean_dec_ref(v_h_3475_);
lean_dec_ref(v_k_3474_);
lean_dec(v_v_3473_);
lean_dec(v_u_3472_);
v_a_3517_ = lean_ctor_get(v___x_3500_, 0);
v_isSharedCheck_3524_ = !lean_is_exclusive(v___x_3500_);
if (v_isSharedCheck_3524_ == 0)
{
v___x_3519_ = v___x_3500_;
v_isShared_3520_ = v_isSharedCheck_3524_;
goto v_resetjp_3518_;
}
else
{
lean_inc(v_a_3517_);
lean_dec(v___x_3500_);
v___x_3519_ = lean_box(0);
v_isShared_3520_ = v_isSharedCheck_3524_;
goto v_resetjp_3518_;
}
v_resetjp_3518_:
{
lean_object* v___x_3522_; 
if (v_isShared_3520_ == 0)
{
v___x_3522_ = v___x_3519_;
goto v_reusejp_3521_;
}
else
{
lean_object* v_reuseFailAlloc_3523_; 
v_reuseFailAlloc_3523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3523_, 0, v_a_3517_);
v___x_3522_ = v_reuseFailAlloc_3523_;
goto v_reusejp_3521_;
}
v_reusejp_3521_:
{
return v___x_3522_;
}
}
}
}
v___jp_3525_:
{
lean_object* v___x_3537_; 
v___x_3537_ = l_Lean_Meta_Grind_Order_getDist_x3f___redArg(v_v_3473_, v_u_3472_, v___y_3526_, v___y_3527_, v___y_3535_);
if (lean_obj_tag(v___x_3537_) == 0)
{
lean_object* v_a_3538_; 
v_a_3538_ = lean_ctor_get(v___x_3537_, 0);
lean_inc(v_a_3538_);
lean_dec_ref_known(v___x_3537_, 1);
if (lean_obj_tag(v_a_3538_) == 1)
{
lean_object* v_val_3539_; lean_object* v___x_3540_; uint8_t v___x_3541_; 
v_val_3539_ = lean_ctor_get(v_a_3538_, 0);
lean_inc_n(v_val_3539_, 2);
lean_dec_ref_known(v_a_3538_, 1);
v___x_3540_ = l_Lean_Meta_Grind_Order_Weight_add(v_k_3474_, v_val_3539_);
v___x_3541_ = l_Lean_Meta_Grind_Order_Weight_isNeg(v___x_3540_);
lean_dec_ref(v___x_3540_);
if (v___x_3541_ == 0)
{
lean_dec(v_val_3539_);
v___y_3489_ = v___y_3526_;
v___y_3490_ = v___y_3527_;
v___y_3491_ = v___y_3528_;
v___y_3492_ = v___y_3529_;
v___y_3493_ = v___y_3530_;
v___y_3494_ = v___y_3531_;
v___y_3495_ = v___y_3532_;
v___y_3496_ = v___y_3533_;
v___y_3497_ = v___y_3534_;
v___y_3498_ = v___y_3535_;
v___y_3499_ = v___y_3536_;
goto v___jp_3488_;
}
else
{
lean_object* v___x_3542_; 
v___x_3542_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setUnsat(v_u_3472_, v_v_3473_, v_k_3474_, v_h_3475_, v_val_3539_, v___y_3526_, v___y_3527_, v___y_3528_, v___y_3529_, v___y_3530_, v___y_3531_, v___y_3532_, v___y_3533_, v___y_3534_, v___y_3535_, v___y_3536_);
lean_dec(v_val_3539_);
lean_dec_ref(v_k_3474_);
lean_dec(v_v_3473_);
lean_dec(v_u_3472_);
if (lean_obj_tag(v___x_3542_) == 0)
{
lean_object* v___x_3544_; uint8_t v_isShared_3545_; uint8_t v_isSharedCheck_3550_; 
v_isSharedCheck_3550_ = !lean_is_exclusive(v___x_3542_);
if (v_isSharedCheck_3550_ == 0)
{
lean_object* v_unused_3551_; 
v_unused_3551_ = lean_ctor_get(v___x_3542_, 0);
lean_dec(v_unused_3551_);
v___x_3544_ = v___x_3542_;
v_isShared_3545_ = v_isSharedCheck_3550_;
goto v_resetjp_3543_;
}
else
{
lean_dec(v___x_3542_);
v___x_3544_ = lean_box(0);
v_isShared_3545_ = v_isSharedCheck_3550_;
goto v_resetjp_3543_;
}
v_resetjp_3543_:
{
lean_object* v___x_3546_; lean_object* v___x_3548_; 
v___x_3546_ = lean_box(0);
if (v_isShared_3545_ == 0)
{
lean_ctor_set(v___x_3544_, 0, v___x_3546_);
v___x_3548_ = v___x_3544_;
goto v_reusejp_3547_;
}
else
{
lean_object* v_reuseFailAlloc_3549_; 
v_reuseFailAlloc_3549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3549_, 0, v___x_3546_);
v___x_3548_ = v_reuseFailAlloc_3549_;
goto v_reusejp_3547_;
}
v_reusejp_3547_:
{
return v___x_3548_;
}
}
}
else
{
return v___x_3542_;
}
}
}
else
{
lean_dec(v_a_3538_);
v___y_3489_ = v___y_3526_;
v___y_3490_ = v___y_3527_;
v___y_3491_ = v___y_3528_;
v___y_3492_ = v___y_3529_;
v___y_3493_ = v___y_3530_;
v___y_3494_ = v___y_3531_;
v___y_3495_ = v___y_3532_;
v___y_3496_ = v___y_3533_;
v___y_3497_ = v___y_3534_;
v___y_3498_ = v___y_3535_;
v___y_3499_ = v___y_3536_;
goto v___jp_3488_;
}
}
else
{
lean_object* v_a_3552_; lean_object* v___x_3554_; uint8_t v_isShared_3555_; uint8_t v_isSharedCheck_3559_; 
lean_dec_ref(v_h_3475_);
lean_dec_ref(v_k_3474_);
lean_dec(v_v_3473_);
lean_dec(v_u_3472_);
v_a_3552_ = lean_ctor_get(v___x_3537_, 0);
v_isSharedCheck_3559_ = !lean_is_exclusive(v___x_3537_);
if (v_isSharedCheck_3559_ == 0)
{
v___x_3554_ = v___x_3537_;
v_isShared_3555_ = v_isSharedCheck_3559_;
goto v_resetjp_3553_;
}
else
{
lean_inc(v_a_3552_);
lean_dec(v___x_3537_);
v___x_3554_ = lean_box(0);
v_isShared_3555_ = v_isSharedCheck_3559_;
goto v_resetjp_3553_;
}
v_resetjp_3553_:
{
lean_object* v___x_3557_; 
if (v_isShared_3555_ == 0)
{
v___x_3557_ = v___x_3554_;
goto v_reusejp_3556_;
}
else
{
lean_object* v_reuseFailAlloc_3558_; 
v_reuseFailAlloc_3558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3558_, 0, v_a_3552_);
v___x_3557_ = v_reuseFailAlloc_3558_;
goto v_reusejp_3556_;
}
v_reusejp_3556_:
{
return v___x_3557_;
}
}
}
}
v___jp_3560_:
{
lean_object* v___x_3561_; lean_object* v___x_3562_; 
v___x_3561_ = lean_box(0);
v___x_3562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3562_, 0, v___x_3561_);
return v___x_3562_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Order_addEdge_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_3472_ = stack[0].m_obj;
lean_object* v_v_3473_ = stack[1].m_obj;
lean_object* v_k_3474_ = stack[2].m_obj;
lean_object* v_h_3475_ = stack[3].m_obj;
lean_object* v_a_3476_ = stack[4].m_obj;
lean_object* v_a_3477_ = stack[5].m_obj;
lean_object* v_a_3478_ = stack[6].m_obj;
lean_object* v_a_3479_ = stack[7].m_obj;
lean_object* v_a_3480_ = stack[8].m_obj;
lean_object* v_a_3481_ = stack[9].m_obj;
lean_object* v_a_3482_ = stack[10].m_obj;
lean_object* v_a_3483_ = stack[11].m_obj;
lean_object* v_a_3484_ = stack[12].m_obj;
lean_object* v_a_3485_ = stack[13].m_obj;
lean_object* v_a_3486_ = stack[14].m_obj;
lean_object* v_res_3650_;
v_res_3650_ = l_Lean_Meta_Grind_Order_addEdge(v_u_3472_, v_v_3473_, v_k_3474_, v_h_3475_, v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_);
stack->m_obj
 = v_res_3650_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_addEdge___boxed(lean_object* v_u_3651_, lean_object* v_v_3652_, lean_object* v_k_3653_, lean_object* v_h_3654_, lean_object* v_a_3655_, lean_object* v_a_3656_, lean_object* v_a_3657_, lean_object* v_a_3658_, lean_object* v_a_3659_, lean_object* v_a_3660_, lean_object* v_a_3661_, lean_object* v_a_3662_, lean_object* v_a_3663_, lean_object* v_a_3664_, lean_object* v_a_3665_, lean_object* v_a_3666_){
_start:
{
lean_object* v_res_3667_; 
v_res_3667_ = l_Lean_Meta_Grind_Order_addEdge(v_u_3651_, v_v_3652_, v_k_3653_, v_h_3654_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_, v_a_3662_, v_a_3663_, v_a_3664_, v_a_3665_);
lean_dec(v_a_3665_);
lean_dec_ref(v_a_3664_);
lean_dec(v_a_3663_);
lean_dec_ref(v_a_3662_);
lean_dec(v_a_3661_);
lean_dec_ref(v_a_3660_);
lean_dec(v_a_3659_);
lean_dec_ref(v_a_3658_);
lean_dec(v_a_3657_);
lean_dec(v_a_3656_);
lean_dec(v_a_3655_);
return v_res_3667_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__2(void){
_start:
{
lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; 
v___x_3674_ = lean_box(0);
v___x_3675_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__1));
v___x_3676_ = l_Lean_mkConst(v___x_3675_, v___x_3674_);
return v___x_3676_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5(void){
_start:
{
lean_object* v_cls_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; 
v_cls_3682_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__4));
v___x_3683_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__6));
v___x_3684_ = l_Lean_Name_append(v___x_3683_, v_cls_3682_);
return v___x_3684_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue(lean_object* v_c_3685_, lean_object* v_e_3686_, lean_object* v_he_3687_, lean_object* v_a_3688_, lean_object* v_a_3689_, lean_object* v_a_3690_, lean_object* v_a_3691_, lean_object* v_a_3692_, lean_object* v_a_3693_, lean_object* v_a_3694_, lean_object* v_a_3695_, lean_object* v_a_3696_, lean_object* v_a_3697_, lean_object* v_a_3698_){
_start:
{
lean_object* v___y_3701_; lean_object* v___y_3702_; lean_object* v___y_3703_; lean_object* v___y_3704_; lean_object* v___y_3705_; lean_object* v___y_3706_; lean_object* v___y_3707_; lean_object* v___y_3708_; lean_object* v___y_3709_; lean_object* v___y_3710_; lean_object* v___y_3711_; lean_object* v___y_3712_; lean_object* v___y_3713_; lean_object* v___y_3714_; lean_object* v___y_3715_; uint8_t v___y_3716_; lean_object* v_h_3720_; lean_object* v___y_3721_; lean_object* v___y_3722_; lean_object* v___y_3723_; lean_object* v___y_3724_; lean_object* v___y_3725_; lean_object* v___y_3726_; lean_object* v___y_3727_; lean_object* v___y_3728_; lean_object* v___y_3729_; lean_object* v___y_3730_; lean_object* v___y_3731_; lean_object* v___y_3742_; lean_object* v___y_3743_; lean_object* v___y_3744_; lean_object* v___y_3745_; lean_object* v___y_3746_; lean_object* v___y_3747_; lean_object* v___y_3748_; lean_object* v___y_3749_; lean_object* v___y_3750_; lean_object* v___y_3751_; lean_object* v___y_3752_; lean_object* v_toCold_3760_; lean_object* v_options_3761_; uint8_t v_hasTrace_3762_; 
v_toCold_3760_ = lean_ctor_get(v_a_3697_, 0);
v_options_3761_ = lean_ctor_get(v_toCold_3760_, 2);
v_hasTrace_3762_ = lean_ctor_get_uint8(v_options_3761_, sizeof(void*)*1);
if (v_hasTrace_3762_ == 0)
{
v___y_3742_ = v_a_3688_;
v___y_3743_ = v_a_3689_;
v___y_3744_ = v_a_3690_;
v___y_3745_ = v_a_3691_;
v___y_3746_ = v_a_3692_;
v___y_3747_ = v_a_3693_;
v___y_3748_ = v_a_3694_;
v___y_3749_ = v_a_3695_;
v___y_3750_ = v_a_3696_;
v___y_3751_ = v_a_3697_;
v___y_3752_ = v_a_3698_;
goto v___jp_3741_;
}
else
{
lean_object* v_inheritedTraceOptions_3763_; lean_object* v_cls_3764_; lean_object* v___x_3765_; uint8_t v___x_3766_; 
v_inheritedTraceOptions_3763_ = lean_ctor_get(v_toCold_3760_, 11);
v_cls_3764_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__4));
v___x_3765_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5);
v___x_3766_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3763_, v_options_3761_, v___x_3765_);
if (v___x_3766_ == 0)
{
v___y_3742_ = v_a_3688_;
v___y_3743_ = v_a_3689_;
v___y_3744_ = v_a_3690_;
v___y_3745_ = v_a_3691_;
v___y_3746_ = v_a_3692_;
v___y_3747_ = v_a_3693_;
v___y_3748_ = v_a_3694_;
v___y_3749_ = v_a_3695_;
v___y_3750_ = v_a_3696_;
v___y_3751_ = v_a_3697_;
v___y_3752_ = v_a_3698_;
goto v___jp_3741_;
}
else
{
lean_object* v___x_3767_; 
v___x_3767_ = l_Lean_Meta_Grind_Order_Cnstr_pp___redArg(v_c_3685_, v_a_3688_, v_a_3689_, v_a_3697_);
if (lean_obj_tag(v___x_3767_) == 0)
{
lean_object* v_a_3768_; lean_object* v___x_3769_; 
v_a_3768_ = lean_ctor_get(v___x_3767_, 0);
lean_inc(v_a_3768_);
lean_dec_ref_known(v___x_3767_, 1);
v___x_3769_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(v_cls_3764_, v_a_3768_, v_a_3695_, v_a_3696_, v_a_3697_, v_a_3698_);
if (lean_obj_tag(v___x_3769_) == 0)
{
lean_dec_ref_known(v___x_3769_, 1);
v___y_3742_ = v_a_3688_;
v___y_3743_ = v_a_3689_;
v___y_3744_ = v_a_3690_;
v___y_3745_ = v_a_3691_;
v___y_3746_ = v_a_3692_;
v___y_3747_ = v_a_3693_;
v___y_3748_ = v_a_3694_;
v___y_3749_ = v_a_3695_;
v___y_3750_ = v_a_3696_;
v___y_3751_ = v_a_3697_;
v___y_3752_ = v_a_3698_;
goto v___jp_3741_;
}
else
{
lean_dec_ref(v_he_3687_);
lean_dec_ref(v_e_3686_);
lean_dec_ref(v_c_3685_);
return v___x_3769_;
}
}
else
{
lean_object* v_a_3770_; lean_object* v___x_3772_; uint8_t v_isShared_3773_; uint8_t v_isSharedCheck_3777_; 
lean_dec_ref(v_he_3687_);
lean_dec_ref(v_e_3686_);
lean_dec_ref(v_c_3685_);
v_a_3770_ = lean_ctor_get(v___x_3767_, 0);
v_isSharedCheck_3777_ = !lean_is_exclusive(v___x_3767_);
if (v_isSharedCheck_3777_ == 0)
{
v___x_3772_ = v___x_3767_;
v_isShared_3773_ = v_isSharedCheck_3777_;
goto v_resetjp_3771_;
}
else
{
lean_inc(v_a_3770_);
lean_dec(v___x_3767_);
v___x_3772_ = lean_box(0);
v_isShared_3773_ = v_isSharedCheck_3777_;
goto v_resetjp_3771_;
}
v_resetjp_3771_:
{
lean_object* v___x_3775_; 
if (v_isShared_3773_ == 0)
{
v___x_3775_ = v___x_3772_;
goto v_reusejp_3774_;
}
else
{
lean_object* v_reuseFailAlloc_3776_; 
v_reuseFailAlloc_3776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3776_, 0, v_a_3770_);
v___x_3775_ = v_reuseFailAlloc_3776_;
goto v_reusejp_3774_;
}
v_reusejp_3774_:
{
return v___x_3775_;
}
}
}
}
}
v___jp_3700_:
{
lean_object* v___x_3717_; lean_object* v___x_3718_; 
v___x_3717_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3717_, 0, v___y_3703_);
lean_ctor_set_uint8(v___x_3717_, sizeof(void*)*1, v___y_3716_);
v___x_3718_ = l_Lean_Meta_Grind_Order_addEdge(v___y_3709_, v___y_3712_, v___x_3717_, v___y_3706_, v___y_3708_, v___y_3711_, v___y_3705_, v___y_3715_, v___y_3702_, v___y_3714_, v___y_3704_, v___y_3710_, v___y_3707_, v___y_3701_, v___y_3713_);
return v___x_3718_;
}
v___jp_3719_:
{
uint8_t v_kind_3732_; 
v_kind_3732_ = lean_ctor_get_uint8(v_c_3685_, sizeof(void*)*5);
if (v_kind_3732_ == 1)
{
lean_object* v_u_3733_; lean_object* v_v_3734_; lean_object* v_k_3735_; uint8_t v___x_3736_; 
v_u_3733_ = lean_ctor_get(v_c_3685_, 0);
lean_inc(v_u_3733_);
v_v_3734_ = lean_ctor_get(v_c_3685_, 1);
lean_inc(v_v_3734_);
v_k_3735_ = lean_ctor_get(v_c_3685_, 2);
lean_inc(v_k_3735_);
lean_dec_ref(v_c_3685_);
v___x_3736_ = 1;
v___y_3701_ = v___y_3730_;
v___y_3702_ = v___y_3725_;
v___y_3703_ = v_k_3735_;
v___y_3704_ = v___y_3727_;
v___y_3705_ = v___y_3723_;
v___y_3706_ = v_h_3720_;
v___y_3707_ = v___y_3729_;
v___y_3708_ = v___y_3721_;
v___y_3709_ = v_u_3733_;
v___y_3710_ = v___y_3728_;
v___y_3711_ = v___y_3722_;
v___y_3712_ = v_v_3734_;
v___y_3713_ = v___y_3731_;
v___y_3714_ = v___y_3726_;
v___y_3715_ = v___y_3724_;
v___y_3716_ = v___x_3736_;
goto v___jp_3700_;
}
else
{
lean_object* v_u_3737_; lean_object* v_v_3738_; lean_object* v_k_3739_; uint8_t v___x_3740_; 
v_u_3737_ = lean_ctor_get(v_c_3685_, 0);
lean_inc(v_u_3737_);
v_v_3738_ = lean_ctor_get(v_c_3685_, 1);
lean_inc(v_v_3738_);
v_k_3739_ = lean_ctor_get(v_c_3685_, 2);
lean_inc(v_k_3739_);
lean_dec_ref(v_c_3685_);
v___x_3740_ = 0;
v___y_3701_ = v___y_3730_;
v___y_3702_ = v___y_3725_;
v___y_3703_ = v_k_3739_;
v___y_3704_ = v___y_3727_;
v___y_3705_ = v___y_3723_;
v___y_3706_ = v_h_3720_;
v___y_3707_ = v___y_3729_;
v___y_3708_ = v___y_3721_;
v___y_3709_ = v_u_3737_;
v___y_3710_ = v___y_3728_;
v___y_3711_ = v___y_3722_;
v___y_3712_ = v_v_3738_;
v___y_3713_ = v___y_3731_;
v___y_3714_ = v___y_3726_;
v___y_3715_ = v___y_3724_;
v___y_3716_ = v___x_3740_;
goto v___jp_3700_;
}
}
v___jp_3741_:
{
lean_object* v_h_x3f_3753_; 
v_h_x3f_3753_ = lean_ctor_get(v_c_3685_, 4);
if (lean_obj_tag(v_h_x3f_3753_) == 1)
{
lean_object* v_e_3754_; lean_object* v_val_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; 
v_e_3754_ = lean_ctor_get(v_c_3685_, 3);
v_val_3755_ = lean_ctor_get(v_h_x3f_3753_, 0);
v___x_3756_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__2, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__2);
lean_inc_ref(v_e_3686_);
v___x_3757_ = l_Lean_Meta_mkOfEqTrueCore(v_e_3686_, v_he_3687_);
lean_inc(v_val_3755_);
lean_inc_ref(v_e_3754_);
v___x_3758_ = l_Lean_mkApp4(v___x_3756_, v_e_3686_, v_e_3754_, v_val_3755_, v___x_3757_);
v_h_3720_ = v___x_3758_;
v___y_3721_ = v___y_3742_;
v___y_3722_ = v___y_3743_;
v___y_3723_ = v___y_3744_;
v___y_3724_ = v___y_3745_;
v___y_3725_ = v___y_3746_;
v___y_3726_ = v___y_3747_;
v___y_3727_ = v___y_3748_;
v___y_3728_ = v___y_3749_;
v___y_3729_ = v___y_3750_;
v___y_3730_ = v___y_3751_;
v___y_3731_ = v___y_3752_;
goto v___jp_3719_;
}
else
{
lean_object* v___x_3759_; 
v___x_3759_ = l_Lean_Meta_mkOfEqTrueCore(v_e_3686_, v_he_3687_);
v_h_3720_ = v___x_3759_;
v___y_3721_ = v___y_3742_;
v___y_3722_ = v___y_3743_;
v___y_3723_ = v___y_3744_;
v___y_3724_ = v___y_3745_;
v___y_3725_ = v___y_3746_;
v___y_3726_ = v___y_3747_;
v___y_3727_ = v___y_3748_;
v___y_3728_ = v___y_3749_;
v___y_3729_ = v___y_3750_;
v___y_3730_ = v___y_3751_;
v___y_3731_ = v___y_3752_;
goto v___jp_3719_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_3685_ = stack[0].m_obj;
lean_object* v_e_3686_ = stack[1].m_obj;
lean_object* v_he_3687_ = stack[2].m_obj;
lean_object* v_a_3688_ = stack[3].m_obj;
lean_object* v_a_3689_ = stack[4].m_obj;
lean_object* v_a_3690_ = stack[5].m_obj;
lean_object* v_a_3691_ = stack[6].m_obj;
lean_object* v_a_3692_ = stack[7].m_obj;
lean_object* v_a_3693_ = stack[8].m_obj;
lean_object* v_a_3694_ = stack[9].m_obj;
lean_object* v_a_3695_ = stack[10].m_obj;
lean_object* v_a_3696_ = stack[11].m_obj;
lean_object* v_a_3697_ = stack[12].m_obj;
lean_object* v_a_3698_ = stack[13].m_obj;
lean_object* v_res_3778_;
v_res_3778_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue(v_c_3685_, v_e_3686_, v_he_3687_, v_a_3688_, v_a_3689_, v_a_3690_, v_a_3691_, v_a_3692_, v_a_3693_, v_a_3694_, v_a_3695_, v_a_3696_, v_a_3697_, v_a_3698_);
stack->m_obj
 = v_res_3778_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___boxed(lean_object* v_c_3779_, lean_object* v_e_3780_, lean_object* v_he_3781_, lean_object* v_a_3782_, lean_object* v_a_3783_, lean_object* v_a_3784_, lean_object* v_a_3785_, lean_object* v_a_3786_, lean_object* v_a_3787_, lean_object* v_a_3788_, lean_object* v_a_3789_, lean_object* v_a_3790_, lean_object* v_a_3791_, lean_object* v_a_3792_, lean_object* v_a_3793_){
_start:
{
lean_object* v_res_3794_; 
v_res_3794_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue(v_c_3779_, v_e_3780_, v_he_3781_, v_a_3782_, v_a_3783_, v_a_3784_, v_a_3785_, v_a_3786_, v_a_3787_, v_a_3788_, v_a_3789_, v_a_3790_, v_a_3791_, v_a_3792_);
lean_dec(v_a_3792_);
lean_dec_ref(v_a_3791_);
lean_dec(v_a_3790_);
lean_dec_ref(v_a_3789_);
lean_dec(v_a_3788_);
lean_dec_ref(v_a_3787_);
lean_dec(v_a_3786_);
lean_dec_ref(v_a_3785_);
lean_dec(v_a_3784_);
lean_dec(v_a_3783_);
lean_dec(v_a_3782_);
return v_res_3794_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__2(void){
_start:
{
lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; 
v___x_3801_ = lean_box(0);
v___x_3802_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__1));
v___x_3803_ = l_Lean_mkConst(v___x_3802_, v___x_3801_);
return v___x_3803_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__3(void){
_start:
{
lean_object* v___x_3804_; lean_object* v___x_3805_; 
v___x_3804_ = lean_unsigned_to_nat(1u);
v___x_3805_ = lean_nat_to_int(v___x_3804_);
return v___x_3805_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4(void){
_start:
{
lean_object* v___x_3806_; lean_object* v___x_3807_; 
v___x_3806_ = lean_unsigned_to_nat(0u);
v___x_3807_ = lean_nat_to_int(v___x_3806_);
return v___x_3807_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__8(void){
_start:
{
lean_object* v___x_3813_; lean_object* v___x_3814_; 
v___x_3813_ = lean_unsigned_to_nat(0u);
v___x_3814_ = l_Lean_Level_ofNat(v___x_3813_);
return v___x_3814_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__9(void){
_start:
{
lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; 
v___x_3815_ = lean_box(0);
v___x_3816_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__8, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__8);
v___x_3817_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3817_, 0, v___x_3816_);
lean_ctor_set(v___x_3817_, 1, v___x_3815_);
return v___x_3817_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10(void){
_start:
{
lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; 
v___x_3818_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__9, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__9);
v___x_3819_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__7));
v___x_3820_ = l_Lean_Expr_const___override(v___x_3819_, v___x_3818_);
return v___x_3820_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13(void){
_start:
{
lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; 
v___x_3824_ = lean_box(0);
v___x_3825_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__12));
v___x_3826_ = l_Lean_Expr_const___override(v___x_3825_, v___x_3824_);
return v___x_3826_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16(void){
_start:
{
lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; 
v___x_3831_ = lean_box(0);
v___x_3832_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__15));
v___x_3833_ = l_Lean_Expr_const___override(v___x_3832_, v___x_3831_);
return v___x_3833_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__29(void){
_start:
{
lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; 
v___x_3870_ = lean_box(0);
v___x_3871_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__28));
v___x_3872_ = l_Lean_mkConst(v___x_3871_, v___x_3870_);
return v___x_3872_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__31(void){
_start:
{
lean_object* v___x_3874_; lean_object* v___x_3875_; 
v___x_3874_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__30));
v___x_3875_ = l_Lean_stringToMessageData(v___x_3874_);
return v___x_3875_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse(lean_object* v_c_3876_, lean_object* v_e_3877_, lean_object* v_he_3878_, lean_object* v_a_3879_, lean_object* v_a_3880_, lean_object* v_a_3881_, lean_object* v_a_3882_, lean_object* v_a_3883_, lean_object* v_a_3884_, lean_object* v_a_3885_, lean_object* v_a_3886_, lean_object* v_a_3887_, lean_object* v_a_3888_, lean_object* v_a_3889_){
_start:
{
lean_object* v___y_3892_; lean_object* v___y_3893_; lean_object* v_k_x27_3894_; lean_object* v_h_3895_; uint8_t v_strict_3896_; lean_object* v___y_3897_; lean_object* v___y_3898_; lean_object* v___y_3899_; lean_object* v___y_3900_; lean_object* v___y_3901_; lean_object* v___y_3902_; lean_object* v___y_3903_; lean_object* v___y_3904_; lean_object* v___y_3905_; lean_object* v___y_3906_; lean_object* v___y_3907_; lean_object* v___y_3911_; lean_object* v___y_3912_; lean_object* v___y_3913_; lean_object* v___y_3914_; lean_object* v___y_3915_; lean_object* v___y_3916_; lean_object* v___y_3917_; lean_object* v___y_3918_; lean_object* v___y_3919_; lean_object* v___y_3920_; lean_object* v___y_3921_; lean_object* v___y_3922_; lean_object* v___y_3923_; lean_object* v___y_3924_; lean_object* v___y_3925_; lean_object* v___y_3926_; lean_object* v___y_3927_; lean_object* v___y_3928_; lean_object* v___y_3929_; lean_object* v___y_3930_; lean_object* v___y_3931_; lean_object* v___y_3935_; lean_object* v___y_3936_; lean_object* v___y_3937_; lean_object* v___y_3938_; lean_object* v___y_3939_; lean_object* v___y_3940_; lean_object* v___y_3941_; lean_object* v___y_3942_; lean_object* v___y_3943_; lean_object* v___y_3944_; lean_object* v___y_3945_; lean_object* v___y_3946_; lean_object* v___y_3947_; lean_object* v___y_3948_; lean_object* v___y_3949_; lean_object* v___y_3950_; lean_object* v___y_3951_; uint8_t v___y_3952_; lean_object* v___x_3998_; 
v___x_3998_ = l_Lean_Meta_Grind_Order_isLinearPreorder(v_a_3879_, v_a_3880_, v_a_3881_, v_a_3882_, v_a_3883_, v_a_3884_, v_a_3885_, v_a_3886_, v_a_3887_, v_a_3888_, v_a_3889_);
if (lean_obj_tag(v___x_3998_) == 0)
{
lean_object* v_a_3999_; lean_object* v___x_4001_; uint8_t v_isShared_4002_; uint8_t v_isSharedCheck_4321_; 
v_a_3999_ = lean_ctor_get(v___x_3998_, 0);
v_isSharedCheck_4321_ = !lean_is_exclusive(v___x_3998_);
if (v_isSharedCheck_4321_ == 0)
{
v___x_4001_ = v___x_3998_;
v_isShared_4002_ = v_isSharedCheck_4321_;
goto v_resetjp_4000_;
}
else
{
lean_inc(v_a_3999_);
lean_dec(v___x_3998_);
v___x_4001_ = lean_box(0);
v_isShared_4002_ = v_isSharedCheck_4321_;
goto v_resetjp_4000_;
}
v_resetjp_4000_:
{
lean_object* v___y_4004_; lean_object* v___y_4005_; lean_object* v___y_4006_; lean_object* v___y_4007_; lean_object* v___y_4008_; lean_object* v___y_4009_; lean_object* v___y_4010_; lean_object* v___y_4011_; lean_object* v___y_4012_; lean_object* v___y_4013_; lean_object* v___y_4014_; uint8_t v___y_4015_; lean_object* v___y_4016_; lean_object* v___y_4017_; lean_object* v___y_4018_; lean_object* v___y_4019_; lean_object* v___y_4020_; lean_object* v___y_4021_; lean_object* v___y_4022_; lean_object* v___y_4023_; lean_object* v___y_4024_; lean_object* v___y_4030_; lean_object* v___y_4031_; lean_object* v___y_4032_; lean_object* v___y_4033_; lean_object* v___y_4034_; lean_object* v___y_4035_; lean_object* v___y_4036_; lean_object* v___y_4037_; lean_object* v___y_4038_; lean_object* v___y_4039_; lean_object* v___y_4040_; lean_object* v___y_4041_; uint8_t v___y_4042_; lean_object* v___y_4043_; lean_object* v___y_4044_; lean_object* v___y_4045_; lean_object* v___y_4046_; lean_object* v___y_4047_; lean_object* v___y_4048_; lean_object* v___y_4049_; lean_object* v___y_4062_; lean_object* v___y_4063_; lean_object* v___y_4064_; lean_object* v___y_4065_; lean_object* v___y_4066_; lean_object* v___y_4067_; lean_object* v___y_4068_; uint8_t v___y_4069_; lean_object* v___y_4070_; lean_object* v___y_4071_; lean_object* v___y_4072_; lean_object* v___y_4073_; lean_object* v___y_4074_; lean_object* v___y_4075_; lean_object* v___y_4076_; lean_object* v___y_4077_; lean_object* v___y_4078_; lean_object* v_h_4121_; lean_object* v___y_4122_; lean_object* v___y_4123_; lean_object* v___y_4124_; lean_object* v___y_4125_; lean_object* v___y_4126_; lean_object* v___y_4127_; lean_object* v___y_4128_; lean_object* v___y_4129_; lean_object* v___y_4130_; lean_object* v___y_4131_; lean_object* v___y_4132_; lean_object* v___y_4278_; lean_object* v___y_4279_; lean_object* v___y_4280_; lean_object* v___y_4281_; lean_object* v___y_4282_; lean_object* v___y_4283_; lean_object* v___y_4284_; lean_object* v___y_4285_; lean_object* v___y_4286_; lean_object* v___y_4287_; lean_object* v___y_4288_; uint8_t v___x_4296_; 
v___x_4296_ = lean_unbox(v_a_3999_);
if (v___x_4296_ == 0)
{
lean_object* v___x_4297_; lean_object* v___x_4299_; 
lean_dec(v_a_3999_);
lean_dec_ref(v_he_3878_);
lean_dec_ref(v_e_3877_);
lean_dec_ref(v_c_3876_);
v___x_4297_ = lean_box(0);
if (v_isShared_4002_ == 0)
{
lean_ctor_set(v___x_4001_, 0, v___x_4297_);
v___x_4299_ = v___x_4001_;
goto v_reusejp_4298_;
}
else
{
lean_object* v_reuseFailAlloc_4300_; 
v_reuseFailAlloc_4300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4300_, 0, v___x_4297_);
v___x_4299_ = v_reuseFailAlloc_4300_;
goto v_reusejp_4298_;
}
v_reusejp_4298_:
{
return v___x_4299_;
}
}
else
{
lean_object* v_toCold_4301_; lean_object* v_options_4302_; uint8_t v_hasTrace_4303_; 
lean_del_object(v___x_4001_);
v_toCold_4301_ = lean_ctor_get(v_a_3888_, 0);
v_options_4302_ = lean_ctor_get(v_toCold_4301_, 2);
v_hasTrace_4303_ = lean_ctor_get_uint8(v_options_4302_, sizeof(void*)*1);
if (v_hasTrace_4303_ == 0)
{
v___y_4278_ = v_a_3879_;
v___y_4279_ = v_a_3880_;
v___y_4280_ = v_a_3881_;
v___y_4281_ = v_a_3882_;
v___y_4282_ = v_a_3883_;
v___y_4283_ = v_a_3884_;
v___y_4284_ = v_a_3885_;
v___y_4285_ = v_a_3886_;
v___y_4286_ = v_a_3887_;
v___y_4287_ = v_a_3888_;
v___y_4288_ = v_a_3889_;
goto v___jp_4277_;
}
else
{
lean_object* v_inheritedTraceOptions_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; uint8_t v___x_4307_; 
v_inheritedTraceOptions_4304_ = lean_ctor_get(v_toCold_4301_, 11);
v___x_4305_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__4));
v___x_4306_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5);
v___x_4307_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4304_, v_options_4302_, v___x_4306_);
if (v___x_4307_ == 0)
{
v___y_4278_ = v_a_3879_;
v___y_4279_ = v_a_3880_;
v___y_4280_ = v_a_3881_;
v___y_4281_ = v_a_3882_;
v___y_4282_ = v_a_3883_;
v___y_4283_ = v_a_3884_;
v___y_4284_ = v_a_3885_;
v___y_4285_ = v_a_3886_;
v___y_4286_ = v_a_3887_;
v___y_4287_ = v_a_3888_;
v___y_4288_ = v_a_3889_;
goto v___jp_4277_;
}
else
{
lean_object* v___x_4308_; 
v___x_4308_ = l_Lean_Meta_Grind_Order_Cnstr_pp___redArg(v_c_3876_, v_a_3879_, v_a_3880_, v_a_3888_);
if (lean_obj_tag(v___x_4308_) == 0)
{
lean_object* v_a_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; 
v_a_4309_ = lean_ctor_get(v___x_4308_, 0);
lean_inc(v_a_4309_);
lean_dec_ref_known(v___x_4308_, 1);
v___x_4310_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__31, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__31_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__31);
v___x_4311_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4311_, 0, v___x_4310_);
lean_ctor_set(v___x_4311_, 1, v_a_4309_);
v___x_4312_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(v___x_4305_, v___x_4311_, v_a_3886_, v_a_3887_, v_a_3888_, v_a_3889_);
if (lean_obj_tag(v___x_4312_) == 0)
{
lean_dec_ref_known(v___x_4312_, 1);
v___y_4278_ = v_a_3879_;
v___y_4279_ = v_a_3880_;
v___y_4280_ = v_a_3881_;
v___y_4281_ = v_a_3882_;
v___y_4282_ = v_a_3883_;
v___y_4283_ = v_a_3884_;
v___y_4284_ = v_a_3885_;
v___y_4285_ = v_a_3886_;
v___y_4286_ = v_a_3887_;
v___y_4287_ = v_a_3888_;
v___y_4288_ = v_a_3889_;
goto v___jp_4277_;
}
else
{
lean_dec(v_a_3999_);
lean_dec_ref(v_he_3878_);
lean_dec_ref(v_e_3877_);
lean_dec_ref(v_c_3876_);
return v___x_4312_;
}
}
else
{
lean_object* v_a_4313_; lean_object* v___x_4315_; uint8_t v_isShared_4316_; uint8_t v_isSharedCheck_4320_; 
lean_dec(v_a_3999_);
lean_dec_ref(v_he_3878_);
lean_dec_ref(v_e_3877_);
lean_dec_ref(v_c_3876_);
v_a_4313_ = lean_ctor_get(v___x_4308_, 0);
v_isSharedCheck_4320_ = !lean_is_exclusive(v___x_4308_);
if (v_isSharedCheck_4320_ == 0)
{
v___x_4315_ = v___x_4308_;
v_isShared_4316_ = v_isSharedCheck_4320_;
goto v_resetjp_4314_;
}
else
{
lean_inc(v_a_4313_);
lean_dec(v___x_4308_);
v___x_4315_ = lean_box(0);
v_isShared_4316_ = v_isSharedCheck_4320_;
goto v_resetjp_4314_;
}
v_resetjp_4314_:
{
lean_object* v___x_4318_; 
if (v_isShared_4316_ == 0)
{
v___x_4318_ = v___x_4315_;
goto v_reusejp_4317_;
}
else
{
lean_object* v_reuseFailAlloc_4319_; 
v_reuseFailAlloc_4319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4319_, 0, v_a_4313_);
v___x_4318_ = v_reuseFailAlloc_4319_;
goto v_reusejp_4317_;
}
v_reusejp_4317_:
{
return v___x_4318_;
}
}
}
}
}
}
v___jp_4003_:
{
lean_object* v___x_4025_; lean_object* v___x_4026_; 
v___x_4025_ = l_Lean_eagerReflBoolTrue;
lean_inc_ref(v___y_4024_);
v___x_4026_ = l_Lean_mkApp6(v___y_4013_, v___y_4007_, v___y_4005_, v___y_4018_, v___y_4024_, v___x_4025_, v___y_4014_);
if (v___y_4015_ == 0)
{
uint8_t v___x_4027_; 
v___x_4027_ = lean_unbox(v_a_3999_);
lean_dec(v_a_3999_);
v___y_3935_ = v___y_4004_;
v___y_3936_ = v___y_4024_;
v___y_3937_ = v___y_4006_;
v___y_3938_ = v___y_4008_;
v___y_3939_ = v___y_4009_;
v___y_3940_ = v___y_4010_;
v___y_3941_ = v___y_4011_;
v___y_3942_ = v___y_4012_;
v___y_3943_ = v___x_4025_;
v___y_3944_ = v___x_4026_;
v___y_3945_ = v___y_4016_;
v___y_3946_ = v___y_4017_;
v___y_3947_ = v___y_4019_;
v___y_3948_ = v___y_4020_;
v___y_3949_ = v___y_4023_;
v___y_3950_ = v___y_4022_;
v___y_3951_ = v___y_4021_;
v___y_3952_ = v___x_4027_;
goto v___jp_3934_;
}
else
{
uint8_t v___x_4028_; 
lean_dec(v_a_3999_);
v___x_4028_ = 0;
v___y_3935_ = v___y_4004_;
v___y_3936_ = v___y_4024_;
v___y_3937_ = v___y_4006_;
v___y_3938_ = v___y_4008_;
v___y_3939_ = v___y_4009_;
v___y_3940_ = v___y_4010_;
v___y_3941_ = v___y_4011_;
v___y_3942_ = v___y_4012_;
v___y_3943_ = v___x_4025_;
v___y_3944_ = v___x_4026_;
v___y_3945_ = v___y_4016_;
v___y_3946_ = v___y_4017_;
v___y_3947_ = v___y_4019_;
v___y_3948_ = v___y_4020_;
v___y_3949_ = v___y_4023_;
v___y_3950_ = v___y_4022_;
v___y_3951_ = v___y_4021_;
v___y_3952_ = v___x_4028_;
goto v___jp_3934_;
}
}
v___jp_4029_:
{
lean_object* v___x_4050_; uint8_t v___x_4051_; 
v___x_4050_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4);
v___x_4051_ = lean_int_dec_le(v___x_4050_, v___y_4030_);
if (v___x_4051_ == 0)
{
lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; 
v___x_4052_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10);
v___x_4053_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13);
v___x_4054_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16);
v___x_4055_ = lean_int_neg(v___y_4030_);
v___x_4056_ = l_Int_toNat(v___x_4055_);
lean_dec(v___x_4055_);
v___x_4057_ = l_Lean_instToExprInt_mkNat(v___x_4056_);
v___x_4058_ = l_Lean_mkApp3(v___x_4052_, v___x_4053_, v___x_4054_, v___x_4057_);
v___y_4004_ = v___y_4030_;
v___y_4005_ = v___y_4031_;
v___y_4006_ = v___y_4032_;
v___y_4007_ = v___y_4033_;
v___y_4008_ = v___y_4034_;
v___y_4009_ = v___y_4035_;
v___y_4010_ = v___y_4036_;
v___y_4011_ = v___y_4037_;
v___y_4012_ = v___y_4038_;
v___y_4013_ = v___y_4039_;
v___y_4014_ = v___y_4040_;
v___y_4015_ = v___y_4042_;
v___y_4016_ = v___y_4041_;
v___y_4017_ = v___y_4043_;
v___y_4018_ = v___y_4049_;
v___y_4019_ = v___y_4044_;
v___y_4020_ = v___y_4045_;
v___y_4021_ = v___y_4048_;
v___y_4022_ = v___y_4047_;
v___y_4023_ = v___y_4046_;
v___y_4024_ = v___x_4058_;
goto v___jp_4003_;
}
else
{
lean_object* v___x_4059_; lean_object* v___x_4060_; 
v___x_4059_ = l_Int_toNat(v___y_4030_);
v___x_4060_ = l_Lean_instToExprInt_mkNat(v___x_4059_);
v___y_4004_ = v___y_4030_;
v___y_4005_ = v___y_4031_;
v___y_4006_ = v___y_4032_;
v___y_4007_ = v___y_4033_;
v___y_4008_ = v___y_4034_;
v___y_4009_ = v___y_4035_;
v___y_4010_ = v___y_4036_;
v___y_4011_ = v___y_4037_;
v___y_4012_ = v___y_4038_;
v___y_4013_ = v___y_4039_;
v___y_4014_ = v___y_4040_;
v___y_4015_ = v___y_4042_;
v___y_4016_ = v___y_4041_;
v___y_4017_ = v___y_4043_;
v___y_4018_ = v___y_4049_;
v___y_4019_ = v___y_4044_;
v___y_4020_ = v___y_4045_;
v___y_4021_ = v___y_4048_;
v___y_4022_ = v___y_4047_;
v___y_4023_ = v___y_4046_;
v___y_4024_ = v___x_4060_;
goto v___jp_4003_;
}
}
v___jp_4061_:
{
lean_object* v___x_4079_; 
lean_inc(v___y_4078_);
v___x_4079_ = l_Lean_Meta_Grind_Order_mkLinearOrdRingPrefix(v___y_4078_, v___y_4075_, v___y_4065_, v___y_4071_, v___y_4076_, v___y_4067_, v___y_4063_, v___y_4062_, v___y_4064_, v___y_4070_, v___y_4066_, v___y_4077_);
if (lean_obj_tag(v___x_4079_) == 0)
{
lean_object* v_a_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; 
v_a_4080_ = lean_ctor_get(v___x_4079_, 0);
lean_inc(v_a_4080_);
lean_dec_ref_known(v___x_4079_, 1);
v___x_4081_ = lean_int_neg(v___y_4073_);
v___x_4082_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v___y_4074_, v___y_4075_, v___y_4065_, v___y_4066_);
if (lean_obj_tag(v___x_4082_) == 0)
{
lean_object* v_a_4083_; lean_object* v___x_4084_; 
v_a_4083_ = lean_ctor_get(v___x_4082_, 0);
lean_inc(v_a_4083_);
lean_dec_ref_known(v___x_4082_, 1);
v___x_4084_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v___y_4072_, v___y_4075_, v___y_4065_, v___y_4066_);
if (lean_obj_tag(v___x_4084_) == 0)
{
lean_object* v_a_4085_; lean_object* v___x_4086_; uint8_t v___x_4087_; 
v_a_4085_ = lean_ctor_get(v___x_4084_, 0);
lean_inc(v_a_4085_);
lean_dec_ref_known(v___x_4084_, 1);
v___x_4086_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4);
v___x_4087_ = lean_int_dec_le(v___x_4086_, v___y_4073_);
if (v___x_4087_ == 0)
{
lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; 
lean_dec(v___y_4073_);
v___x_4088_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10);
v___x_4089_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13);
v___x_4090_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16);
v___x_4091_ = l_Int_toNat(v___x_4081_);
v___x_4092_ = l_Lean_instToExprInt_mkNat(v___x_4091_);
v___x_4093_ = l_Lean_mkApp3(v___x_4088_, v___x_4089_, v___x_4090_, v___x_4092_);
v___y_4030_ = v___x_4081_;
v___y_4031_ = v_a_4085_;
v___y_4032_ = v___y_4062_;
v___y_4033_ = v_a_4083_;
v___y_4034_ = v___y_4063_;
v___y_4035_ = v___y_4064_;
v___y_4036_ = v___y_4065_;
v___y_4037_ = v___y_4066_;
v___y_4038_ = v___y_4067_;
v___y_4039_ = v_a_4080_;
v___y_4040_ = v___y_4068_;
v___y_4041_ = v___y_4070_;
v___y_4042_ = v___y_4069_;
v___y_4043_ = v___y_4071_;
v___y_4044_ = v___y_4072_;
v___y_4045_ = v___y_4074_;
v___y_4046_ = v___y_4075_;
v___y_4047_ = v___y_4076_;
v___y_4048_ = v___y_4077_;
v___y_4049_ = v___x_4093_;
goto v___jp_4029_;
}
else
{
lean_object* v___x_4094_; lean_object* v___x_4095_; 
v___x_4094_ = l_Int_toNat(v___y_4073_);
lean_dec(v___y_4073_);
v___x_4095_ = l_Lean_instToExprInt_mkNat(v___x_4094_);
v___y_4030_ = v___x_4081_;
v___y_4031_ = v_a_4085_;
v___y_4032_ = v___y_4062_;
v___y_4033_ = v_a_4083_;
v___y_4034_ = v___y_4063_;
v___y_4035_ = v___y_4064_;
v___y_4036_ = v___y_4065_;
v___y_4037_ = v___y_4066_;
v___y_4038_ = v___y_4067_;
v___y_4039_ = v_a_4080_;
v___y_4040_ = v___y_4068_;
v___y_4041_ = v___y_4070_;
v___y_4042_ = v___y_4069_;
v___y_4043_ = v___y_4071_;
v___y_4044_ = v___y_4072_;
v___y_4045_ = v___y_4074_;
v___y_4046_ = v___y_4075_;
v___y_4047_ = v___y_4076_;
v___y_4048_ = v___y_4077_;
v___y_4049_ = v___x_4095_;
goto v___jp_4029_;
}
}
else
{
lean_object* v_a_4096_; lean_object* v___x_4098_; uint8_t v_isShared_4099_; uint8_t v_isSharedCheck_4103_; 
lean_dec(v_a_4083_);
lean_dec(v___x_4081_);
lean_dec(v_a_4080_);
lean_dec(v___y_4074_);
lean_dec(v___y_4073_);
lean_dec(v___y_4072_);
lean_dec_ref(v___y_4068_);
lean_dec(v_a_3999_);
v_a_4096_ = lean_ctor_get(v___x_4084_, 0);
v_isSharedCheck_4103_ = !lean_is_exclusive(v___x_4084_);
if (v_isSharedCheck_4103_ == 0)
{
v___x_4098_ = v___x_4084_;
v_isShared_4099_ = v_isSharedCheck_4103_;
goto v_resetjp_4097_;
}
else
{
lean_inc(v_a_4096_);
lean_dec(v___x_4084_);
v___x_4098_ = lean_box(0);
v_isShared_4099_ = v_isSharedCheck_4103_;
goto v_resetjp_4097_;
}
v_resetjp_4097_:
{
lean_object* v___x_4101_; 
if (v_isShared_4099_ == 0)
{
v___x_4101_ = v___x_4098_;
goto v_reusejp_4100_;
}
else
{
lean_object* v_reuseFailAlloc_4102_; 
v_reuseFailAlloc_4102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4102_, 0, v_a_4096_);
v___x_4101_ = v_reuseFailAlloc_4102_;
goto v_reusejp_4100_;
}
v_reusejp_4100_:
{
return v___x_4101_;
}
}
}
}
else
{
lean_object* v_a_4104_; lean_object* v___x_4106_; uint8_t v_isShared_4107_; uint8_t v_isSharedCheck_4111_; 
lean_dec(v___x_4081_);
lean_dec(v_a_4080_);
lean_dec(v___y_4074_);
lean_dec(v___y_4073_);
lean_dec(v___y_4072_);
lean_dec_ref(v___y_4068_);
lean_dec(v_a_3999_);
v_a_4104_ = lean_ctor_get(v___x_4082_, 0);
v_isSharedCheck_4111_ = !lean_is_exclusive(v___x_4082_);
if (v_isSharedCheck_4111_ == 0)
{
v___x_4106_ = v___x_4082_;
v_isShared_4107_ = v_isSharedCheck_4111_;
goto v_resetjp_4105_;
}
else
{
lean_inc(v_a_4104_);
lean_dec(v___x_4082_);
v___x_4106_ = lean_box(0);
v_isShared_4107_ = v_isSharedCheck_4111_;
goto v_resetjp_4105_;
}
v_resetjp_4105_:
{
lean_object* v___x_4109_; 
if (v_isShared_4107_ == 0)
{
v___x_4109_ = v___x_4106_;
goto v_reusejp_4108_;
}
else
{
lean_object* v_reuseFailAlloc_4110_; 
v_reuseFailAlloc_4110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4110_, 0, v_a_4104_);
v___x_4109_ = v_reuseFailAlloc_4110_;
goto v_reusejp_4108_;
}
v_reusejp_4108_:
{
return v___x_4109_;
}
}
}
}
else
{
lean_object* v_a_4112_; lean_object* v___x_4114_; uint8_t v_isShared_4115_; uint8_t v_isSharedCheck_4119_; 
lean_dec(v___y_4074_);
lean_dec(v___y_4073_);
lean_dec(v___y_4072_);
lean_dec_ref(v___y_4068_);
lean_dec(v_a_3999_);
v_a_4112_ = lean_ctor_get(v___x_4079_, 0);
v_isSharedCheck_4119_ = !lean_is_exclusive(v___x_4079_);
if (v_isSharedCheck_4119_ == 0)
{
v___x_4114_ = v___x_4079_;
v_isShared_4115_ = v_isSharedCheck_4119_;
goto v_resetjp_4113_;
}
else
{
lean_inc(v_a_4112_);
lean_dec(v___x_4079_);
v___x_4114_ = lean_box(0);
v_isShared_4115_ = v_isSharedCheck_4119_;
goto v_resetjp_4113_;
}
v_resetjp_4113_:
{
lean_object* v___x_4117_; 
if (v_isShared_4115_ == 0)
{
v___x_4117_ = v___x_4114_;
goto v_reusejp_4116_;
}
else
{
lean_object* v_reuseFailAlloc_4118_; 
v_reuseFailAlloc_4118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4118_, 0, v_a_4112_);
v___x_4117_ = v_reuseFailAlloc_4118_;
goto v_reusejp_4116_;
}
v_reusejp_4116_:
{
return v___x_4117_;
}
}
}
}
v___jp_4120_:
{
lean_object* v___x_4133_; 
v___x_4133_ = l_Lean_Meta_Grind_Order_isRing(v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_);
if (lean_obj_tag(v___x_4133_) == 0)
{
lean_object* v_a_4134_; uint8_t v___x_4135_; 
v_a_4134_ = lean_ctor_get(v___x_4133_, 0);
lean_inc(v_a_4134_);
lean_dec_ref_known(v___x_4133_, 1);
v___x_4135_ = lean_unbox(v_a_4134_);
if (v___x_4135_ == 0)
{
uint8_t v_kind_4136_; 
v_kind_4136_ = lean_ctor_get_uint8(v_c_3876_, sizeof(void*)*5);
if (v_kind_4136_ == 1)
{
lean_object* v_u_4137_; lean_object* v_v_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; 
lean_dec(v_a_3999_);
v_u_4137_ = lean_ctor_get(v_c_3876_, 0);
lean_inc(v_u_4137_);
v_v_4138_ = lean_ctor_get(v_c_3876_, 1);
lean_inc(v_v_4138_);
lean_dec_ref(v_c_3876_);
v___x_4139_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__18));
v___x_4140_ = l_Lean_Meta_Grind_Order_mkLeLtLinearPrefix(v___x_4139_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_);
if (lean_obj_tag(v___x_4140_) == 0)
{
lean_object* v_a_4141_; lean_object* v___x_4142_; 
v_a_4141_ = lean_ctor_get(v___x_4140_, 0);
lean_inc(v_a_4141_);
lean_dec_ref_known(v___x_4140_, 1);
v___x_4142_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_u_4137_, v___y_4122_, v___y_4123_, v___y_4131_);
if (lean_obj_tag(v___x_4142_) == 0)
{
lean_object* v_a_4143_; lean_object* v___x_4144_; 
v_a_4143_ = lean_ctor_get(v___x_4142_, 0);
lean_inc(v_a_4143_);
lean_dec_ref_known(v___x_4142_, 1);
v___x_4144_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_v_4138_, v___y_4122_, v___y_4123_, v___y_4131_);
if (lean_obj_tag(v___x_4144_) == 0)
{
lean_object* v_a_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; uint8_t v___x_4149_; lean_object* v___x_4150_; 
v_a_4145_ = lean_ctor_get(v___x_4144_, 0);
lean_inc(v_a_4145_);
lean_dec_ref_known(v___x_4144_, 1);
v___x_4146_ = l_Lean_mkApp3(v_a_4141_, v_a_4143_, v_a_4145_, v_h_4121_);
v___x_4147_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4);
v___x_4148_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4148_, 0, v___x_4147_);
v___x_4149_ = lean_unbox(v_a_4134_);
lean_dec(v_a_4134_);
lean_ctor_set_uint8(v___x_4148_, sizeof(void*)*1, v___x_4149_);
v___x_4150_ = l_Lean_Meta_Grind_Order_addEdge(v_v_4138_, v_u_4137_, v___x_4148_, v___x_4146_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_);
return v___x_4150_;
}
else
{
lean_object* v_a_4151_; lean_object* v___x_4153_; uint8_t v_isShared_4154_; uint8_t v_isSharedCheck_4158_; 
lean_dec(v_a_4143_);
lean_dec(v_a_4141_);
lean_dec(v_v_4138_);
lean_dec(v_u_4137_);
lean_dec(v_a_4134_);
lean_dec_ref(v_h_4121_);
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
lean_dec(v_v_4138_);
lean_dec(v_u_4137_);
lean_dec(v_a_4134_);
lean_dec_ref(v_h_4121_);
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
lean_dec(v_v_4138_);
lean_dec(v_u_4137_);
lean_dec(v_a_4134_);
lean_dec_ref(v_h_4121_);
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
lean_object* v_u_4175_; lean_object* v_v_4176_; lean_object* v___x_4177_; 
lean_dec(v_a_4134_);
v_u_4175_ = lean_ctor_get(v_c_3876_, 0);
lean_inc(v_u_4175_);
v_v_4176_ = lean_ctor_get(v_c_3876_, 1);
lean_inc(v_v_4176_);
lean_dec_ref(v_c_3876_);
v___x_4177_ = l_Lean_Meta_Grind_Order_hasLt(v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_);
if (lean_obj_tag(v___x_4177_) == 0)
{
lean_object* v_a_4178_; uint8_t v___x_4179_; 
v_a_4178_ = lean_ctor_get(v___x_4177_, 0);
lean_inc(v_a_4178_);
lean_dec_ref_known(v___x_4177_, 1);
v___x_4179_ = lean_unbox(v_a_4178_);
if (v___x_4179_ == 0)
{
lean_object* v___x_4180_; lean_object* v___x_4181_; 
lean_dec(v_a_3999_);
v___x_4180_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__20));
v___x_4181_ = l_Lean_Meta_Grind_Order_mkLeLinearPrefix(v___x_4180_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_);
if (lean_obj_tag(v___x_4181_) == 0)
{
lean_object* v_a_4182_; lean_object* v___x_4183_; 
v_a_4182_ = lean_ctor_get(v___x_4181_, 0);
lean_inc(v_a_4182_);
lean_dec_ref_known(v___x_4181_, 1);
v___x_4183_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_u_4175_, v___y_4122_, v___y_4123_, v___y_4131_);
if (lean_obj_tag(v___x_4183_) == 0)
{
lean_object* v_a_4184_; lean_object* v___x_4185_; 
v_a_4184_ = lean_ctor_get(v___x_4183_, 0);
lean_inc(v_a_4184_);
lean_dec_ref_known(v___x_4183_, 1);
v___x_4185_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_v_4176_, v___y_4122_, v___y_4123_, v___y_4131_);
if (lean_obj_tag(v___x_4185_) == 0)
{
lean_object* v_a_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; uint8_t v___x_4190_; lean_object* v___x_4191_; 
v_a_4186_ = lean_ctor_get(v___x_4185_, 0);
lean_inc(v_a_4186_);
lean_dec_ref_known(v___x_4185_, 1);
v___x_4187_ = l_Lean_mkApp3(v_a_4182_, v_a_4184_, v_a_4186_, v_h_4121_);
v___x_4188_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4);
v___x_4189_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4189_, 0, v___x_4188_);
v___x_4190_ = lean_unbox(v_a_4178_);
lean_dec(v_a_4178_);
lean_ctor_set_uint8(v___x_4189_, sizeof(void*)*1, v___x_4190_);
v___x_4191_ = l_Lean_Meta_Grind_Order_addEdge(v_v_4176_, v_u_4175_, v___x_4189_, v___x_4187_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_);
return v___x_4191_;
}
else
{
lean_object* v_a_4192_; lean_object* v___x_4194_; uint8_t v_isShared_4195_; uint8_t v_isSharedCheck_4199_; 
lean_dec(v_a_4184_);
lean_dec(v_a_4182_);
lean_dec(v_a_4178_);
lean_dec(v_v_4176_);
lean_dec(v_u_4175_);
lean_dec_ref(v_h_4121_);
v_a_4192_ = lean_ctor_get(v___x_4185_, 0);
v_isSharedCheck_4199_ = !lean_is_exclusive(v___x_4185_);
if (v_isSharedCheck_4199_ == 0)
{
v___x_4194_ = v___x_4185_;
v_isShared_4195_ = v_isSharedCheck_4199_;
goto v_resetjp_4193_;
}
else
{
lean_inc(v_a_4192_);
lean_dec(v___x_4185_);
v___x_4194_ = lean_box(0);
v_isShared_4195_ = v_isSharedCheck_4199_;
goto v_resetjp_4193_;
}
v_resetjp_4193_:
{
lean_object* v___x_4197_; 
if (v_isShared_4195_ == 0)
{
v___x_4197_ = v___x_4194_;
goto v_reusejp_4196_;
}
else
{
lean_object* v_reuseFailAlloc_4198_; 
v_reuseFailAlloc_4198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4198_, 0, v_a_4192_);
v___x_4197_ = v_reuseFailAlloc_4198_;
goto v_reusejp_4196_;
}
v_reusejp_4196_:
{
return v___x_4197_;
}
}
}
}
else
{
lean_object* v_a_4200_; lean_object* v___x_4202_; uint8_t v_isShared_4203_; uint8_t v_isSharedCheck_4207_; 
lean_dec(v_a_4182_);
lean_dec(v_a_4178_);
lean_dec(v_v_4176_);
lean_dec(v_u_4175_);
lean_dec_ref(v_h_4121_);
v_a_4200_ = lean_ctor_get(v___x_4183_, 0);
v_isSharedCheck_4207_ = !lean_is_exclusive(v___x_4183_);
if (v_isSharedCheck_4207_ == 0)
{
v___x_4202_ = v___x_4183_;
v_isShared_4203_ = v_isSharedCheck_4207_;
goto v_resetjp_4201_;
}
else
{
lean_inc(v_a_4200_);
lean_dec(v___x_4183_);
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
lean_dec(v_a_4178_);
lean_dec(v_v_4176_);
lean_dec(v_u_4175_);
lean_dec_ref(v_h_4121_);
v_a_4208_ = lean_ctor_get(v___x_4181_, 0);
v_isSharedCheck_4215_ = !lean_is_exclusive(v___x_4181_);
if (v_isSharedCheck_4215_ == 0)
{
v___x_4210_ = v___x_4181_;
v_isShared_4211_ = v_isSharedCheck_4215_;
goto v_resetjp_4209_;
}
else
{
lean_inc(v_a_4208_);
lean_dec(v___x_4181_);
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
lean_object* v___x_4216_; lean_object* v___x_4217_; 
lean_dec(v_a_4178_);
v___x_4216_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__22));
v___x_4217_ = l_Lean_Meta_Grind_Order_mkLeLtLinearPrefix(v___x_4216_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_);
if (lean_obj_tag(v___x_4217_) == 0)
{
lean_object* v_a_4218_; lean_object* v___x_4219_; 
v_a_4218_ = lean_ctor_get(v___x_4217_, 0);
lean_inc(v_a_4218_);
lean_dec_ref_known(v___x_4217_, 1);
v___x_4219_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_u_4175_, v___y_4122_, v___y_4123_, v___y_4131_);
if (lean_obj_tag(v___x_4219_) == 0)
{
lean_object* v_a_4220_; lean_object* v___x_4221_; 
v_a_4220_ = lean_ctor_get(v___x_4219_, 0);
lean_inc(v_a_4220_);
lean_dec_ref_known(v___x_4219_, 1);
v___x_4221_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_v_4176_, v___y_4122_, v___y_4123_, v___y_4131_);
if (lean_obj_tag(v___x_4221_) == 0)
{
lean_object* v_a_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; uint8_t v___x_4226_; lean_object* v___x_4227_; 
v_a_4222_ = lean_ctor_get(v___x_4221_, 0);
lean_inc(v_a_4222_);
lean_dec_ref_known(v___x_4221_, 1);
v___x_4223_ = l_Lean_mkApp3(v_a_4218_, v_a_4220_, v_a_4222_, v_h_4121_);
v___x_4224_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4);
v___x_4225_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4225_, 0, v___x_4224_);
v___x_4226_ = lean_unbox(v_a_3999_);
lean_dec(v_a_3999_);
lean_ctor_set_uint8(v___x_4225_, sizeof(void*)*1, v___x_4226_);
v___x_4227_ = l_Lean_Meta_Grind_Order_addEdge(v_v_4176_, v_u_4175_, v___x_4225_, v___x_4223_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_);
return v___x_4227_;
}
else
{
lean_object* v_a_4228_; lean_object* v___x_4230_; uint8_t v_isShared_4231_; uint8_t v_isSharedCheck_4235_; 
lean_dec(v_a_4220_);
lean_dec(v_a_4218_);
lean_dec(v_v_4176_);
lean_dec(v_u_4175_);
lean_dec_ref(v_h_4121_);
lean_dec(v_a_3999_);
v_a_4228_ = lean_ctor_get(v___x_4221_, 0);
v_isSharedCheck_4235_ = !lean_is_exclusive(v___x_4221_);
if (v_isSharedCheck_4235_ == 0)
{
v___x_4230_ = v___x_4221_;
v_isShared_4231_ = v_isSharedCheck_4235_;
goto v_resetjp_4229_;
}
else
{
lean_inc(v_a_4228_);
lean_dec(v___x_4221_);
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
else
{
lean_object* v_a_4236_; lean_object* v___x_4238_; uint8_t v_isShared_4239_; uint8_t v_isSharedCheck_4243_; 
lean_dec(v_a_4218_);
lean_dec(v_v_4176_);
lean_dec(v_u_4175_);
lean_dec_ref(v_h_4121_);
lean_dec(v_a_3999_);
v_a_4236_ = lean_ctor_get(v___x_4219_, 0);
v_isSharedCheck_4243_ = !lean_is_exclusive(v___x_4219_);
if (v_isSharedCheck_4243_ == 0)
{
v___x_4238_ = v___x_4219_;
v_isShared_4239_ = v_isSharedCheck_4243_;
goto v_resetjp_4237_;
}
else
{
lean_inc(v_a_4236_);
lean_dec(v___x_4219_);
v___x_4238_ = lean_box(0);
v_isShared_4239_ = v_isSharedCheck_4243_;
goto v_resetjp_4237_;
}
v_resetjp_4237_:
{
lean_object* v___x_4241_; 
if (v_isShared_4239_ == 0)
{
v___x_4241_ = v___x_4238_;
goto v_reusejp_4240_;
}
else
{
lean_object* v_reuseFailAlloc_4242_; 
v_reuseFailAlloc_4242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4242_, 0, v_a_4236_);
v___x_4241_ = v_reuseFailAlloc_4242_;
goto v_reusejp_4240_;
}
v_reusejp_4240_:
{
return v___x_4241_;
}
}
}
}
else
{
lean_object* v_a_4244_; lean_object* v___x_4246_; uint8_t v_isShared_4247_; uint8_t v_isSharedCheck_4251_; 
lean_dec(v_v_4176_);
lean_dec(v_u_4175_);
lean_dec_ref(v_h_4121_);
lean_dec(v_a_3999_);
v_a_4244_ = lean_ctor_get(v___x_4217_, 0);
v_isSharedCheck_4251_ = !lean_is_exclusive(v___x_4217_);
if (v_isSharedCheck_4251_ == 0)
{
v___x_4246_ = v___x_4217_;
v_isShared_4247_ = v_isSharedCheck_4251_;
goto v_resetjp_4245_;
}
else
{
lean_inc(v_a_4244_);
lean_dec(v___x_4217_);
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
}
else
{
lean_object* v_a_4252_; lean_object* v___x_4254_; uint8_t v_isShared_4255_; uint8_t v_isSharedCheck_4259_; 
lean_dec(v_v_4176_);
lean_dec(v_u_4175_);
lean_dec_ref(v_h_4121_);
lean_dec(v_a_3999_);
v_a_4252_ = lean_ctor_get(v___x_4177_, 0);
v_isSharedCheck_4259_ = !lean_is_exclusive(v___x_4177_);
if (v_isSharedCheck_4259_ == 0)
{
v___x_4254_ = v___x_4177_;
v_isShared_4255_ = v_isSharedCheck_4259_;
goto v_resetjp_4253_;
}
else
{
lean_inc(v_a_4252_);
lean_dec(v___x_4177_);
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
}
else
{
uint8_t v_kind_4260_; 
lean_dec(v_a_4134_);
v_kind_4260_ = lean_ctor_get_uint8(v_c_3876_, sizeof(void*)*5);
if (v_kind_4260_ == 1)
{
lean_object* v_u_4261_; lean_object* v_v_4262_; lean_object* v_k_4263_; lean_object* v___x_4264_; 
v_u_4261_ = lean_ctor_get(v_c_3876_, 0);
lean_inc(v_u_4261_);
v_v_4262_ = lean_ctor_get(v_c_3876_, 1);
lean_inc(v_v_4262_);
v_k_4263_ = lean_ctor_get(v_c_3876_, 2);
lean_inc(v_k_4263_);
lean_dec_ref(v_c_3876_);
v___x_4264_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__24));
v___y_4062_ = v___y_4128_;
v___y_4063_ = v___y_4127_;
v___y_4064_ = v___y_4129_;
v___y_4065_ = v___y_4123_;
v___y_4066_ = v___y_4131_;
v___y_4067_ = v___y_4126_;
v___y_4068_ = v_h_4121_;
v___y_4069_ = v_kind_4260_;
v___y_4070_ = v___y_4130_;
v___y_4071_ = v___y_4124_;
v___y_4072_ = v_v_4262_;
v___y_4073_ = v_k_4263_;
v___y_4074_ = v_u_4261_;
v___y_4075_ = v___y_4122_;
v___y_4076_ = v___y_4125_;
v___y_4077_ = v___y_4132_;
v___y_4078_ = v___x_4264_;
goto v___jp_4061_;
}
else
{
lean_object* v_u_4265_; lean_object* v_v_4266_; lean_object* v_k_4267_; lean_object* v___x_4268_; 
v_u_4265_ = lean_ctor_get(v_c_3876_, 0);
lean_inc(v_u_4265_);
v_v_4266_ = lean_ctor_get(v_c_3876_, 1);
lean_inc(v_v_4266_);
v_k_4267_ = lean_ctor_get(v_c_3876_, 2);
lean_inc(v_k_4267_);
lean_dec_ref(v_c_3876_);
v___x_4268_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__26));
v___y_4062_ = v___y_4128_;
v___y_4063_ = v___y_4127_;
v___y_4064_ = v___y_4129_;
v___y_4065_ = v___y_4123_;
v___y_4066_ = v___y_4131_;
v___y_4067_ = v___y_4126_;
v___y_4068_ = v_h_4121_;
v___y_4069_ = v_kind_4260_;
v___y_4070_ = v___y_4130_;
v___y_4071_ = v___y_4124_;
v___y_4072_ = v_v_4266_;
v___y_4073_ = v_k_4267_;
v___y_4074_ = v_u_4265_;
v___y_4075_ = v___y_4122_;
v___y_4076_ = v___y_4125_;
v___y_4077_ = v___y_4132_;
v___y_4078_ = v___x_4268_;
goto v___jp_4061_;
}
}
}
else
{
lean_object* v_a_4269_; lean_object* v___x_4271_; uint8_t v_isShared_4272_; uint8_t v_isSharedCheck_4276_; 
lean_dec_ref(v_h_4121_);
lean_dec(v_a_3999_);
lean_dec_ref(v_c_3876_);
v_a_4269_ = lean_ctor_get(v___x_4133_, 0);
v_isSharedCheck_4276_ = !lean_is_exclusive(v___x_4133_);
if (v_isSharedCheck_4276_ == 0)
{
v___x_4271_ = v___x_4133_;
v_isShared_4272_ = v_isSharedCheck_4276_;
goto v_resetjp_4270_;
}
else
{
lean_inc(v_a_4269_);
lean_dec(v___x_4133_);
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
}
v___jp_4277_:
{
lean_object* v_h_x3f_4289_; 
v_h_x3f_4289_ = lean_ctor_get(v_c_3876_, 4);
if (lean_obj_tag(v_h_x3f_4289_) == 1)
{
lean_object* v_e_4290_; lean_object* v_val_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; 
v_e_4290_ = lean_ctor_get(v_c_3876_, 3);
v_val_4291_ = lean_ctor_get(v_h_x3f_4289_, 0);
v___x_4292_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__29, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__29_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__29);
lean_inc_ref(v_e_3877_);
v___x_4293_ = l_Lean_Meta_mkOfEqFalseCore(v_e_3877_, v_he_3878_);
lean_inc(v_val_4291_);
lean_inc_ref(v_e_4290_);
v___x_4294_ = l_Lean_mkApp4(v___x_4292_, v_e_3877_, v_e_4290_, v_val_4291_, v___x_4293_);
v_h_4121_ = v___x_4294_;
v___y_4122_ = v___y_4278_;
v___y_4123_ = v___y_4279_;
v___y_4124_ = v___y_4280_;
v___y_4125_ = v___y_4281_;
v___y_4126_ = v___y_4282_;
v___y_4127_ = v___y_4283_;
v___y_4128_ = v___y_4284_;
v___y_4129_ = v___y_4285_;
v___y_4130_ = v___y_4286_;
v___y_4131_ = v___y_4287_;
v___y_4132_ = v___y_4288_;
goto v___jp_4120_;
}
else
{
lean_object* v___x_4295_; 
v___x_4295_ = l_Lean_Meta_mkOfEqFalseCore(v_e_3877_, v_he_3878_);
v_h_4121_ = v___x_4295_;
v___y_4122_ = v___y_4278_;
v___y_4123_ = v___y_4279_;
v___y_4124_ = v___y_4280_;
v___y_4125_ = v___y_4281_;
v___y_4126_ = v___y_4282_;
v___y_4127_ = v___y_4283_;
v___y_4128_ = v___y_4284_;
v___y_4129_ = v___y_4285_;
v___y_4130_ = v___y_4286_;
v___y_4131_ = v___y_4287_;
v___y_4132_ = v___y_4288_;
goto v___jp_4120_;
}
}
}
}
else
{
lean_object* v_a_4322_; lean_object* v___x_4324_; uint8_t v_isShared_4325_; uint8_t v_isSharedCheck_4329_; 
lean_dec_ref(v_he_3878_);
lean_dec_ref(v_e_3877_);
lean_dec_ref(v_c_3876_);
v_a_4322_ = lean_ctor_get(v___x_3998_, 0);
v_isSharedCheck_4329_ = !lean_is_exclusive(v___x_3998_);
if (v_isSharedCheck_4329_ == 0)
{
v___x_4324_ = v___x_3998_;
v_isShared_4325_ = v_isSharedCheck_4329_;
goto v_resetjp_4323_;
}
else
{
lean_inc(v_a_4322_);
lean_dec(v___x_3998_);
v___x_4324_ = lean_box(0);
v_isShared_4325_ = v_isSharedCheck_4329_;
goto v_resetjp_4323_;
}
v_resetjp_4323_:
{
lean_object* v___x_4327_; 
if (v_isShared_4325_ == 0)
{
v___x_4327_ = v___x_4324_;
goto v_reusejp_4326_;
}
else
{
lean_object* v_reuseFailAlloc_4328_; 
v_reuseFailAlloc_4328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4328_, 0, v_a_4322_);
v___x_4327_ = v_reuseFailAlloc_4328_;
goto v_reusejp_4326_;
}
v_reusejp_4326_:
{
return v___x_4327_;
}
}
}
v___jp_3891_:
{
lean_object* v___x_3908_; lean_object* v___x_3909_; 
v___x_3908_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3908_, 0, v_k_x27_3894_);
lean_ctor_set_uint8(v___x_3908_, sizeof(void*)*1, v_strict_3896_);
v___x_3909_ = l_Lean_Meta_Grind_Order_addEdge(v___y_3892_, v___y_3893_, v___x_3908_, v_h_3895_, v___y_3897_, v___y_3898_, v___y_3899_, v___y_3900_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_);
return v___x_3909_;
}
v___jp_3910_:
{
lean_object* v___x_3932_; uint8_t v___x_3933_; 
lean_inc_ref(v___y_3919_);
v___x_3932_ = l_Lean_mkApp6(v___y_3919_, v___y_3914_, v___y_3923_, v___y_3911_, v___y_3931_, v___y_3920_, v___y_3921_);
v___x_3933_ = 0;
v___y_3892_ = v___y_3926_;
v___y_3893_ = v___y_3927_;
v_k_x27_3894_ = v___y_3924_;
v_h_3895_ = v___x_3932_;
v_strict_3896_ = v___x_3933_;
v___y_3897_ = v___y_3929_;
v___y_3898_ = v___y_3916_;
v___y_3899_ = v___y_3925_;
v___y_3900_ = v___y_3930_;
v___y_3901_ = v___y_3918_;
v___y_3902_ = v___y_3915_;
v___y_3903_ = v___y_3912_;
v___y_3904_ = v___y_3913_;
v___y_3905_ = v___y_3922_;
v___y_3906_ = v___y_3917_;
v___y_3907_ = v___y_3928_;
goto v___jp_3891_;
}
v___jp_3934_:
{
lean_object* v___x_3953_; 
v___x_3953_ = l_Lean_Meta_Grind_Order_isInt(v___y_3949_, v___y_3940_, v___y_3946_, v___y_3950_, v___y_3942_, v___y_3938_, v___y_3937_, v___y_3939_, v___y_3945_, v___y_3941_, v___y_3951_);
if (lean_obj_tag(v___x_3953_) == 0)
{
lean_object* v_a_3954_; uint8_t v___x_3955_; 
v_a_3954_ = lean_ctor_get(v___x_3953_, 0);
lean_inc(v_a_3954_);
lean_dec_ref_known(v___x_3953_, 1);
v___x_3955_ = lean_unbox(v_a_3954_);
lean_dec(v_a_3954_);
if (v___x_3955_ == 0)
{
lean_dec_ref(v___y_3943_);
lean_dec_ref(v___y_3936_);
v___y_3892_ = v___y_3947_;
v___y_3893_ = v___y_3948_;
v_k_x27_3894_ = v___y_3935_;
v_h_3895_ = v___y_3944_;
v_strict_3896_ = v___y_3952_;
v___y_3897_ = v___y_3949_;
v___y_3898_ = v___y_3940_;
v___y_3899_ = v___y_3946_;
v___y_3900_ = v___y_3950_;
v___y_3901_ = v___y_3942_;
v___y_3902_ = v___y_3938_;
v___y_3903_ = v___y_3937_;
v___y_3904_ = v___y_3939_;
v___y_3905_ = v___y_3945_;
v___y_3906_ = v___y_3941_;
v___y_3907_ = v___y_3951_;
goto v___jp_3891_;
}
else
{
if (v___y_3952_ == 0)
{
lean_dec_ref(v___y_3943_);
lean_dec_ref(v___y_3936_);
v___y_3892_ = v___y_3947_;
v___y_3893_ = v___y_3948_;
v_k_x27_3894_ = v___y_3935_;
v_h_3895_ = v___y_3944_;
v_strict_3896_ = v___y_3952_;
v___y_3897_ = v___y_3949_;
v___y_3898_ = v___y_3940_;
v___y_3899_ = v___y_3946_;
v___y_3900_ = v___y_3950_;
v___y_3901_ = v___y_3942_;
v___y_3902_ = v___y_3938_;
v___y_3903_ = v___y_3937_;
v___y_3904_ = v___y_3939_;
v___y_3905_ = v___y_3945_;
v___y_3906_ = v___y_3941_;
v___y_3907_ = v___y_3951_;
goto v___jp_3891_;
}
else
{
lean_object* v___x_3956_; 
v___x_3956_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v___y_3947_, v___y_3949_, v___y_3940_, v___y_3941_);
if (lean_obj_tag(v___x_3956_) == 0)
{
lean_object* v_a_3957_; lean_object* v___x_3958_; 
v_a_3957_ = lean_ctor_get(v___x_3956_, 0);
lean_inc(v_a_3957_);
lean_dec_ref_known(v___x_3956_, 1);
v___x_3958_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v___y_3948_, v___y_3949_, v___y_3940_, v___y_3941_);
if (lean_obj_tag(v___x_3958_) == 0)
{
lean_object* v_a_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; uint8_t v___x_3964_; 
v_a_3959_ = lean_ctor_get(v___x_3958_, 0);
lean_inc(v_a_3959_);
lean_dec_ref_known(v___x_3958_, 1);
v___x_3960_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__2, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__2);
v___x_3961_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__3);
v___x_3962_ = lean_int_sub(v___y_3935_, v___x_3961_);
lean_dec(v___y_3935_);
v___x_3963_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4);
v___x_3964_ = lean_int_dec_le(v___x_3963_, v___x_3962_);
if (v___x_3964_ == 0)
{
lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; 
v___x_3965_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10);
v___x_3966_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13);
v___x_3967_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16);
v___x_3968_ = lean_int_neg(v___x_3962_);
v___x_3969_ = l_Int_toNat(v___x_3968_);
lean_dec(v___x_3968_);
v___x_3970_ = l_Lean_instToExprInt_mkNat(v___x_3969_);
v___x_3971_ = l_Lean_mkApp3(v___x_3965_, v___x_3966_, v___x_3967_, v___x_3970_);
v___y_3911_ = v___y_3936_;
v___y_3912_ = v___y_3937_;
v___y_3913_ = v___y_3939_;
v___y_3914_ = v_a_3957_;
v___y_3915_ = v___y_3938_;
v___y_3916_ = v___y_3940_;
v___y_3917_ = v___y_3941_;
v___y_3918_ = v___y_3942_;
v___y_3919_ = v___x_3960_;
v___y_3920_ = v___y_3943_;
v___y_3921_ = v___y_3944_;
v___y_3922_ = v___y_3945_;
v___y_3923_ = v_a_3959_;
v___y_3924_ = v___x_3962_;
v___y_3925_ = v___y_3946_;
v___y_3926_ = v___y_3947_;
v___y_3927_ = v___y_3948_;
v___y_3928_ = v___y_3951_;
v___y_3929_ = v___y_3949_;
v___y_3930_ = v___y_3950_;
v___y_3931_ = v___x_3971_;
goto v___jp_3910_;
}
else
{
lean_object* v___x_3972_; lean_object* v___x_3973_; 
v___x_3972_ = l_Int_toNat(v___x_3962_);
v___x_3973_ = l_Lean_instToExprInt_mkNat(v___x_3972_);
v___y_3911_ = v___y_3936_;
v___y_3912_ = v___y_3937_;
v___y_3913_ = v___y_3939_;
v___y_3914_ = v_a_3957_;
v___y_3915_ = v___y_3938_;
v___y_3916_ = v___y_3940_;
v___y_3917_ = v___y_3941_;
v___y_3918_ = v___y_3942_;
v___y_3919_ = v___x_3960_;
v___y_3920_ = v___y_3943_;
v___y_3921_ = v___y_3944_;
v___y_3922_ = v___y_3945_;
v___y_3923_ = v_a_3959_;
v___y_3924_ = v___x_3962_;
v___y_3925_ = v___y_3946_;
v___y_3926_ = v___y_3947_;
v___y_3927_ = v___y_3948_;
v___y_3928_ = v___y_3951_;
v___y_3929_ = v___y_3949_;
v___y_3930_ = v___y_3950_;
v___y_3931_ = v___x_3973_;
goto v___jp_3910_;
}
}
else
{
lean_object* v_a_3974_; lean_object* v___x_3976_; uint8_t v_isShared_3977_; uint8_t v_isSharedCheck_3981_; 
lean_dec(v_a_3957_);
lean_dec(v___y_3948_);
lean_dec(v___y_3947_);
lean_dec_ref(v___y_3944_);
lean_dec_ref(v___y_3943_);
lean_dec_ref(v___y_3936_);
lean_dec(v___y_3935_);
v_a_3974_ = lean_ctor_get(v___x_3958_, 0);
v_isSharedCheck_3981_ = !lean_is_exclusive(v___x_3958_);
if (v_isSharedCheck_3981_ == 0)
{
v___x_3976_ = v___x_3958_;
v_isShared_3977_ = v_isSharedCheck_3981_;
goto v_resetjp_3975_;
}
else
{
lean_inc(v_a_3974_);
lean_dec(v___x_3958_);
v___x_3976_ = lean_box(0);
v_isShared_3977_ = v_isSharedCheck_3981_;
goto v_resetjp_3975_;
}
v_resetjp_3975_:
{
lean_object* v___x_3979_; 
if (v_isShared_3977_ == 0)
{
v___x_3979_ = v___x_3976_;
goto v_reusejp_3978_;
}
else
{
lean_object* v_reuseFailAlloc_3980_; 
v_reuseFailAlloc_3980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3980_, 0, v_a_3974_);
v___x_3979_ = v_reuseFailAlloc_3980_;
goto v_reusejp_3978_;
}
v_reusejp_3978_:
{
return v___x_3979_;
}
}
}
}
else
{
lean_object* v_a_3982_; lean_object* v___x_3984_; uint8_t v_isShared_3985_; uint8_t v_isSharedCheck_3989_; 
lean_dec(v___y_3948_);
lean_dec(v___y_3947_);
lean_dec_ref(v___y_3944_);
lean_dec_ref(v___y_3943_);
lean_dec_ref(v___y_3936_);
lean_dec(v___y_3935_);
v_a_3982_ = lean_ctor_get(v___x_3956_, 0);
v_isSharedCheck_3989_ = !lean_is_exclusive(v___x_3956_);
if (v_isSharedCheck_3989_ == 0)
{
v___x_3984_ = v___x_3956_;
v_isShared_3985_ = v_isSharedCheck_3989_;
goto v_resetjp_3983_;
}
else
{
lean_inc(v_a_3982_);
lean_dec(v___x_3956_);
v___x_3984_ = lean_box(0);
v_isShared_3985_ = v_isSharedCheck_3989_;
goto v_resetjp_3983_;
}
v_resetjp_3983_:
{
lean_object* v___x_3987_; 
if (v_isShared_3985_ == 0)
{
v___x_3987_ = v___x_3984_;
goto v_reusejp_3986_;
}
else
{
lean_object* v_reuseFailAlloc_3988_; 
v_reuseFailAlloc_3988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3988_, 0, v_a_3982_);
v___x_3987_ = v_reuseFailAlloc_3988_;
goto v_reusejp_3986_;
}
v_reusejp_3986_:
{
return v___x_3987_;
}
}
}
}
}
}
else
{
lean_object* v_a_3990_; lean_object* v___x_3992_; uint8_t v_isShared_3993_; uint8_t v_isSharedCheck_3997_; 
lean_dec(v___y_3948_);
lean_dec(v___y_3947_);
lean_dec_ref(v___y_3944_);
lean_dec_ref(v___y_3943_);
lean_dec_ref(v___y_3936_);
lean_dec(v___y_3935_);
v_a_3990_ = lean_ctor_get(v___x_3953_, 0);
v_isSharedCheck_3997_ = !lean_is_exclusive(v___x_3953_);
if (v_isSharedCheck_3997_ == 0)
{
v___x_3992_ = v___x_3953_;
v_isShared_3993_ = v_isSharedCheck_3997_;
goto v_resetjp_3991_;
}
else
{
lean_inc(v_a_3990_);
lean_dec(v___x_3953_);
v___x_3992_ = lean_box(0);
v_isShared_3993_ = v_isSharedCheck_3997_;
goto v_resetjp_3991_;
}
v_resetjp_3991_:
{
lean_object* v___x_3995_; 
if (v_isShared_3993_ == 0)
{
v___x_3995_ = v___x_3992_;
goto v_reusejp_3994_;
}
else
{
lean_object* v_reuseFailAlloc_3996_; 
v_reuseFailAlloc_3996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3996_, 0, v_a_3990_);
v___x_3995_ = v_reuseFailAlloc_3996_;
goto v_reusejp_3994_;
}
v_reusejp_3994_:
{
return v___x_3995_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_3876_ = stack[0].m_obj;
lean_object* v_e_3877_ = stack[1].m_obj;
lean_object* v_he_3878_ = stack[2].m_obj;
lean_object* v_a_3879_ = stack[3].m_obj;
lean_object* v_a_3880_ = stack[4].m_obj;
lean_object* v_a_3881_ = stack[5].m_obj;
lean_object* v_a_3882_ = stack[6].m_obj;
lean_object* v_a_3883_ = stack[7].m_obj;
lean_object* v_a_3884_ = stack[8].m_obj;
lean_object* v_a_3885_ = stack[9].m_obj;
lean_object* v_a_3886_ = stack[10].m_obj;
lean_object* v_a_3887_ = stack[11].m_obj;
lean_object* v_a_3888_ = stack[12].m_obj;
lean_object* v_a_3889_ = stack[13].m_obj;
lean_object* v_res_4330_;
v_res_4330_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse(v_c_3876_, v_e_3877_, v_he_3878_, v_a_3879_, v_a_3880_, v_a_3881_, v_a_3882_, v_a_3883_, v_a_3884_, v_a_3885_, v_a_3886_, v_a_3887_, v_a_3888_, v_a_3889_);
stack->m_obj
 = v_res_4330_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___boxed(lean_object* v_c_4331_, lean_object* v_e_4332_, lean_object* v_he_4333_, lean_object* v_a_4334_, lean_object* v_a_4335_, lean_object* v_a_4336_, lean_object* v_a_4337_, lean_object* v_a_4338_, lean_object* v_a_4339_, lean_object* v_a_4340_, lean_object* v_a_4341_, lean_object* v_a_4342_, lean_object* v_a_4343_, lean_object* v_a_4344_, lean_object* v_a_4345_){
_start:
{
lean_object* v_res_4346_; 
v_res_4346_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse(v_c_4331_, v_e_4332_, v_he_4333_, v_a_4334_, v_a_4335_, v_a_4336_, v_a_4337_, v_a_4338_, v_a_4339_, v_a_4340_, v_a_4341_, v_a_4342_, v_a_4343_, v_a_4344_);
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
lean_dec(v_a_4334_);
return v_res_4346_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___redArg(lean_object* v_e_4347_, lean_object* v_a_4348_, lean_object* v_a_4349_){
_start:
{
lean_object* v___x_4351_; 
v___x_4351_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_4348_, v_a_4349_);
if (lean_obj_tag(v___x_4351_) == 0)
{
lean_object* v_a_4352_; lean_object* v___x_4354_; uint8_t v_isShared_4355_; uint8_t v_isSharedCheck_4361_; 
v_a_4352_ = lean_ctor_get(v___x_4351_, 0);
v_isSharedCheck_4361_ = !lean_is_exclusive(v___x_4351_);
if (v_isSharedCheck_4361_ == 0)
{
v___x_4354_ = v___x_4351_;
v_isShared_4355_ = v_isSharedCheck_4361_;
goto v_resetjp_4353_;
}
else
{
lean_inc(v_a_4352_);
lean_dec(v___x_4351_);
v___x_4354_ = lean_box(0);
v_isShared_4355_ = v_isSharedCheck_4361_;
goto v_resetjp_4353_;
}
v_resetjp_4353_:
{
lean_object* v_exprToStructId_4356_; lean_object* v___x_4357_; lean_object* v___x_4359_; 
v_exprToStructId_4356_ = lean_ctor_get(v_a_4352_, 2);
lean_inc_ref(v_exprToStructId_4356_);
lean_dec(v_a_4352_);
v___x_4357_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_exprToStructId_4356_, v_e_4347_);
lean_dec_ref(v_exprToStructId_4356_);
if (v_isShared_4355_ == 0)
{
lean_ctor_set(v___x_4354_, 0, v___x_4357_);
v___x_4359_ = v___x_4354_;
goto v_reusejp_4358_;
}
else
{
lean_object* v_reuseFailAlloc_4360_; 
v_reuseFailAlloc_4360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4360_, 0, v___x_4357_);
v___x_4359_ = v_reuseFailAlloc_4360_;
goto v_reusejp_4358_;
}
v_reusejp_4358_:
{
return v___x_4359_;
}
}
}
else
{
lean_object* v_a_4362_; lean_object* v___x_4364_; uint8_t v_isShared_4365_; uint8_t v_isSharedCheck_4369_; 
v_a_4362_ = lean_ctor_get(v___x_4351_, 0);
v_isSharedCheck_4369_ = !lean_is_exclusive(v___x_4351_);
if (v_isSharedCheck_4369_ == 0)
{
v___x_4364_ = v___x_4351_;
v_isShared_4365_ = v_isSharedCheck_4369_;
goto v_resetjp_4363_;
}
else
{
lean_inc(v_a_4362_);
lean_dec(v___x_4351_);
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
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4347_ = stack[0].m_obj;
lean_object* v_a_4348_ = stack[1].m_obj;
lean_object* v_a_4349_ = stack[2].m_obj;
lean_object* v_res_4370_;
v_res_4370_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___redArg(v_e_4347_, v_a_4348_, v_a_4349_);
stack->m_obj
 = v_res_4370_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___redArg___boxed(lean_object* v_e_4371_, lean_object* v_a_4372_, lean_object* v_a_4373_, lean_object* v_a_4374_){
_start:
{
lean_object* v_res_4375_; 
v_res_4375_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___redArg(v_e_4371_, v_a_4372_, v_a_4373_);
lean_dec_ref(v_a_4373_);
lean_dec(v_a_4372_);
lean_dec_ref(v_e_4371_);
return v_res_4375_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f(lean_object* v_e_4376_, lean_object* v_a_4377_, lean_object* v_a_4378_, lean_object* v_a_4379_, lean_object* v_a_4380_, lean_object* v_a_4381_, lean_object* v_a_4382_, lean_object* v_a_4383_, lean_object* v_a_4384_, lean_object* v_a_4385_, lean_object* v_a_4386_){
_start:
{
lean_object* v___x_4388_; 
v___x_4388_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___redArg(v_e_4376_, v_a_4377_, v_a_4385_);
return v___x_4388_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4376_ = stack[0].m_obj;
lean_object* v_a_4377_ = stack[1].m_obj;
lean_object* v_a_4378_ = stack[2].m_obj;
lean_object* v_a_4379_ = stack[3].m_obj;
lean_object* v_a_4380_ = stack[4].m_obj;
lean_object* v_a_4381_ = stack[5].m_obj;
lean_object* v_a_4382_ = stack[6].m_obj;
lean_object* v_a_4383_ = stack[7].m_obj;
lean_object* v_a_4384_ = stack[8].m_obj;
lean_object* v_a_4385_ = stack[9].m_obj;
lean_object* v_a_4386_ = stack[10].m_obj;
lean_object* v_res_4389_;
v_res_4389_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f(v_e_4376_, v_a_4377_, v_a_4378_, v_a_4379_, v_a_4380_, v_a_4381_, v_a_4382_, v_a_4383_, v_a_4384_, v_a_4385_, v_a_4386_);
stack->m_obj
 = v_res_4389_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___boxed(lean_object* v_e_4390_, lean_object* v_a_4391_, lean_object* v_a_4392_, lean_object* v_a_4393_, lean_object* v_a_4394_, lean_object* v_a_4395_, lean_object* v_a_4396_, lean_object* v_a_4397_, lean_object* v_a_4398_, lean_object* v_a_4399_, lean_object* v_a_4400_, lean_object* v_a_4401_){
_start:
{
lean_object* v_res_4402_; 
v_res_4402_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f(v_e_4390_, v_a_4391_, v_a_4392_, v_a_4393_, v_a_4394_, v_a_4395_, v_a_4396_, v_a_4397_, v_a_4398_, v_a_4399_, v_a_4400_);
lean_dec(v_a_4400_);
lean_dec_ref(v_a_4399_);
lean_dec(v_a_4398_);
lean_dec_ref(v_a_4397_);
lean_dec(v_a_4396_);
lean_dec_ref(v_a_4395_);
lean_dec(v_a_4394_);
lean_dec_ref(v_a_4393_);
lean_dec(v_a_4392_);
lean_dec(v_a_4391_);
lean_dec_ref(v_e_4390_);
return v_res_4402_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__2(void){
_start:
{
lean_object* v___x_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; 
v___x_4409_ = lean_box(0);
v___x_4410_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__1));
v___x_4411_ = l_Lean_mkConst(v___x_4410_, v___x_4409_);
return v___x_4411_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__5(void){
_start:
{
lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; 
v___x_4418_ = lean_box(0);
v___x_4419_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__4));
v___x_4420_ = l_Lean_mkConst(v___x_4419_, v___x_4418_);
return v___x_4420_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go(lean_object* v_e_4421_, lean_object* v_e_x27_4422_, lean_object* v_he_x3f_4423_, lean_object* v_a_4424_, lean_object* v_a_4425_, lean_object* v_a_4426_, lean_object* v_a_4427_, lean_object* v_a_4428_, lean_object* v_a_4429_, lean_object* v_a_4430_, lean_object* v_a_4431_, lean_object* v_a_4432_, lean_object* v_a_4433_){
_start:
{
lean_object* v___x_4435_; 
v___x_4435_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___redArg(v_e_x27_4422_, v_a_4424_, v_a_4432_);
if (lean_obj_tag(v___x_4435_) == 0)
{
lean_object* v_a_4436_; lean_object* v___x_4438_; uint8_t v_isShared_4439_; uint8_t v_isSharedCheck_4526_; 
v_a_4436_ = lean_ctor_get(v___x_4435_, 0);
v_isSharedCheck_4526_ = !lean_is_exclusive(v___x_4435_);
if (v_isSharedCheck_4526_ == 0)
{
v___x_4438_ = v___x_4435_;
v_isShared_4439_ = v_isSharedCheck_4526_;
goto v_resetjp_4437_;
}
else
{
lean_inc(v_a_4436_);
lean_dec(v___x_4435_);
v___x_4438_ = lean_box(0);
v_isShared_4439_ = v_isSharedCheck_4526_;
goto v_resetjp_4437_;
}
v_resetjp_4437_:
{
if (lean_obj_tag(v_a_4436_) == 1)
{
lean_object* v_val_4440_; lean_object* v___x_4441_; 
lean_del_object(v___x_4438_);
v_val_4440_ = lean_ctor_get(v_a_4436_, 0);
lean_inc(v_val_4440_);
lean_dec_ref_known(v_a_4436_, 1);
v___x_4441_ = l_Lean_Meta_Grind_Order_getCnstr_x3f___redArg(v_e_x27_4422_, v_val_4440_, v_a_4424_, v_a_4432_);
if (lean_obj_tag(v___x_4441_) == 0)
{
lean_object* v_a_4442_; lean_object* v___x_4444_; uint8_t v_isShared_4445_; uint8_t v_isSharedCheck_4513_; 
v_a_4442_ = lean_ctor_get(v___x_4441_, 0);
v_isSharedCheck_4513_ = !lean_is_exclusive(v___x_4441_);
if (v_isSharedCheck_4513_ == 0)
{
v___x_4444_ = v___x_4441_;
v_isShared_4445_ = v_isSharedCheck_4513_;
goto v_resetjp_4443_;
}
else
{
lean_inc(v_a_4442_);
lean_dec(v___x_4441_);
v___x_4444_ = lean_box(0);
v_isShared_4445_ = v_isSharedCheck_4513_;
goto v_resetjp_4443_;
}
v_resetjp_4443_:
{
if (lean_obj_tag(v_a_4442_) == 1)
{
lean_object* v_val_4446_; lean_object* v___x_4447_; 
lean_del_object(v___x_4444_);
v_val_4446_ = lean_ctor_get(v_a_4442_, 0);
lean_inc(v_val_4446_);
lean_dec_ref_known(v_a_4442_, 1);
lean_inc_ref(v_e_4421_);
v___x_4447_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_4421_, v_a_4424_, v_a_4428_, v_a_4430_, v_a_4431_, v_a_4432_, v_a_4433_);
if (lean_obj_tag(v___x_4447_) == 0)
{
lean_object* v_a_4448_; uint8_t v___x_4449_; 
v_a_4448_ = lean_ctor_get(v___x_4447_, 0);
lean_inc(v_a_4448_);
lean_dec_ref_known(v___x_4447_, 1);
v___x_4449_ = lean_unbox(v_a_4448_);
lean_dec(v_a_4448_);
if (v___x_4449_ == 0)
{
lean_object* v___x_4450_; 
lean_inc_ref(v_e_4421_);
v___x_4450_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_4421_, v_a_4424_, v_a_4428_, v_a_4430_, v_a_4431_, v_a_4432_, v_a_4433_);
if (lean_obj_tag(v___x_4450_) == 0)
{
lean_object* v_a_4451_; lean_object* v___x_4453_; uint8_t v_isShared_4454_; uint8_t v_isSharedCheck_4476_; 
v_a_4451_ = lean_ctor_get(v___x_4450_, 0);
v_isSharedCheck_4476_ = !lean_is_exclusive(v___x_4450_);
if (v_isSharedCheck_4476_ == 0)
{
v___x_4453_ = v___x_4450_;
v_isShared_4454_ = v_isSharedCheck_4476_;
goto v_resetjp_4452_;
}
else
{
lean_inc(v_a_4451_);
lean_dec(v___x_4450_);
v___x_4453_ = lean_box(0);
v_isShared_4454_ = v_isSharedCheck_4476_;
goto v_resetjp_4452_;
}
v_resetjp_4452_:
{
uint8_t v___x_4455_; 
v___x_4455_ = lean_unbox(v_a_4451_);
lean_dec(v_a_4451_);
if (v___x_4455_ == 0)
{
lean_object* v___x_4456_; lean_object* v___x_4458_; 
lean_dec(v_val_4446_);
lean_dec(v_val_4440_);
lean_dec(v_he_x3f_4423_);
lean_dec_ref(v_e_x27_4422_);
lean_dec_ref(v_e_4421_);
v___x_4456_ = lean_box(0);
if (v_isShared_4454_ == 0)
{
lean_ctor_set(v___x_4453_, 0, v___x_4456_);
v___x_4458_ = v___x_4453_;
goto v_reusejp_4457_;
}
else
{
lean_object* v_reuseFailAlloc_4459_; 
v_reuseFailAlloc_4459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4459_, 0, v___x_4456_);
v___x_4458_ = v_reuseFailAlloc_4459_;
goto v_reusejp_4457_;
}
v_reusejp_4457_:
{
return v___x_4458_;
}
}
else
{
lean_object* v___x_4460_; 
lean_del_object(v___x_4453_);
lean_inc_ref(v_e_4421_);
v___x_4460_ = l_Lean_Meta_Grind_mkEqFalseProof(v_e_4421_, v_a_4424_, v_a_4425_, v_a_4426_, v_a_4427_, v_a_4428_, v_a_4429_, v_a_4430_, v_a_4431_, v_a_4432_, v_a_4433_);
if (lean_obj_tag(v___x_4460_) == 0)
{
if (lean_obj_tag(v_he_x3f_4423_) == 1)
{
lean_object* v_a_4461_; lean_object* v_val_4462_; lean_object* v___x_4463_; lean_object* v___x_4464_; lean_object* v___x_4465_; 
v_a_4461_ = lean_ctor_get(v___x_4460_, 0);
lean_inc(v_a_4461_);
lean_dec_ref_known(v___x_4460_, 1);
v_val_4462_ = lean_ctor_get(v_he_x3f_4423_, 0);
lean_inc(v_val_4462_);
lean_dec_ref_known(v_he_x3f_4423_, 1);
v___x_4463_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__2, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__2);
lean_inc_ref(v_e_x27_4422_);
v___x_4464_ = l_Lean_mkApp4(v___x_4463_, v_e_4421_, v_e_x27_4422_, v_val_4462_, v_a_4461_);
v___x_4465_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse(v_val_4446_, v_e_x27_4422_, v___x_4464_, v_val_4440_, v_a_4424_, v_a_4425_, v_a_4426_, v_a_4427_, v_a_4428_, v_a_4429_, v_a_4430_, v_a_4431_, v_a_4432_, v_a_4433_);
lean_dec(v_val_4440_);
return v___x_4465_;
}
else
{
lean_object* v_a_4466_; lean_object* v___x_4467_; 
lean_dec(v_he_x3f_4423_);
lean_dec_ref(v_e_4421_);
v_a_4466_ = lean_ctor_get(v___x_4460_, 0);
lean_inc(v_a_4466_);
lean_dec_ref_known(v___x_4460_, 1);
v___x_4467_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse(v_val_4446_, v_e_x27_4422_, v_a_4466_, v_val_4440_, v_a_4424_, v_a_4425_, v_a_4426_, v_a_4427_, v_a_4428_, v_a_4429_, v_a_4430_, v_a_4431_, v_a_4432_, v_a_4433_);
lean_dec(v_val_4440_);
return v___x_4467_;
}
}
else
{
lean_object* v_a_4468_; lean_object* v___x_4470_; uint8_t v_isShared_4471_; uint8_t v_isSharedCheck_4475_; 
lean_dec(v_val_4446_);
lean_dec(v_val_4440_);
lean_dec(v_he_x3f_4423_);
lean_dec_ref(v_e_x27_4422_);
lean_dec_ref(v_e_4421_);
v_a_4468_ = lean_ctor_get(v___x_4460_, 0);
v_isSharedCheck_4475_ = !lean_is_exclusive(v___x_4460_);
if (v_isSharedCheck_4475_ == 0)
{
v___x_4470_ = v___x_4460_;
v_isShared_4471_ = v_isSharedCheck_4475_;
goto v_resetjp_4469_;
}
else
{
lean_inc(v_a_4468_);
lean_dec(v___x_4460_);
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
}
}
else
{
lean_object* v_a_4477_; lean_object* v___x_4479_; uint8_t v_isShared_4480_; uint8_t v_isSharedCheck_4484_; 
lean_dec(v_val_4446_);
lean_dec(v_val_4440_);
lean_dec(v_he_x3f_4423_);
lean_dec_ref(v_e_x27_4422_);
lean_dec_ref(v_e_4421_);
v_a_4477_ = lean_ctor_get(v___x_4450_, 0);
v_isSharedCheck_4484_ = !lean_is_exclusive(v___x_4450_);
if (v_isSharedCheck_4484_ == 0)
{
v___x_4479_ = v___x_4450_;
v_isShared_4480_ = v_isSharedCheck_4484_;
goto v_resetjp_4478_;
}
else
{
lean_inc(v_a_4477_);
lean_dec(v___x_4450_);
v___x_4479_ = lean_box(0);
v_isShared_4480_ = v_isSharedCheck_4484_;
goto v_resetjp_4478_;
}
v_resetjp_4478_:
{
lean_object* v___x_4482_; 
if (v_isShared_4480_ == 0)
{
v___x_4482_ = v___x_4479_;
goto v_reusejp_4481_;
}
else
{
lean_object* v_reuseFailAlloc_4483_; 
v_reuseFailAlloc_4483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4483_, 0, v_a_4477_);
v___x_4482_ = v_reuseFailAlloc_4483_;
goto v_reusejp_4481_;
}
v_reusejp_4481_:
{
return v___x_4482_;
}
}
}
}
else
{
lean_object* v___x_4485_; 
lean_inc_ref(v_e_4421_);
v___x_4485_ = l_Lean_Meta_Grind_mkEqTrueProof(v_e_4421_, v_a_4424_, v_a_4425_, v_a_4426_, v_a_4427_, v_a_4428_, v_a_4429_, v_a_4430_, v_a_4431_, v_a_4432_, v_a_4433_);
if (lean_obj_tag(v___x_4485_) == 0)
{
if (lean_obj_tag(v_he_x3f_4423_) == 1)
{
lean_object* v_a_4486_; lean_object* v_val_4487_; lean_object* v___x_4488_; lean_object* v___x_4489_; lean_object* v___x_4490_; 
v_a_4486_ = lean_ctor_get(v___x_4485_, 0);
lean_inc(v_a_4486_);
lean_dec_ref_known(v___x_4485_, 1);
v_val_4487_ = lean_ctor_get(v_he_x3f_4423_, 0);
lean_inc(v_val_4487_);
lean_dec_ref_known(v_he_x3f_4423_, 1);
v___x_4488_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__5);
lean_inc_ref(v_e_x27_4422_);
v___x_4489_ = l_Lean_mkApp4(v___x_4488_, v_e_4421_, v_e_x27_4422_, v_val_4487_, v_a_4486_);
v___x_4490_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue(v_val_4446_, v_e_x27_4422_, v___x_4489_, v_val_4440_, v_a_4424_, v_a_4425_, v_a_4426_, v_a_4427_, v_a_4428_, v_a_4429_, v_a_4430_, v_a_4431_, v_a_4432_, v_a_4433_);
lean_dec(v_val_4440_);
return v___x_4490_;
}
else
{
lean_object* v_a_4491_; lean_object* v___x_4492_; 
lean_dec(v_he_x3f_4423_);
lean_dec_ref(v_e_4421_);
v_a_4491_ = lean_ctor_get(v___x_4485_, 0);
lean_inc(v_a_4491_);
lean_dec_ref_known(v___x_4485_, 1);
v___x_4492_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue(v_val_4446_, v_e_x27_4422_, v_a_4491_, v_val_4440_, v_a_4424_, v_a_4425_, v_a_4426_, v_a_4427_, v_a_4428_, v_a_4429_, v_a_4430_, v_a_4431_, v_a_4432_, v_a_4433_);
lean_dec(v_val_4440_);
return v___x_4492_;
}
}
else
{
lean_object* v_a_4493_; lean_object* v___x_4495_; uint8_t v_isShared_4496_; uint8_t v_isSharedCheck_4500_; 
lean_dec(v_val_4446_);
lean_dec(v_val_4440_);
lean_dec(v_he_x3f_4423_);
lean_dec_ref(v_e_x27_4422_);
lean_dec_ref(v_e_4421_);
v_a_4493_ = lean_ctor_get(v___x_4485_, 0);
v_isSharedCheck_4500_ = !lean_is_exclusive(v___x_4485_);
if (v_isSharedCheck_4500_ == 0)
{
v___x_4495_ = v___x_4485_;
v_isShared_4496_ = v_isSharedCheck_4500_;
goto v_resetjp_4494_;
}
else
{
lean_inc(v_a_4493_);
lean_dec(v___x_4485_);
v___x_4495_ = lean_box(0);
v_isShared_4496_ = v_isSharedCheck_4500_;
goto v_resetjp_4494_;
}
v_resetjp_4494_:
{
lean_object* v___x_4498_; 
if (v_isShared_4496_ == 0)
{
v___x_4498_ = v___x_4495_;
goto v_reusejp_4497_;
}
else
{
lean_object* v_reuseFailAlloc_4499_; 
v_reuseFailAlloc_4499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4499_, 0, v_a_4493_);
v___x_4498_ = v_reuseFailAlloc_4499_;
goto v_reusejp_4497_;
}
v_reusejp_4497_:
{
return v___x_4498_;
}
}
}
}
}
else
{
lean_object* v_a_4501_; lean_object* v___x_4503_; uint8_t v_isShared_4504_; uint8_t v_isSharedCheck_4508_; 
lean_dec(v_val_4446_);
lean_dec(v_val_4440_);
lean_dec(v_he_x3f_4423_);
lean_dec_ref(v_e_x27_4422_);
lean_dec_ref(v_e_4421_);
v_a_4501_ = lean_ctor_get(v___x_4447_, 0);
v_isSharedCheck_4508_ = !lean_is_exclusive(v___x_4447_);
if (v_isSharedCheck_4508_ == 0)
{
v___x_4503_ = v___x_4447_;
v_isShared_4504_ = v_isSharedCheck_4508_;
goto v_resetjp_4502_;
}
else
{
lean_inc(v_a_4501_);
lean_dec(v___x_4447_);
v___x_4503_ = lean_box(0);
v_isShared_4504_ = v_isSharedCheck_4508_;
goto v_resetjp_4502_;
}
v_resetjp_4502_:
{
lean_object* v___x_4506_; 
if (v_isShared_4504_ == 0)
{
v___x_4506_ = v___x_4503_;
goto v_reusejp_4505_;
}
else
{
lean_object* v_reuseFailAlloc_4507_; 
v_reuseFailAlloc_4507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4507_, 0, v_a_4501_);
v___x_4506_ = v_reuseFailAlloc_4507_;
goto v_reusejp_4505_;
}
v_reusejp_4505_:
{
return v___x_4506_;
}
}
}
}
else
{
lean_object* v___x_4509_; lean_object* v___x_4511_; 
lean_dec(v_a_4442_);
lean_dec(v_val_4440_);
lean_dec(v_he_x3f_4423_);
lean_dec_ref(v_e_x27_4422_);
lean_dec_ref(v_e_4421_);
v___x_4509_ = lean_box(0);
if (v_isShared_4445_ == 0)
{
lean_ctor_set(v___x_4444_, 0, v___x_4509_);
v___x_4511_ = v___x_4444_;
goto v_reusejp_4510_;
}
else
{
lean_object* v_reuseFailAlloc_4512_; 
v_reuseFailAlloc_4512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4512_, 0, v___x_4509_);
v___x_4511_ = v_reuseFailAlloc_4512_;
goto v_reusejp_4510_;
}
v_reusejp_4510_:
{
return v___x_4511_;
}
}
}
}
else
{
lean_object* v_a_4514_; lean_object* v___x_4516_; uint8_t v_isShared_4517_; uint8_t v_isSharedCheck_4521_; 
lean_dec(v_val_4440_);
lean_dec(v_he_x3f_4423_);
lean_dec_ref(v_e_x27_4422_);
lean_dec_ref(v_e_4421_);
v_a_4514_ = lean_ctor_get(v___x_4441_, 0);
v_isSharedCheck_4521_ = !lean_is_exclusive(v___x_4441_);
if (v_isSharedCheck_4521_ == 0)
{
v___x_4516_ = v___x_4441_;
v_isShared_4517_ = v_isSharedCheck_4521_;
goto v_resetjp_4515_;
}
else
{
lean_inc(v_a_4514_);
lean_dec(v___x_4441_);
v___x_4516_ = lean_box(0);
v_isShared_4517_ = v_isSharedCheck_4521_;
goto v_resetjp_4515_;
}
v_resetjp_4515_:
{
lean_object* v___x_4519_; 
if (v_isShared_4517_ == 0)
{
v___x_4519_ = v___x_4516_;
goto v_reusejp_4518_;
}
else
{
lean_object* v_reuseFailAlloc_4520_; 
v_reuseFailAlloc_4520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4520_, 0, v_a_4514_);
v___x_4519_ = v_reuseFailAlloc_4520_;
goto v_reusejp_4518_;
}
v_reusejp_4518_:
{
return v___x_4519_;
}
}
}
}
else
{
lean_object* v___x_4522_; lean_object* v___x_4524_; 
lean_dec(v_a_4436_);
lean_dec(v_he_x3f_4423_);
lean_dec_ref(v_e_x27_4422_);
lean_dec_ref(v_e_4421_);
v___x_4522_ = lean_box(0);
if (v_isShared_4439_ == 0)
{
lean_ctor_set(v___x_4438_, 0, v___x_4522_);
v___x_4524_ = v___x_4438_;
goto v_reusejp_4523_;
}
else
{
lean_object* v_reuseFailAlloc_4525_; 
v_reuseFailAlloc_4525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4525_, 0, v___x_4522_);
v___x_4524_ = v_reuseFailAlloc_4525_;
goto v_reusejp_4523_;
}
v_reusejp_4523_:
{
return v___x_4524_;
}
}
}
}
else
{
lean_object* v_a_4527_; lean_object* v___x_4529_; uint8_t v_isShared_4530_; uint8_t v_isSharedCheck_4534_; 
lean_dec(v_he_x3f_4423_);
lean_dec_ref(v_e_x27_4422_);
lean_dec_ref(v_e_4421_);
v_a_4527_ = lean_ctor_get(v___x_4435_, 0);
v_isSharedCheck_4534_ = !lean_is_exclusive(v___x_4435_);
if (v_isSharedCheck_4534_ == 0)
{
v___x_4529_ = v___x_4435_;
v_isShared_4530_ = v_isSharedCheck_4534_;
goto v_resetjp_4528_;
}
else
{
lean_inc(v_a_4527_);
lean_dec(v___x_4435_);
v___x_4529_ = lean_box(0);
v_isShared_4530_ = v_isSharedCheck_4534_;
goto v_resetjp_4528_;
}
v_resetjp_4528_:
{
lean_object* v___x_4532_; 
if (v_isShared_4530_ == 0)
{
v___x_4532_ = v___x_4529_;
goto v_reusejp_4531_;
}
else
{
lean_object* v_reuseFailAlloc_4533_; 
v_reuseFailAlloc_4533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4533_, 0, v_a_4527_);
v___x_4532_ = v_reuseFailAlloc_4533_;
goto v_reusejp_4531_;
}
v_reusejp_4531_:
{
return v___x_4532_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4421_ = stack[0].m_obj;
lean_object* v_e_x27_4422_ = stack[1].m_obj;
lean_object* v_he_x3f_4423_ = stack[2].m_obj;
lean_object* v_a_4424_ = stack[3].m_obj;
lean_object* v_a_4425_ = stack[4].m_obj;
lean_object* v_a_4426_ = stack[5].m_obj;
lean_object* v_a_4427_ = stack[6].m_obj;
lean_object* v_a_4428_ = stack[7].m_obj;
lean_object* v_a_4429_ = stack[8].m_obj;
lean_object* v_a_4430_ = stack[9].m_obj;
lean_object* v_a_4431_ = stack[10].m_obj;
lean_object* v_a_4432_ = stack[11].m_obj;
lean_object* v_a_4433_ = stack[12].m_obj;
lean_object* v_res_4535_;
v_res_4535_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go(v_e_4421_, v_e_x27_4422_, v_he_x3f_4423_, v_a_4424_, v_a_4425_, v_a_4426_, v_a_4427_, v_a_4428_, v_a_4429_, v_a_4430_, v_a_4431_, v_a_4432_, v_a_4433_);
stack->m_obj
 = v_res_4535_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___boxed(lean_object* v_e_4536_, lean_object* v_e_x27_4537_, lean_object* v_he_x3f_4538_, lean_object* v_a_4539_, lean_object* v_a_4540_, lean_object* v_a_4541_, lean_object* v_a_4542_, lean_object* v_a_4543_, lean_object* v_a_4544_, lean_object* v_a_4545_, lean_object* v_a_4546_, lean_object* v_a_4547_, lean_object* v_a_4548_, lean_object* v_a_4549_){
_start:
{
lean_object* v_res_4550_; 
v_res_4550_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go(v_e_4536_, v_e_x27_4537_, v_he_x3f_4538_, v_a_4539_, v_a_4540_, v_a_4541_, v_a_4542_, v_a_4543_, v_a_4544_, v_a_4545_, v_a_4546_, v_a_4547_, v_a_4548_);
lean_dec(v_a_4548_);
lean_dec_ref(v_a_4547_);
lean_dec(v_a_4546_);
lean_dec_ref(v_a_4545_);
lean_dec(v_a_4544_);
lean_dec_ref(v_a_4543_);
lean_dec(v_a_4542_);
lean_dec_ref(v_a_4541_);
lean_dec(v_a_4540_);
lean_dec(v_a_4539_);
return v_res_4550_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq(lean_object* v_e_4551_, lean_object* v_a_4552_, lean_object* v_a_4553_, lean_object* v_a_4554_, lean_object* v_a_4555_, lean_object* v_a_4556_, lean_object* v_a_4557_, lean_object* v_a_4558_, lean_object* v_a_4559_, lean_object* v_a_4560_, lean_object* v_a_4561_){
_start:
{
lean_object* v___x_4563_; 
v___x_4563_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_4552_, v_a_4560_);
if (lean_obj_tag(v___x_4563_) == 0)
{
lean_object* v_a_4564_; lean_object* v_termMap_4565_; lean_object* v___x_4566_; 
v_a_4564_ = lean_ctor_get(v___x_4563_, 0);
lean_inc(v_a_4564_);
lean_dec_ref_known(v___x_4563_, 1);
v_termMap_4565_ = lean_ctor_get(v_a_4564_, 3);
lean_inc_ref(v_termMap_4565_);
lean_dec(v_a_4564_);
v___x_4566_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMap_4565_, v_e_4551_);
lean_dec_ref(v_termMap_4565_);
if (lean_obj_tag(v___x_4566_) == 1)
{
lean_object* v_val_4567_; lean_object* v___x_4569_; uint8_t v_isShared_4570_; uint8_t v_isSharedCheck_4577_; 
v_val_4567_ = lean_ctor_get(v___x_4566_, 0);
v_isSharedCheck_4577_ = !lean_is_exclusive(v___x_4566_);
if (v_isSharedCheck_4577_ == 0)
{
v___x_4569_ = v___x_4566_;
v_isShared_4570_ = v_isSharedCheck_4577_;
goto v_resetjp_4568_;
}
else
{
lean_inc(v_val_4567_);
lean_dec(v___x_4566_);
v___x_4569_ = lean_box(0);
v_isShared_4570_ = v_isSharedCheck_4577_;
goto v_resetjp_4568_;
}
v_resetjp_4568_:
{
lean_object* v_e_4571_; lean_object* v_h_4572_; lean_object* v___x_4574_; 
v_e_4571_ = lean_ctor_get(v_val_4567_, 0);
lean_inc_ref(v_e_4571_);
v_h_4572_ = lean_ctor_get(v_val_4567_, 1);
lean_inc_ref(v_h_4572_);
lean_dec(v_val_4567_);
if (v_isShared_4570_ == 0)
{
lean_ctor_set(v___x_4569_, 0, v_h_4572_);
v___x_4574_ = v___x_4569_;
goto v_reusejp_4573_;
}
else
{
lean_object* v_reuseFailAlloc_4576_; 
v_reuseFailAlloc_4576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4576_, 0, v_h_4572_);
v___x_4574_ = v_reuseFailAlloc_4576_;
goto v_reusejp_4573_;
}
v_reusejp_4573_:
{
lean_object* v___x_4575_; 
v___x_4575_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go(v_e_4551_, v_e_4571_, v___x_4574_, v_a_4552_, v_a_4553_, v_a_4554_, v_a_4555_, v_a_4556_, v_a_4557_, v_a_4558_, v_a_4559_, v_a_4560_, v_a_4561_);
return v___x_4575_;
}
}
}
else
{
lean_object* v___x_4578_; lean_object* v___x_4579_; 
lean_dec(v___x_4566_);
v___x_4578_ = lean_box(0);
lean_inc_ref(v_e_4551_);
v___x_4579_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go(v_e_4551_, v_e_4551_, v___x_4578_, v_a_4552_, v_a_4553_, v_a_4554_, v_a_4555_, v_a_4556_, v_a_4557_, v_a_4558_, v_a_4559_, v_a_4560_, v_a_4561_);
return v___x_4579_;
}
}
else
{
lean_object* v_a_4580_; lean_object* v___x_4582_; uint8_t v_isShared_4583_; uint8_t v_isSharedCheck_4587_; 
lean_dec_ref(v_e_4551_);
v_a_4580_ = lean_ctor_get(v___x_4563_, 0);
v_isSharedCheck_4587_ = !lean_is_exclusive(v___x_4563_);
if (v_isSharedCheck_4587_ == 0)
{
v___x_4582_ = v___x_4563_;
v_isShared_4583_ = v_isSharedCheck_4587_;
goto v_resetjp_4581_;
}
else
{
lean_inc(v_a_4580_);
lean_dec(v___x_4563_);
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
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4551_ = stack[0].m_obj;
lean_object* v_a_4552_ = stack[1].m_obj;
lean_object* v_a_4553_ = stack[2].m_obj;
lean_object* v_a_4554_ = stack[3].m_obj;
lean_object* v_a_4555_ = stack[4].m_obj;
lean_object* v_a_4556_ = stack[5].m_obj;
lean_object* v_a_4557_ = stack[6].m_obj;
lean_object* v_a_4558_ = stack[7].m_obj;
lean_object* v_a_4559_ = stack[8].m_obj;
lean_object* v_a_4560_ = stack[9].m_obj;
lean_object* v_a_4561_ = stack[10].m_obj;
lean_object* v_res_4588_;
v_res_4588_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq(v_e_4551_, v_a_4552_, v_a_4553_, v_a_4554_, v_a_4555_, v_a_4556_, v_a_4557_, v_a_4558_, v_a_4559_, v_a_4560_, v_a_4561_);
stack->m_obj
 = v_res_4588_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq___boxed(lean_object* v_e_4589_, lean_object* v_a_4590_, lean_object* v_a_4591_, lean_object* v_a_4592_, lean_object* v_a_4593_, lean_object* v_a_4594_, lean_object* v_a_4595_, lean_object* v_a_4596_, lean_object* v_a_4597_, lean_object* v_a_4598_, lean_object* v_a_4599_, lean_object* v_a_4600_){
_start:
{
lean_object* v_res_4601_; 
v_res_4601_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq(v_e_4589_, v_a_4590_, v_a_4591_, v_a_4592_, v_a_4593_, v_a_4594_, v_a_4595_, v_a_4596_, v_a_4597_, v_a_4598_, v_a_4599_);
lean_dec(v_a_4599_);
lean_dec_ref(v_a_4598_);
lean_dec(v_a_4597_);
lean_dec_ref(v_a_4596_);
lean_dec(v_a_4595_);
lean_dec_ref(v_a_4594_);
lean_dec(v_a_4593_);
lean_dec_ref(v_a_4592_);
lean_dec(v_a_4591_);
lean_dec(v_a_4590_);
return v_res_4601_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE(lean_object* v_e_4602_, lean_object* v_a_4603_, lean_object* v_a_4604_, lean_object* v_a_4605_, lean_object* v_a_4606_, lean_object* v_a_4607_, lean_object* v_a_4608_, lean_object* v_a_4609_, lean_object* v_a_4610_, lean_object* v_a_4611_, lean_object* v_a_4612_){
_start:
{
lean_object* v___x_4614_; 
v___x_4614_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq(v_e_4602_, v_a_4603_, v_a_4604_, v_a_4605_, v_a_4606_, v_a_4607_, v_a_4608_, v_a_4609_, v_a_4610_, v_a_4611_, v_a_4612_);
return v___x_4614_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4602_ = stack[0].m_obj;
lean_object* v_a_4603_ = stack[1].m_obj;
lean_object* v_a_4604_ = stack[2].m_obj;
lean_object* v_a_4605_ = stack[3].m_obj;
lean_object* v_a_4606_ = stack[4].m_obj;
lean_object* v_a_4607_ = stack[5].m_obj;
lean_object* v_a_4608_ = stack[6].m_obj;
lean_object* v_a_4609_ = stack[7].m_obj;
lean_object* v_a_4610_ = stack[8].m_obj;
lean_object* v_a_4611_ = stack[9].m_obj;
lean_object* v_a_4612_ = stack[10].m_obj;
lean_object* v_res_4615_;
v_res_4615_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE(v_e_4602_, v_a_4603_, v_a_4604_, v_a_4605_, v_a_4606_, v_a_4607_, v_a_4608_, v_a_4609_, v_a_4610_, v_a_4611_, v_a_4612_);
stack->m_obj
 = v_res_4615_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___boxed(lean_object* v_e_4616_, lean_object* v_a_4617_, lean_object* v_a_4618_, lean_object* v_a_4619_, lean_object* v_a_4620_, lean_object* v_a_4621_, lean_object* v_a_4622_, lean_object* v_a_4623_, lean_object* v_a_4624_, lean_object* v_a_4625_, lean_object* v_a_4626_, lean_object* v_a_4627_){
_start:
{
lean_object* v_res_4628_; 
v_res_4628_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE(v_e_4616_, v_a_4617_, v_a_4618_, v_a_4619_, v_a_4620_, v_a_4621_, v_a_4622_, v_a_4623_, v_a_4624_, v_a_4625_, v_a_4626_);
lean_dec(v_a_4626_);
lean_dec_ref(v_a_4625_);
lean_dec(v_a_4624_);
lean_dec_ref(v_a_4623_);
lean_dec(v_a_4622_);
lean_dec_ref(v_a_4621_);
lean_dec(v_a_4620_);
lean_dec_ref(v_a_4619_);
lean_dec(v_a_4618_);
lean_dec(v_a_4617_);
return v_res_4628_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_9_(){
_start:
{
lean_object* v___f_4636_; lean_object* v___x_4637_; lean_object* v___x_4638_; 
v___f_4636_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_9_));
v___x_4637_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_9_));
v___x_4638_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_4637_, v___f_4636_);
return v___x_4638_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_9__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4639_;
v_res_4639_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_9_();
stack->m_obj
 = v_res_4639_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_9____boxed(lean_object* v_a_4640_){
_start:
{
lean_object* v_res_4641_; 
v_res_4641_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_9_();
return v_res_4641_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT(lean_object* v_e_4642_, lean_object* v_a_4643_, lean_object* v_a_4644_, lean_object* v_a_4645_, lean_object* v_a_4646_, lean_object* v_a_4647_, lean_object* v_a_4648_, lean_object* v_a_4649_, lean_object* v_a_4650_, lean_object* v_a_4651_, lean_object* v_a_4652_){
_start:
{
lean_object* v___x_4654_; 
v___x_4654_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq(v_e_4642_, v_a_4643_, v_a_4644_, v_a_4645_, v_a_4646_, v_a_4647_, v_a_4648_, v_a_4649_, v_a_4650_, v_a_4651_, v_a_4652_);
return v___x_4654_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4642_ = stack[0].m_obj;
lean_object* v_a_4643_ = stack[1].m_obj;
lean_object* v_a_4644_ = stack[2].m_obj;
lean_object* v_a_4645_ = stack[3].m_obj;
lean_object* v_a_4646_ = stack[4].m_obj;
lean_object* v_a_4647_ = stack[5].m_obj;
lean_object* v_a_4648_ = stack[6].m_obj;
lean_object* v_a_4649_ = stack[7].m_obj;
lean_object* v_a_4650_ = stack[8].m_obj;
lean_object* v_a_4651_ = stack[9].m_obj;
lean_object* v_a_4652_ = stack[10].m_obj;
lean_object* v_res_4655_;
v_res_4655_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT(v_e_4642_, v_a_4643_, v_a_4644_, v_a_4645_, v_a_4646_, v_a_4647_, v_a_4648_, v_a_4649_, v_a_4650_, v_a_4651_, v_a_4652_);
stack->m_obj
 = v_res_4655_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___boxed(lean_object* v_e_4656_, lean_object* v_a_4657_, lean_object* v_a_4658_, lean_object* v_a_4659_, lean_object* v_a_4660_, lean_object* v_a_4661_, lean_object* v_a_4662_, lean_object* v_a_4663_, lean_object* v_a_4664_, lean_object* v_a_4665_, lean_object* v_a_4666_, lean_object* v_a_4667_){
_start:
{
lean_object* v_res_4668_; 
v_res_4668_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT(v_e_4656_, v_a_4657_, v_a_4658_, v_a_4659_, v_a_4660_, v_a_4661_, v_a_4662_, v_a_4663_, v_a_4664_, v_a_4665_, v_a_4666_);
lean_dec(v_a_4666_);
lean_dec_ref(v_a_4665_);
lean_dec(v_a_4664_);
lean_dec_ref(v_a_4663_);
lean_dec(v_a_4662_);
lean_dec_ref(v_a_4661_);
lean_dec(v_a_4660_);
lean_dec_ref(v_a_4659_);
lean_dec(v_a_4658_);
lean_dec(v_a_4657_);
return v_res_4668_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_1204040634____hygCtx___hyg_9_(){
_start:
{
lean_object* v___f_4675_; lean_object* v___x_4676_; lean_object* v___x_4677_; 
v___f_4675_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_9_));
v___x_4676_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_1204040634____hygCtx___hyg_9_));
v___x_4677_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_4676_, v___f_4675_);
return v___x_4677_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_1204040634____hygCtx___hyg_9__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4678_;
v_res_4678_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_1204040634____hygCtx___hyg_9_();
stack->m_obj
 = v_res_4678_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_1204040634____hygCtx___hyg_9____boxed(lean_object* v_a_4679_){
_start:
{
lean_object* v_res_4680_; 
v_res_4680_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_1204040634____hygCtx___hyg_9_();
return v_res_4680_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f___redArg(lean_object* v_e_4681_, lean_object* v_a_4682_, lean_object* v_a_4683_){
_start:
{
lean_object* v___x_4685_; 
v___x_4685_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_4682_, v_a_4683_);
if (lean_obj_tag(v___x_4685_) == 0)
{
lean_object* v_a_4686_; lean_object* v___x_4688_; uint8_t v_isShared_4689_; uint8_t v_isSharedCheck_4695_; 
v_a_4686_ = lean_ctor_get(v___x_4685_, 0);
v_isSharedCheck_4695_ = !lean_is_exclusive(v___x_4685_);
if (v_isSharedCheck_4695_ == 0)
{
v___x_4688_ = v___x_4685_;
v_isShared_4689_ = v_isSharedCheck_4695_;
goto v_resetjp_4687_;
}
else
{
lean_inc(v_a_4686_);
lean_dec(v___x_4685_);
v___x_4688_ = lean_box(0);
v_isShared_4689_ = v_isSharedCheck_4695_;
goto v_resetjp_4687_;
}
v_resetjp_4687_:
{
lean_object* v_termMap_4690_; lean_object* v___x_4691_; lean_object* v___x_4693_; 
v_termMap_4690_ = lean_ctor_get(v_a_4686_, 3);
lean_inc_ref(v_termMap_4690_);
lean_dec(v_a_4686_);
v___x_4691_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMap_4690_, v_e_4681_);
lean_dec_ref(v_termMap_4690_);
if (v_isShared_4689_ == 0)
{
lean_ctor_set(v___x_4688_, 0, v___x_4691_);
v___x_4693_ = v___x_4688_;
goto v_reusejp_4692_;
}
else
{
lean_object* v_reuseFailAlloc_4694_; 
v_reuseFailAlloc_4694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4694_, 0, v___x_4691_);
v___x_4693_ = v_reuseFailAlloc_4694_;
goto v_reusejp_4692_;
}
v_reusejp_4692_:
{
return v___x_4693_;
}
}
}
else
{
lean_object* v_a_4696_; lean_object* v___x_4698_; uint8_t v_isShared_4699_; uint8_t v_isSharedCheck_4703_; 
v_a_4696_ = lean_ctor_get(v___x_4685_, 0);
v_isSharedCheck_4703_ = !lean_is_exclusive(v___x_4685_);
if (v_isSharedCheck_4703_ == 0)
{
v___x_4698_ = v___x_4685_;
v_isShared_4699_ = v_isSharedCheck_4703_;
goto v_resetjp_4697_;
}
else
{
lean_inc(v_a_4696_);
lean_dec(v___x_4685_);
v___x_4698_ = lean_box(0);
v_isShared_4699_ = v_isSharedCheck_4703_;
goto v_resetjp_4697_;
}
v_resetjp_4697_:
{
lean_object* v___x_4701_; 
if (v_isShared_4699_ == 0)
{
v___x_4701_ = v___x_4698_;
goto v_reusejp_4700_;
}
else
{
lean_object* v_reuseFailAlloc_4702_; 
v_reuseFailAlloc_4702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4702_, 0, v_a_4696_);
v___x_4701_ = v_reuseFailAlloc_4702_;
goto v_reusejp_4700_;
}
v_reusejp_4700_:
{
return v___x_4701_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4681_ = stack[0].m_obj;
lean_object* v_a_4682_ = stack[1].m_obj;
lean_object* v_a_4683_ = stack[2].m_obj;
lean_object* v_res_4704_;
v_res_4704_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f___redArg(v_e_4681_, v_a_4682_, v_a_4683_);
stack->m_obj
 = v_res_4704_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f___redArg___boxed(lean_object* v_e_4705_, lean_object* v_a_4706_, lean_object* v_a_4707_, lean_object* v_a_4708_){
_start:
{
lean_object* v_res_4709_; 
v_res_4709_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f___redArg(v_e_4705_, v_a_4706_, v_a_4707_);
lean_dec_ref(v_a_4707_);
lean_dec(v_a_4706_);
lean_dec_ref(v_e_4705_);
return v_res_4709_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f(lean_object* v_e_4710_, lean_object* v_a_4711_, lean_object* v_a_4712_, lean_object* v_a_4713_, lean_object* v_a_4714_, lean_object* v_a_4715_, lean_object* v_a_4716_, lean_object* v_a_4717_, lean_object* v_a_4718_, lean_object* v_a_4719_, lean_object* v_a_4720_){
_start:
{
lean_object* v___x_4722_; 
v___x_4722_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f___redArg(v_e_4710_, v_a_4711_, v_a_4719_);
return v___x_4722_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4710_ = stack[0].m_obj;
lean_object* v_a_4711_ = stack[1].m_obj;
lean_object* v_a_4712_ = stack[2].m_obj;
lean_object* v_a_4713_ = stack[3].m_obj;
lean_object* v_a_4714_ = stack[4].m_obj;
lean_object* v_a_4715_ = stack[5].m_obj;
lean_object* v_a_4716_ = stack[6].m_obj;
lean_object* v_a_4717_ = stack[7].m_obj;
lean_object* v_a_4718_ = stack[8].m_obj;
lean_object* v_a_4719_ = stack[9].m_obj;
lean_object* v_a_4720_ = stack[10].m_obj;
lean_object* v_res_4723_;
v_res_4723_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f(v_e_4710_, v_a_4711_, v_a_4712_, v_a_4713_, v_a_4714_, v_a_4715_, v_a_4716_, v_a_4717_, v_a_4718_, v_a_4719_, v_a_4720_);
stack->m_obj
 = v_res_4723_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f___boxed(lean_object* v_e_4724_, lean_object* v_a_4725_, lean_object* v_a_4726_, lean_object* v_a_4727_, lean_object* v_a_4728_, lean_object* v_a_4729_, lean_object* v_a_4730_, lean_object* v_a_4731_, lean_object* v_a_4732_, lean_object* v_a_4733_, lean_object* v_a_4734_, lean_object* v_a_4735_){
_start:
{
lean_object* v_res_4736_; 
v_res_4736_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f(v_e_4724_, v_a_4725_, v_a_4726_, v_a_4727_, v_a_4728_, v_a_4729_, v_a_4730_, v_a_4731_, v_a_4732_, v_a_4733_, v_a_4734_);
lean_dec(v_a_4734_);
lean_dec_ref(v_a_4733_);
lean_dec(v_a_4732_);
lean_dec_ref(v_a_4731_);
lean_dec(v_a_4730_);
lean_dec_ref(v_a_4729_);
lean_dec(v_a_4728_);
lean_dec_ref(v_a_4727_);
lean_dec(v_a_4726_);
lean_dec(v_a_4725_);
lean_dec_ref(v_e_4724_);
return v_res_4736_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__8(void){
_start:
{
uint8_t v___x_4761_; lean_object* v___x_4762_; lean_object* v___x_4763_; 
v___x_4761_ = 0;
v___x_4762_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4);
v___x_4763_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4763_, 0, v___x_4762_);
lean_ctor_set_uint8(v___x_4763_, sizeof(void*)*1, v___x_4761_);
return v___x_4763_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__10(void){
_start:
{
lean_object* v___x_4765_; lean_object* v___x_4766_; 
v___x_4765_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__9));
v___x_4766_ = l_Lean_stringToMessageData(v___x_4765_);
return v___x_4766_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go(lean_object* v_a_4767_, lean_object* v_b_4768_, lean_object* v_h_4769_, lean_object* v_a_4770_, lean_object* v_a_4771_, lean_object* v_a_4772_, lean_object* v_a_4773_, lean_object* v_a_4774_, lean_object* v_a_4775_, lean_object* v_a_4776_, lean_object* v_a_4777_, lean_object* v_a_4778_, lean_object* v_a_4779_){
_start:
{
lean_object* v___y_4782_; lean_object* v___y_4783_; lean_object* v___y_4784_; lean_object* v___y_4785_; lean_object* v___y_4786_; lean_object* v___y_4787_; lean_object* v___y_4788_; lean_object* v___y_4789_; lean_object* v___y_4790_; lean_object* v___y_4791_; lean_object* v___y_4792_; lean_object* v___x_4880_; 
v___x_4880_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___redArg(v_a_4767_, v_a_4770_, v_a_4778_);
if (lean_obj_tag(v___x_4880_) == 0)
{
lean_object* v_a_4881_; lean_object* v___x_4883_; uint8_t v_isShared_4884_; uint8_t v_isSharedCheck_4927_; 
v_a_4881_ = lean_ctor_get(v___x_4880_, 0);
v_isSharedCheck_4927_ = !lean_is_exclusive(v___x_4880_);
if (v_isSharedCheck_4927_ == 0)
{
v___x_4883_ = v___x_4880_;
v_isShared_4884_ = v_isSharedCheck_4927_;
goto v_resetjp_4882_;
}
else
{
lean_inc(v_a_4881_);
lean_dec(v___x_4880_);
v___x_4883_ = lean_box(0);
v_isShared_4884_ = v_isSharedCheck_4927_;
goto v_resetjp_4882_;
}
v_resetjp_4882_:
{
if (lean_obj_tag(v_a_4881_) == 1)
{
lean_object* v_val_4885_; lean_object* v___x_4886_; 
lean_del_object(v___x_4883_);
v_val_4885_ = lean_ctor_get(v_a_4881_, 0);
lean_inc(v_val_4885_);
lean_dec_ref_known(v_a_4881_, 1);
v___x_4886_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___redArg(v_b_4768_, v_a_4770_, v_a_4778_);
if (lean_obj_tag(v___x_4886_) == 0)
{
lean_object* v_a_4887_; lean_object* v___x_4889_; uint8_t v_isShared_4890_; uint8_t v_isSharedCheck_4914_; 
v_a_4887_ = lean_ctor_get(v___x_4886_, 0);
v_isSharedCheck_4914_ = !lean_is_exclusive(v___x_4886_);
if (v_isSharedCheck_4914_ == 0)
{
v___x_4889_ = v___x_4886_;
v_isShared_4890_ = v_isSharedCheck_4914_;
goto v_resetjp_4888_;
}
else
{
lean_inc(v_a_4887_);
lean_dec(v___x_4886_);
v___x_4889_ = lean_box(0);
v_isShared_4890_ = v_isSharedCheck_4914_;
goto v_resetjp_4888_;
}
v_resetjp_4888_:
{
if (lean_obj_tag(v_a_4887_) == 1)
{
lean_object* v_val_4891_; uint8_t v___x_4892_; 
v_val_4891_ = lean_ctor_get(v_a_4887_, 0);
lean_inc(v_val_4891_);
lean_dec_ref_known(v_a_4887_, 1);
v___x_4892_ = lean_nat_dec_eq(v_val_4885_, v_val_4891_);
lean_dec(v_val_4891_);
if (v___x_4892_ == 0)
{
lean_object* v___x_4893_; lean_object* v___x_4895_; 
lean_dec(v_val_4885_);
lean_dec_ref(v_h_4769_);
lean_dec_ref(v_b_4768_);
lean_dec_ref(v_a_4767_);
v___x_4893_ = lean_box(0);
if (v_isShared_4890_ == 0)
{
lean_ctor_set(v___x_4889_, 0, v___x_4893_);
v___x_4895_ = v___x_4889_;
goto v_reusejp_4894_;
}
else
{
lean_object* v_reuseFailAlloc_4896_; 
v_reuseFailAlloc_4896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4896_, 0, v___x_4893_);
v___x_4895_ = v_reuseFailAlloc_4896_;
goto v_reusejp_4894_;
}
v_reusejp_4894_:
{
return v___x_4895_;
}
}
else
{
lean_object* v_toCold_4897_; lean_object* v_options_4898_; uint8_t v_hasTrace_4899_; 
lean_del_object(v___x_4889_);
v_toCold_4897_ = lean_ctor_get(v_a_4778_, 0);
v_options_4898_ = lean_ctor_get(v_toCold_4897_, 2);
v_hasTrace_4899_ = lean_ctor_get_uint8(v_options_4898_, sizeof(void*)*1);
if (v_hasTrace_4899_ == 0)
{
v___y_4782_ = v_val_4885_;
v___y_4783_ = v_a_4770_;
v___y_4784_ = v_a_4771_;
v___y_4785_ = v_a_4772_;
v___y_4786_ = v_a_4773_;
v___y_4787_ = v_a_4774_;
v___y_4788_ = v_a_4775_;
v___y_4789_ = v_a_4776_;
v___y_4790_ = v_a_4777_;
v___y_4791_ = v_a_4778_;
v___y_4792_ = v_a_4779_;
goto v___jp_4781_;
}
else
{
lean_object* v_inheritedTraceOptions_4900_; lean_object* v___x_4901_; lean_object* v___x_4902_; uint8_t v___x_4903_; 
v_inheritedTraceOptions_4900_ = lean_ctor_get(v_toCold_4897_, 11);
v___x_4901_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__4));
v___x_4902_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5);
v___x_4903_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4900_, v_options_4898_, v___x_4902_);
if (v___x_4903_ == 0)
{
v___y_4782_ = v_val_4885_;
v___y_4783_ = v_a_4770_;
v___y_4784_ = v_a_4771_;
v___y_4785_ = v_a_4772_;
v___y_4786_ = v_a_4773_;
v___y_4787_ = v_a_4774_;
v___y_4788_ = v_a_4775_;
v___y_4789_ = v_a_4776_;
v___y_4790_ = v_a_4777_;
v___y_4791_ = v_a_4778_;
v___y_4792_ = v_a_4779_;
goto v___jp_4781_;
}
else
{
lean_object* v___x_4904_; lean_object* v___x_4905_; lean_object* v___x_4906_; lean_object* v___x_4907_; lean_object* v___x_4908_; lean_object* v___x_4909_; 
lean_inc_ref(v_a_4767_);
v___x_4904_ = l_Lean_MessageData_ofExpr(v_a_4767_);
v___x_4905_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__10, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__10);
v___x_4906_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4906_, 0, v___x_4904_);
lean_ctor_set(v___x_4906_, 1, v___x_4905_);
lean_inc_ref(v_b_4768_);
v___x_4907_ = l_Lean_MessageData_ofExpr(v_b_4768_);
v___x_4908_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4908_, 0, v___x_4906_);
lean_ctor_set(v___x_4908_, 1, v___x_4907_);
v___x_4909_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(v___x_4901_, v___x_4908_, v_a_4776_, v_a_4777_, v_a_4778_, v_a_4779_);
if (lean_obj_tag(v___x_4909_) == 0)
{
lean_dec_ref_known(v___x_4909_, 1);
v___y_4782_ = v_val_4885_;
v___y_4783_ = v_a_4770_;
v___y_4784_ = v_a_4771_;
v___y_4785_ = v_a_4772_;
v___y_4786_ = v_a_4773_;
v___y_4787_ = v_a_4774_;
v___y_4788_ = v_a_4775_;
v___y_4789_ = v_a_4776_;
v___y_4790_ = v_a_4777_;
v___y_4791_ = v_a_4778_;
v___y_4792_ = v_a_4779_;
goto v___jp_4781_;
}
else
{
lean_dec(v_val_4885_);
lean_dec_ref(v_h_4769_);
lean_dec_ref(v_b_4768_);
lean_dec_ref(v_a_4767_);
return v___x_4909_;
}
}
}
}
}
else
{
lean_object* v___x_4910_; lean_object* v___x_4912_; 
lean_dec(v_a_4887_);
lean_dec(v_val_4885_);
lean_dec_ref(v_h_4769_);
lean_dec_ref(v_b_4768_);
lean_dec_ref(v_a_4767_);
v___x_4910_ = lean_box(0);
if (v_isShared_4890_ == 0)
{
lean_ctor_set(v___x_4889_, 0, v___x_4910_);
v___x_4912_ = v___x_4889_;
goto v_reusejp_4911_;
}
else
{
lean_object* v_reuseFailAlloc_4913_; 
v_reuseFailAlloc_4913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4913_, 0, v___x_4910_);
v___x_4912_ = v_reuseFailAlloc_4913_;
goto v_reusejp_4911_;
}
v_reusejp_4911_:
{
return v___x_4912_;
}
}
}
}
else
{
lean_object* v_a_4915_; lean_object* v___x_4917_; uint8_t v_isShared_4918_; uint8_t v_isSharedCheck_4922_; 
lean_dec(v_val_4885_);
lean_dec_ref(v_h_4769_);
lean_dec_ref(v_b_4768_);
lean_dec_ref(v_a_4767_);
v_a_4915_ = lean_ctor_get(v___x_4886_, 0);
v_isSharedCheck_4922_ = !lean_is_exclusive(v___x_4886_);
if (v_isSharedCheck_4922_ == 0)
{
v___x_4917_ = v___x_4886_;
v_isShared_4918_ = v_isSharedCheck_4922_;
goto v_resetjp_4916_;
}
else
{
lean_inc(v_a_4915_);
lean_dec(v___x_4886_);
v___x_4917_ = lean_box(0);
v_isShared_4918_ = v_isSharedCheck_4922_;
goto v_resetjp_4916_;
}
v_resetjp_4916_:
{
lean_object* v___x_4920_; 
if (v_isShared_4918_ == 0)
{
v___x_4920_ = v___x_4917_;
goto v_reusejp_4919_;
}
else
{
lean_object* v_reuseFailAlloc_4921_; 
v_reuseFailAlloc_4921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4921_, 0, v_a_4915_);
v___x_4920_ = v_reuseFailAlloc_4921_;
goto v_reusejp_4919_;
}
v_reusejp_4919_:
{
return v___x_4920_;
}
}
}
}
else
{
lean_object* v___x_4923_; lean_object* v___x_4925_; 
lean_dec(v_a_4881_);
lean_dec_ref(v_h_4769_);
lean_dec_ref(v_b_4768_);
lean_dec_ref(v_a_4767_);
v___x_4923_ = lean_box(0);
if (v_isShared_4884_ == 0)
{
lean_ctor_set(v___x_4883_, 0, v___x_4923_);
v___x_4925_ = v___x_4883_;
goto v_reusejp_4924_;
}
else
{
lean_object* v_reuseFailAlloc_4926_; 
v_reuseFailAlloc_4926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4926_, 0, v___x_4923_);
v___x_4925_ = v_reuseFailAlloc_4926_;
goto v_reusejp_4924_;
}
v_reusejp_4924_:
{
return v___x_4925_;
}
}
}
}
else
{
lean_object* v_a_4928_; lean_object* v___x_4930_; uint8_t v_isShared_4931_; uint8_t v_isSharedCheck_4935_; 
lean_dec_ref(v_h_4769_);
lean_dec_ref(v_b_4768_);
lean_dec_ref(v_a_4767_);
v_a_4928_ = lean_ctor_get(v___x_4880_, 0);
v_isSharedCheck_4935_ = !lean_is_exclusive(v___x_4880_);
if (v_isSharedCheck_4935_ == 0)
{
v___x_4930_ = v___x_4880_;
v_isShared_4931_ = v_isSharedCheck_4935_;
goto v_resetjp_4929_;
}
else
{
lean_inc(v_a_4928_);
lean_dec(v___x_4880_);
v___x_4930_ = lean_box(0);
v_isShared_4931_ = v_isSharedCheck_4935_;
goto v_resetjp_4929_;
}
v_resetjp_4929_:
{
lean_object* v___x_4933_; 
if (v_isShared_4931_ == 0)
{
v___x_4933_ = v___x_4930_;
goto v_reusejp_4932_;
}
else
{
lean_object* v_reuseFailAlloc_4934_; 
v_reuseFailAlloc_4934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4934_, 0, v_a_4928_);
v___x_4933_ = v_reuseFailAlloc_4934_;
goto v_reusejp_4932_;
}
v_reusejp_4932_:
{
return v___x_4933_;
}
}
}
v___jp_4781_:
{
lean_object* v___x_4793_; 
lean_inc_ref(v_a_4767_);
v___x_4793_ = l_Lean_Meta_Grind_Order_getNodeId___redArg(v_a_4767_, v___y_4782_, v___y_4783_, v___y_4789_, v___y_4790_, v___y_4791_, v___y_4792_);
if (lean_obj_tag(v___x_4793_) == 0)
{
lean_object* v_a_4794_; lean_object* v___x_4795_; 
v_a_4794_ = lean_ctor_get(v___x_4793_, 0);
lean_inc(v_a_4794_);
lean_dec_ref_known(v___x_4793_, 1);
lean_inc_ref(v_b_4768_);
v___x_4795_ = l_Lean_Meta_Grind_Order_getNodeId___redArg(v_b_4768_, v___y_4782_, v___y_4783_, v___y_4789_, v___y_4790_, v___y_4791_, v___y_4792_);
if (lean_obj_tag(v___x_4795_) == 0)
{
lean_object* v_a_4796_; lean_object* v___x_4797_; 
v_a_4796_ = lean_ctor_get(v___x_4795_, 0);
lean_inc(v_a_4796_);
lean_dec_ref_known(v___x_4795_, 1);
v___x_4797_ = l_Lean_Meta_Grind_Order_isRing(v___y_4782_, v___y_4783_, v___y_4784_, v___y_4785_, v___y_4786_, v___y_4787_, v___y_4788_, v___y_4789_, v___y_4790_, v___y_4791_, v___y_4792_);
if (lean_obj_tag(v___x_4797_) == 0)
{
lean_object* v_a_4798_; uint8_t v___x_4799_; 
v_a_4798_ = lean_ctor_get(v___x_4797_, 0);
lean_inc(v_a_4798_);
lean_dec_ref_known(v___x_4797_, 1);
v___x_4799_ = lean_unbox(v_a_4798_);
if (v___x_4799_ == 0)
{
lean_object* v___x_4800_; lean_object* v___x_4801_; 
v___x_4800_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__1));
v___x_4801_ = l_Lean_Meta_Grind_Order_mkLePreorderPrefix(v___x_4800_, v___y_4782_, v___y_4783_, v___y_4784_, v___y_4785_, v___y_4786_, v___y_4787_, v___y_4788_, v___y_4789_, v___y_4790_, v___y_4791_, v___y_4792_);
if (lean_obj_tag(v___x_4801_) == 0)
{
lean_object* v_a_4802_; lean_object* v___x_4803_; lean_object* v___x_4804_; lean_object* v___x_4805_; 
v_a_4802_ = lean_ctor_get(v___x_4801_, 0);
lean_inc(v_a_4802_);
lean_dec_ref_known(v___x_4801_, 1);
lean_inc_ref(v_h_4769_);
lean_inc_ref(v_b_4768_);
lean_inc_ref(v_a_4767_);
v___x_4803_ = l_Lean_mkApp3(v_a_4802_, v_a_4767_, v_b_4768_, v_h_4769_);
v___x_4804_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__3));
v___x_4805_ = l_Lean_Meta_Grind_Order_mkLePreorderPrefix(v___x_4804_, v___y_4782_, v___y_4783_, v___y_4784_, v___y_4785_, v___y_4786_, v___y_4787_, v___y_4788_, v___y_4789_, v___y_4790_, v___y_4791_, v___y_4792_);
if (lean_obj_tag(v___x_4805_) == 0)
{
lean_object* v_a_4806_; lean_object* v___x_4807_; lean_object* v___x_4808_; lean_object* v___x_4809_; uint8_t v___x_4810_; lean_object* v___x_4811_; 
v_a_4806_ = lean_ctor_get(v___x_4805_, 0);
lean_inc(v_a_4806_);
lean_dec_ref_known(v___x_4805_, 1);
v___x_4807_ = l_Lean_mkApp3(v_a_4806_, v_a_4767_, v_b_4768_, v_h_4769_);
v___x_4808_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4);
v___x_4809_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4809_, 0, v___x_4808_);
v___x_4810_ = lean_unbox(v_a_4798_);
lean_dec(v_a_4798_);
lean_ctor_set_uint8(v___x_4809_, sizeof(void*)*1, v___x_4810_);
lean_inc_ref(v___x_4809_);
lean_inc(v_a_4796_);
lean_inc(v_a_4794_);
v___x_4811_ = l_Lean_Meta_Grind_Order_addEdge(v_a_4794_, v_a_4796_, v___x_4809_, v___x_4803_, v___y_4782_, v___y_4783_, v___y_4784_, v___y_4785_, v___y_4786_, v___y_4787_, v___y_4788_, v___y_4789_, v___y_4790_, v___y_4791_, v___y_4792_);
if (lean_obj_tag(v___x_4811_) == 0)
{
lean_object* v___x_4812_; 
lean_dec_ref_known(v___x_4811_, 1);
v___x_4812_ = l_Lean_Meta_Grind_Order_addEdge(v_a_4796_, v_a_4794_, v___x_4809_, v___x_4807_, v___y_4782_, v___y_4783_, v___y_4784_, v___y_4785_, v___y_4786_, v___y_4787_, v___y_4788_, v___y_4789_, v___y_4790_, v___y_4791_, v___y_4792_);
lean_dec(v___y_4782_);
return v___x_4812_;
}
else
{
lean_dec_ref_known(v___x_4809_, 1);
lean_dec_ref(v___x_4807_);
lean_dec(v_a_4796_);
lean_dec(v_a_4794_);
lean_dec(v___y_4782_);
return v___x_4811_;
}
}
else
{
lean_object* v_a_4813_; lean_object* v___x_4815_; uint8_t v_isShared_4816_; uint8_t v_isSharedCheck_4820_; 
lean_dec_ref(v___x_4803_);
lean_dec(v_a_4798_);
lean_dec(v_a_4796_);
lean_dec(v_a_4794_);
lean_dec(v___y_4782_);
lean_dec_ref(v_h_4769_);
lean_dec_ref(v_b_4768_);
lean_dec_ref(v_a_4767_);
v_a_4813_ = lean_ctor_get(v___x_4805_, 0);
v_isSharedCheck_4820_ = !lean_is_exclusive(v___x_4805_);
if (v_isSharedCheck_4820_ == 0)
{
v___x_4815_ = v___x_4805_;
v_isShared_4816_ = v_isSharedCheck_4820_;
goto v_resetjp_4814_;
}
else
{
lean_inc(v_a_4813_);
lean_dec(v___x_4805_);
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
else
{
lean_object* v_a_4821_; lean_object* v___x_4823_; uint8_t v_isShared_4824_; uint8_t v_isSharedCheck_4828_; 
lean_dec(v_a_4798_);
lean_dec(v_a_4796_);
lean_dec(v_a_4794_);
lean_dec(v___y_4782_);
lean_dec_ref(v_h_4769_);
lean_dec_ref(v_b_4768_);
lean_dec_ref(v_a_4767_);
v_a_4821_ = lean_ctor_get(v___x_4801_, 0);
v_isSharedCheck_4828_ = !lean_is_exclusive(v___x_4801_);
if (v_isSharedCheck_4828_ == 0)
{
v___x_4823_ = v___x_4801_;
v_isShared_4824_ = v_isSharedCheck_4828_;
goto v_resetjp_4822_;
}
else
{
lean_inc(v_a_4821_);
lean_dec(v___x_4801_);
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
lean_object* v___x_4829_; lean_object* v___x_4830_; 
lean_dec(v_a_4798_);
v___x_4829_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__5));
v___x_4830_ = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(v___x_4829_, v___y_4782_, v___y_4783_, v___y_4784_, v___y_4785_, v___y_4786_, v___y_4787_, v___y_4788_, v___y_4789_, v___y_4790_, v___y_4791_, v___y_4792_);
if (lean_obj_tag(v___x_4830_) == 0)
{
lean_object* v_a_4831_; lean_object* v___x_4832_; lean_object* v___x_4833_; lean_object* v___x_4834_; 
v_a_4831_ = lean_ctor_get(v___x_4830_, 0);
lean_inc(v_a_4831_);
lean_dec_ref_known(v___x_4830_, 1);
lean_inc_ref(v_h_4769_);
lean_inc_ref(v_b_4768_);
lean_inc_ref(v_a_4767_);
v___x_4832_ = l_Lean_mkApp3(v_a_4831_, v_a_4767_, v_b_4768_, v_h_4769_);
v___x_4833_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__7));
v___x_4834_ = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(v___x_4833_, v___y_4782_, v___y_4783_, v___y_4784_, v___y_4785_, v___y_4786_, v___y_4787_, v___y_4788_, v___y_4789_, v___y_4790_, v___y_4791_, v___y_4792_);
if (lean_obj_tag(v___x_4834_) == 0)
{
lean_object* v_a_4835_; lean_object* v___x_4836_; lean_object* v___x_4837_; lean_object* v___x_4838_; 
v_a_4835_ = lean_ctor_get(v___x_4834_, 0);
lean_inc(v_a_4835_);
lean_dec_ref_known(v___x_4834_, 1);
v___x_4836_ = l_Lean_mkApp3(v_a_4835_, v_a_4767_, v_b_4768_, v_h_4769_);
v___x_4837_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__8, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__8);
lean_inc(v_a_4796_);
lean_inc(v_a_4794_);
v___x_4838_ = l_Lean_Meta_Grind_Order_addEdge(v_a_4794_, v_a_4796_, v___x_4837_, v___x_4832_, v___y_4782_, v___y_4783_, v___y_4784_, v___y_4785_, v___y_4786_, v___y_4787_, v___y_4788_, v___y_4789_, v___y_4790_, v___y_4791_, v___y_4792_);
if (lean_obj_tag(v___x_4838_) == 0)
{
lean_object* v___x_4839_; 
lean_dec_ref_known(v___x_4838_, 1);
v___x_4839_ = l_Lean_Meta_Grind_Order_addEdge(v_a_4796_, v_a_4794_, v___x_4837_, v___x_4836_, v___y_4782_, v___y_4783_, v___y_4784_, v___y_4785_, v___y_4786_, v___y_4787_, v___y_4788_, v___y_4789_, v___y_4790_, v___y_4791_, v___y_4792_);
lean_dec(v___y_4782_);
return v___x_4839_;
}
else
{
lean_dec_ref(v___x_4836_);
lean_dec(v_a_4796_);
lean_dec(v_a_4794_);
lean_dec(v___y_4782_);
return v___x_4838_;
}
}
else
{
lean_object* v_a_4840_; lean_object* v___x_4842_; uint8_t v_isShared_4843_; uint8_t v_isSharedCheck_4847_; 
lean_dec_ref(v___x_4832_);
lean_dec(v_a_4796_);
lean_dec(v_a_4794_);
lean_dec(v___y_4782_);
lean_dec_ref(v_h_4769_);
lean_dec_ref(v_b_4768_);
lean_dec_ref(v_a_4767_);
v_a_4840_ = lean_ctor_get(v___x_4834_, 0);
v_isSharedCheck_4847_ = !lean_is_exclusive(v___x_4834_);
if (v_isSharedCheck_4847_ == 0)
{
v___x_4842_ = v___x_4834_;
v_isShared_4843_ = v_isSharedCheck_4847_;
goto v_resetjp_4841_;
}
else
{
lean_inc(v_a_4840_);
lean_dec(v___x_4834_);
v___x_4842_ = lean_box(0);
v_isShared_4843_ = v_isSharedCheck_4847_;
goto v_resetjp_4841_;
}
v_resetjp_4841_:
{
lean_object* v___x_4845_; 
if (v_isShared_4843_ == 0)
{
v___x_4845_ = v___x_4842_;
goto v_reusejp_4844_;
}
else
{
lean_object* v_reuseFailAlloc_4846_; 
v_reuseFailAlloc_4846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4846_, 0, v_a_4840_);
v___x_4845_ = v_reuseFailAlloc_4846_;
goto v_reusejp_4844_;
}
v_reusejp_4844_:
{
return v___x_4845_;
}
}
}
}
else
{
lean_object* v_a_4848_; lean_object* v___x_4850_; uint8_t v_isShared_4851_; uint8_t v_isSharedCheck_4855_; 
lean_dec(v_a_4796_);
lean_dec(v_a_4794_);
lean_dec(v___y_4782_);
lean_dec_ref(v_h_4769_);
lean_dec_ref(v_b_4768_);
lean_dec_ref(v_a_4767_);
v_a_4848_ = lean_ctor_get(v___x_4830_, 0);
v_isSharedCheck_4855_ = !lean_is_exclusive(v___x_4830_);
if (v_isSharedCheck_4855_ == 0)
{
v___x_4850_ = v___x_4830_;
v_isShared_4851_ = v_isSharedCheck_4855_;
goto v_resetjp_4849_;
}
else
{
lean_inc(v_a_4848_);
lean_dec(v___x_4830_);
v___x_4850_ = lean_box(0);
v_isShared_4851_ = v_isSharedCheck_4855_;
goto v_resetjp_4849_;
}
v_resetjp_4849_:
{
lean_object* v___x_4853_; 
if (v_isShared_4851_ == 0)
{
v___x_4853_ = v___x_4850_;
goto v_reusejp_4852_;
}
else
{
lean_object* v_reuseFailAlloc_4854_; 
v_reuseFailAlloc_4854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4854_, 0, v_a_4848_);
v___x_4853_ = v_reuseFailAlloc_4854_;
goto v_reusejp_4852_;
}
v_reusejp_4852_:
{
return v___x_4853_;
}
}
}
}
}
else
{
lean_object* v_a_4856_; lean_object* v___x_4858_; uint8_t v_isShared_4859_; uint8_t v_isSharedCheck_4863_; 
lean_dec(v_a_4796_);
lean_dec(v_a_4794_);
lean_dec(v___y_4782_);
lean_dec_ref(v_h_4769_);
lean_dec_ref(v_b_4768_);
lean_dec_ref(v_a_4767_);
v_a_4856_ = lean_ctor_get(v___x_4797_, 0);
v_isSharedCheck_4863_ = !lean_is_exclusive(v___x_4797_);
if (v_isSharedCheck_4863_ == 0)
{
v___x_4858_ = v___x_4797_;
v_isShared_4859_ = v_isSharedCheck_4863_;
goto v_resetjp_4857_;
}
else
{
lean_inc(v_a_4856_);
lean_dec(v___x_4797_);
v___x_4858_ = lean_box(0);
v_isShared_4859_ = v_isSharedCheck_4863_;
goto v_resetjp_4857_;
}
v_resetjp_4857_:
{
lean_object* v___x_4861_; 
if (v_isShared_4859_ == 0)
{
v___x_4861_ = v___x_4858_;
goto v_reusejp_4860_;
}
else
{
lean_object* v_reuseFailAlloc_4862_; 
v_reuseFailAlloc_4862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4862_, 0, v_a_4856_);
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
lean_dec(v_a_4794_);
lean_dec(v___y_4782_);
lean_dec_ref(v_h_4769_);
lean_dec_ref(v_b_4768_);
lean_dec_ref(v_a_4767_);
v_a_4864_ = lean_ctor_get(v___x_4795_, 0);
v_isSharedCheck_4871_ = !lean_is_exclusive(v___x_4795_);
if (v_isSharedCheck_4871_ == 0)
{
v___x_4866_ = v___x_4795_;
v_isShared_4867_ = v_isSharedCheck_4871_;
goto v_resetjp_4865_;
}
else
{
lean_inc(v_a_4864_);
lean_dec(v___x_4795_);
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
}
else
{
lean_object* v_a_4872_; lean_object* v___x_4874_; uint8_t v_isShared_4875_; uint8_t v_isSharedCheck_4879_; 
lean_dec(v___y_4782_);
lean_dec_ref(v_h_4769_);
lean_dec_ref(v_b_4768_);
lean_dec_ref(v_a_4767_);
v_a_4872_ = lean_ctor_get(v___x_4793_, 0);
v_isSharedCheck_4879_ = !lean_is_exclusive(v___x_4793_);
if (v_isSharedCheck_4879_ == 0)
{
v___x_4874_ = v___x_4793_;
v_isShared_4875_ = v_isSharedCheck_4879_;
goto v_resetjp_4873_;
}
else
{
lean_inc(v_a_4872_);
lean_dec(v___x_4793_);
v___x_4874_ = lean_box(0);
v_isShared_4875_ = v_isSharedCheck_4879_;
goto v_resetjp_4873_;
}
v_resetjp_4873_:
{
lean_object* v___x_4877_; 
if (v_isShared_4875_ == 0)
{
v___x_4877_ = v___x_4874_;
goto v_reusejp_4876_;
}
else
{
lean_object* v_reuseFailAlloc_4878_; 
v_reuseFailAlloc_4878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4878_, 0, v_a_4872_);
v___x_4877_ = v_reuseFailAlloc_4878_;
goto v_reusejp_4876_;
}
v_reusejp_4876_:
{
return v___x_4877_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4767_ = stack[0].m_obj;
lean_object* v_b_4768_ = stack[1].m_obj;
lean_object* v_h_4769_ = stack[2].m_obj;
lean_object* v_a_4770_ = stack[3].m_obj;
lean_object* v_a_4771_ = stack[4].m_obj;
lean_object* v_a_4772_ = stack[5].m_obj;
lean_object* v_a_4773_ = stack[6].m_obj;
lean_object* v_a_4774_ = stack[7].m_obj;
lean_object* v_a_4775_ = stack[8].m_obj;
lean_object* v_a_4776_ = stack[9].m_obj;
lean_object* v_a_4777_ = stack[10].m_obj;
lean_object* v_a_4778_ = stack[11].m_obj;
lean_object* v_a_4779_ = stack[12].m_obj;
lean_object* v_res_4936_;
v_res_4936_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go(v_a_4767_, v_b_4768_, v_h_4769_, v_a_4770_, v_a_4771_, v_a_4772_, v_a_4773_, v_a_4774_, v_a_4775_, v_a_4776_, v_a_4777_, v_a_4778_, v_a_4779_);
stack->m_obj
 = v_res_4936_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___boxed(lean_object* v_a_4937_, lean_object* v_b_4938_, lean_object* v_h_4939_, lean_object* v_a_4940_, lean_object* v_a_4941_, lean_object* v_a_4942_, lean_object* v_a_4943_, lean_object* v_a_4944_, lean_object* v_a_4945_, lean_object* v_a_4946_, lean_object* v_a_4947_, lean_object* v_a_4948_, lean_object* v_a_4949_, lean_object* v_a_4950_){
_start:
{
lean_object* v_res_4951_; 
v_res_4951_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go(v_a_4937_, v_b_4938_, v_h_4939_, v_a_4940_, v_a_4941_, v_a_4942_, v_a_4943_, v_a_4944_, v_a_4945_, v_a_4946_, v_a_4947_, v_a_4948_, v_a_4949_);
lean_dec(v_a_4949_);
lean_dec_ref(v_a_4948_);
lean_dec(v_a_4947_);
lean_dec_ref(v_a_4946_);
lean_dec(v_a_4945_);
lean_dec_ref(v_a_4944_);
lean_dec(v_a_4943_);
lean_dec_ref(v_a_4942_);
lean_dec(v_a_4941_);
lean_dec(v_a_4940_);
return v_res_4951_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_processNewEq___closed__6(void){
_start:
{
lean_object* v___x_4967_; lean_object* v___x_4968_; lean_object* v___x_4969_; 
v___x_4967_ = lean_box(0);
v___x_4968_ = ((lean_object*)(l_Lean_Meta_Grind_Order_processNewEq___closed__5));
v___x_4969_ = l_Lean_mkConst(v___x_4968_, v___x_4967_);
return v___x_4969_;
}
}
lean_object* l_Lean_Meta_Grind_Order_processNewEq(lean_object* v_a_4970_, lean_object* v_b_4971_, lean_object* v_a_4972_, lean_object* v_a_4973_, lean_object* v_a_4974_, lean_object* v_a_4975_, lean_object* v_a_4976_, lean_object* v_a_4977_, lean_object* v_a_4978_, lean_object* v_a_4979_, lean_object* v_a_4980_, lean_object* v_a_4981_){
_start:
{
size_t v___x_4983_; size_t v___x_4984_; uint8_t v___x_4985_; 
v___x_4983_ = lean_ptr_addr(v_a_4970_);
v___x_4984_ = lean_ptr_addr(v_b_4971_);
v___x_4985_ = lean_usize_dec_eq(v___x_4983_, v___x_4984_);
if (v___x_4985_ == 0)
{
lean_object* v___x_4986_; 
lean_inc(v_a_4981_);
lean_inc_ref(v_a_4980_);
lean_inc(v_a_4979_);
lean_inc_ref(v_a_4978_);
lean_inc(v_a_4977_);
lean_inc_ref(v_a_4976_);
lean_inc(v_a_4975_);
lean_inc_ref(v_a_4974_);
lean_inc(v_a_4973_);
lean_inc(v_a_4972_);
lean_inc_ref(v_b_4971_);
lean_inc_ref(v_a_4970_);
v___x_4986_ = lean_grind_mk_eq_proof(v_a_4970_, v_b_4971_, v_a_4972_, v_a_4973_, v_a_4974_, v_a_4975_, v_a_4976_, v_a_4977_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_);
if (lean_obj_tag(v___x_4986_) == 0)
{
lean_object* v_a_4987_; lean_object* v___x_4988_; 
v_a_4987_ = lean_ctor_get(v___x_4986_, 0);
lean_inc(v_a_4987_);
lean_dec_ref_known(v___x_4986_, 1);
v___x_4988_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f___redArg(v_a_4970_, v_a_4972_, v_a_4980_);
if (lean_obj_tag(v___x_4988_) == 0)
{
lean_object* v_a_4989_; 
v_a_4989_ = lean_ctor_get(v___x_4988_, 0);
lean_inc(v_a_4989_);
lean_dec_ref_known(v___x_4988_, 1);
if (lean_obj_tag(v_a_4989_) == 1)
{
lean_object* v_val_4990_; lean_object* v_e_4991_; lean_object* v_h_4992_; lean_object* v_00_u03b1_4993_; lean_object* v___x_4994_; 
v_val_4990_ = lean_ctor_get(v_a_4989_, 0);
lean_inc(v_val_4990_);
lean_dec_ref_known(v_a_4989_, 1);
v_e_4991_ = lean_ctor_get(v_val_4990_, 0);
lean_inc_ref(v_e_4991_);
v_h_4992_ = lean_ctor_get(v_val_4990_, 1);
lean_inc_ref(v_h_4992_);
v_00_u03b1_4993_ = lean_ctor_get(v_val_4990_, 2);
lean_inc_ref(v_00_u03b1_4993_);
lean_dec(v_val_4990_);
v___x_4994_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f___redArg(v_b_4971_, v_a_4972_, v_a_4980_);
if (lean_obj_tag(v___x_4994_) == 0)
{
lean_object* v_a_4995_; lean_object* v___x_4997_; uint8_t v_isShared_4998_; uint8_t v_isSharedCheck_5040_; 
v_a_4995_ = lean_ctor_get(v___x_4994_, 0);
v_isSharedCheck_5040_ = !lean_is_exclusive(v___x_4994_);
if (v_isSharedCheck_5040_ == 0)
{
v___x_4997_ = v___x_4994_;
v_isShared_4998_ = v_isSharedCheck_5040_;
goto v_resetjp_4996_;
}
else
{
lean_inc(v_a_4995_);
lean_dec(v___x_4994_);
v___x_4997_ = lean_box(0);
v_isShared_4998_ = v_isSharedCheck_5040_;
goto v_resetjp_4996_;
}
v_resetjp_4996_:
{
if (lean_obj_tag(v_a_4995_) == 1)
{
lean_object* v_val_4999_; lean_object* v_e_5000_; lean_object* v_h_5001_; lean_object* v___x_5002_; uint8_t v___x_5003_; 
lean_del_object(v___x_4997_);
v_val_4999_ = lean_ctor_get(v_a_4995_, 0);
lean_inc(v_val_4999_);
lean_dec_ref_known(v_a_4995_, 1);
v_e_5000_ = lean_ctor_get(v_val_4999_, 0);
lean_inc_ref(v_e_5000_);
v_h_5001_ = lean_ctor_get(v_val_4999_, 1);
lean_inc_ref(v_h_5001_);
lean_dec(v_val_4999_);
v___x_5002_ = l_Lean_Int_mkType;
v___x_5003_ = lean_expr_eqv(v_00_u03b1_4993_, v___x_5002_);
if (v___x_5003_ == 0)
{
lean_object* v___x_5004_; 
lean_inc_ref(v_00_u03b1_4993_);
v___x_5004_ = l_Lean_Meta_getDecLevel(v_00_u03b1_4993_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_);
if (lean_obj_tag(v___x_5004_) == 0)
{
lean_object* v_a_5005_; lean_object* v___x_5006_; lean_object* v___x_5007_; lean_object* v___x_5008_; lean_object* v___x_5009_; lean_object* v___x_5010_; lean_object* v___x_5011_; 
v_a_5005_ = lean_ctor_get(v___x_5004_, 0);
lean_inc(v_a_5005_);
lean_dec_ref_known(v___x_5004_, 1);
v___x_5006_ = ((lean_object*)(l_Lean_Meta_Grind_Order_processNewEq___closed__1));
v___x_5007_ = lean_box(0);
v___x_5008_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5008_, 0, v_a_5005_);
lean_ctor_set(v___x_5008_, 1, v___x_5007_);
lean_inc_ref(v___x_5008_);
v___x_5009_ = l_Lean_mkConst(v___x_5006_, v___x_5008_);
lean_inc_ref(v_00_u03b1_4993_);
v___x_5010_ = l_Lean_Expr_app___override(v___x_5009_, v_00_u03b1_4993_);
v___x_5011_ = l_Lean_Meta_Sym_synthInstance(v___x_5010_, v_a_4976_, v_a_4977_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_);
if (lean_obj_tag(v___x_5011_) == 0)
{
lean_object* v_a_5012_; lean_object* v___x_5013_; lean_object* v___x_5014_; lean_object* v___x_5015_; lean_object* v___x_5016_; 
v_a_5012_ = lean_ctor_get(v___x_5011_, 0);
lean_inc(v_a_5012_);
lean_dec_ref_known(v___x_5011_, 1);
v___x_5013_ = ((lean_object*)(l_Lean_Meta_Grind_Order_processNewEq___closed__3));
v___x_5014_ = l_Lean_mkConst(v___x_5013_, v___x_5008_);
lean_inc_ref(v_e_5000_);
lean_inc_ref(v_e_4991_);
v___x_5015_ = l_Lean_mkApp9(v___x_5014_, v_00_u03b1_4993_, v_a_5012_, v_a_4970_, v_b_4971_, v_e_4991_, v_e_5000_, v_h_4992_, v_h_5001_, v_a_4987_);
v___x_5016_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go(v_e_4991_, v_e_5000_, v___x_5015_, v_a_4972_, v_a_4973_, v_a_4974_, v_a_4975_, v_a_4976_, v_a_4977_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_);
return v___x_5016_;
}
else
{
lean_object* v_a_5017_; lean_object* v___x_5019_; uint8_t v_isShared_5020_; uint8_t v_isSharedCheck_5024_; 
lean_dec_ref_known(v___x_5008_, 2);
lean_dec_ref(v_h_5001_);
lean_dec_ref(v_e_5000_);
lean_dec_ref(v_00_u03b1_4993_);
lean_dec_ref(v_h_4992_);
lean_dec_ref(v_e_4991_);
lean_dec(v_a_4987_);
lean_dec_ref(v_b_4971_);
lean_dec_ref(v_a_4970_);
v_a_5017_ = lean_ctor_get(v___x_5011_, 0);
v_isSharedCheck_5024_ = !lean_is_exclusive(v___x_5011_);
if (v_isSharedCheck_5024_ == 0)
{
v___x_5019_ = v___x_5011_;
v_isShared_5020_ = v_isSharedCheck_5024_;
goto v_resetjp_5018_;
}
else
{
lean_inc(v_a_5017_);
lean_dec(v___x_5011_);
v___x_5019_ = lean_box(0);
v_isShared_5020_ = v_isSharedCheck_5024_;
goto v_resetjp_5018_;
}
v_resetjp_5018_:
{
lean_object* v___x_5022_; 
if (v_isShared_5020_ == 0)
{
v___x_5022_ = v___x_5019_;
goto v_reusejp_5021_;
}
else
{
lean_object* v_reuseFailAlloc_5023_; 
v_reuseFailAlloc_5023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5023_, 0, v_a_5017_);
v___x_5022_ = v_reuseFailAlloc_5023_;
goto v_reusejp_5021_;
}
v_reusejp_5021_:
{
return v___x_5022_;
}
}
}
}
else
{
lean_object* v_a_5025_; lean_object* v___x_5027_; uint8_t v_isShared_5028_; uint8_t v_isSharedCheck_5032_; 
lean_dec_ref(v_h_5001_);
lean_dec_ref(v_e_5000_);
lean_dec_ref(v_00_u03b1_4993_);
lean_dec_ref(v_h_4992_);
lean_dec_ref(v_e_4991_);
lean_dec(v_a_4987_);
lean_dec_ref(v_b_4971_);
lean_dec_ref(v_a_4970_);
v_a_5025_ = lean_ctor_get(v___x_5004_, 0);
v_isSharedCheck_5032_ = !lean_is_exclusive(v___x_5004_);
if (v_isSharedCheck_5032_ == 0)
{
v___x_5027_ = v___x_5004_;
v_isShared_5028_ = v_isSharedCheck_5032_;
goto v_resetjp_5026_;
}
else
{
lean_inc(v_a_5025_);
lean_dec(v___x_5004_);
v___x_5027_ = lean_box(0);
v_isShared_5028_ = v_isSharedCheck_5032_;
goto v_resetjp_5026_;
}
v_resetjp_5026_:
{
lean_object* v___x_5030_; 
if (v_isShared_5028_ == 0)
{
v___x_5030_ = v___x_5027_;
goto v_reusejp_5029_;
}
else
{
lean_object* v_reuseFailAlloc_5031_; 
v_reuseFailAlloc_5031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5031_, 0, v_a_5025_);
v___x_5030_ = v_reuseFailAlloc_5031_;
goto v_reusejp_5029_;
}
v_reusejp_5029_:
{
return v___x_5030_;
}
}
}
}
else
{
lean_object* v___x_5033_; lean_object* v___x_5034_; lean_object* v___x_5035_; 
lean_dec_ref(v_00_u03b1_4993_);
v___x_5033_ = lean_obj_once(&l_Lean_Meta_Grind_Order_processNewEq___closed__6, &l_Lean_Meta_Grind_Order_processNewEq___closed__6_once, _init_l_Lean_Meta_Grind_Order_processNewEq___closed__6);
lean_inc_ref(v_e_5000_);
lean_inc_ref(v_e_4991_);
v___x_5034_ = l_Lean_mkApp7(v___x_5033_, v_a_4970_, v_b_4971_, v_e_4991_, v_e_5000_, v_h_4992_, v_h_5001_, v_a_4987_);
v___x_5035_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go(v_e_4991_, v_e_5000_, v___x_5034_, v_a_4972_, v_a_4973_, v_a_4974_, v_a_4975_, v_a_4976_, v_a_4977_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_);
return v___x_5035_;
}
}
else
{
lean_object* v___x_5036_; lean_object* v___x_5038_; 
lean_dec(v_a_4995_);
lean_dec_ref(v_00_u03b1_4993_);
lean_dec_ref(v_h_4992_);
lean_dec_ref(v_e_4991_);
lean_dec(v_a_4987_);
lean_dec_ref(v_b_4971_);
lean_dec_ref(v_a_4970_);
v___x_5036_ = lean_box(0);
if (v_isShared_4998_ == 0)
{
lean_ctor_set(v___x_4997_, 0, v___x_5036_);
v___x_5038_ = v___x_4997_;
goto v_reusejp_5037_;
}
else
{
lean_object* v_reuseFailAlloc_5039_; 
v_reuseFailAlloc_5039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5039_, 0, v___x_5036_);
v___x_5038_ = v_reuseFailAlloc_5039_;
goto v_reusejp_5037_;
}
v_reusejp_5037_:
{
return v___x_5038_;
}
}
}
}
else
{
lean_object* v_a_5041_; lean_object* v___x_5043_; uint8_t v_isShared_5044_; uint8_t v_isSharedCheck_5048_; 
lean_dec_ref(v_00_u03b1_4993_);
lean_dec_ref(v_h_4992_);
lean_dec_ref(v_e_4991_);
lean_dec(v_a_4987_);
lean_dec_ref(v_b_4971_);
lean_dec_ref(v_a_4970_);
v_a_5041_ = lean_ctor_get(v___x_4994_, 0);
v_isSharedCheck_5048_ = !lean_is_exclusive(v___x_4994_);
if (v_isSharedCheck_5048_ == 0)
{
v___x_5043_ = v___x_4994_;
v_isShared_5044_ = v_isSharedCheck_5048_;
goto v_resetjp_5042_;
}
else
{
lean_inc(v_a_5041_);
lean_dec(v___x_4994_);
v___x_5043_ = lean_box(0);
v_isShared_5044_ = v_isSharedCheck_5048_;
goto v_resetjp_5042_;
}
v_resetjp_5042_:
{
lean_object* v___x_5046_; 
if (v_isShared_5044_ == 0)
{
v___x_5046_ = v___x_5043_;
goto v_reusejp_5045_;
}
else
{
lean_object* v_reuseFailAlloc_5047_; 
v_reuseFailAlloc_5047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5047_, 0, v_a_5041_);
v___x_5046_ = v_reuseFailAlloc_5047_;
goto v_reusejp_5045_;
}
v_reusejp_5045_:
{
return v___x_5046_;
}
}
}
}
else
{
lean_object* v___x_5049_; 
lean_dec(v_a_4989_);
v___x_5049_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go(v_a_4970_, v_b_4971_, v_a_4987_, v_a_4972_, v_a_4973_, v_a_4974_, v_a_4975_, v_a_4976_, v_a_4977_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_);
return v___x_5049_;
}
}
else
{
lean_object* v_a_5050_; lean_object* v___x_5052_; uint8_t v_isShared_5053_; uint8_t v_isSharedCheck_5057_; 
lean_dec(v_a_4987_);
lean_dec_ref(v_b_4971_);
lean_dec_ref(v_a_4970_);
v_a_5050_ = lean_ctor_get(v___x_4988_, 0);
v_isSharedCheck_5057_ = !lean_is_exclusive(v___x_4988_);
if (v_isSharedCheck_5057_ == 0)
{
v___x_5052_ = v___x_4988_;
v_isShared_5053_ = v_isSharedCheck_5057_;
goto v_resetjp_5051_;
}
else
{
lean_inc(v_a_5050_);
lean_dec(v___x_4988_);
v___x_5052_ = lean_box(0);
v_isShared_5053_ = v_isSharedCheck_5057_;
goto v_resetjp_5051_;
}
v_resetjp_5051_:
{
lean_object* v___x_5055_; 
if (v_isShared_5053_ == 0)
{
v___x_5055_ = v___x_5052_;
goto v_reusejp_5054_;
}
else
{
lean_object* v_reuseFailAlloc_5056_; 
v_reuseFailAlloc_5056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5056_, 0, v_a_5050_);
v___x_5055_ = v_reuseFailAlloc_5056_;
goto v_reusejp_5054_;
}
v_reusejp_5054_:
{
return v___x_5055_;
}
}
}
}
else
{
lean_object* v_a_5058_; lean_object* v___x_5060_; uint8_t v_isShared_5061_; uint8_t v_isSharedCheck_5065_; 
lean_dec_ref(v_b_4971_);
lean_dec_ref(v_a_4970_);
v_a_5058_ = lean_ctor_get(v___x_4986_, 0);
v_isSharedCheck_5065_ = !lean_is_exclusive(v___x_4986_);
if (v_isSharedCheck_5065_ == 0)
{
v___x_5060_ = v___x_4986_;
v_isShared_5061_ = v_isSharedCheck_5065_;
goto v_resetjp_5059_;
}
else
{
lean_inc(v_a_5058_);
lean_dec(v___x_4986_);
v___x_5060_ = lean_box(0);
v_isShared_5061_ = v_isSharedCheck_5065_;
goto v_resetjp_5059_;
}
v_resetjp_5059_:
{
lean_object* v___x_5063_; 
if (v_isShared_5061_ == 0)
{
v___x_5063_ = v___x_5060_;
goto v_reusejp_5062_;
}
else
{
lean_object* v_reuseFailAlloc_5064_; 
v_reuseFailAlloc_5064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5064_, 0, v_a_5058_);
v___x_5063_ = v_reuseFailAlloc_5064_;
goto v_reusejp_5062_;
}
v_reusejp_5062_:
{
return v___x_5063_;
}
}
}
}
else
{
lean_object* v___x_5066_; lean_object* v___x_5067_; 
lean_dec_ref(v_b_4971_);
lean_dec_ref(v_a_4970_);
v___x_5066_ = lean_box(0);
v___x_5067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5067_, 0, v___x_5066_);
return v___x_5067_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Order_processNewEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4970_ = stack[0].m_obj;
lean_object* v_b_4971_ = stack[1].m_obj;
lean_object* v_a_4972_ = stack[2].m_obj;
lean_object* v_a_4973_ = stack[3].m_obj;
lean_object* v_a_4974_ = stack[4].m_obj;
lean_object* v_a_4975_ = stack[5].m_obj;
lean_object* v_a_4976_ = stack[6].m_obj;
lean_object* v_a_4977_ = stack[7].m_obj;
lean_object* v_a_4978_ = stack[8].m_obj;
lean_object* v_a_4979_ = stack[9].m_obj;
lean_object* v_a_4980_ = stack[10].m_obj;
lean_object* v_a_4981_ = stack[11].m_obj;
lean_object* v_res_5068_;
v_res_5068_ = l_Lean_Meta_Grind_Order_processNewEq(v_a_4970_, v_b_4971_, v_a_4972_, v_a_4973_, v_a_4974_, v_a_4975_, v_a_4976_, v_a_4977_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_);
stack->m_obj
 = v_res_5068_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_processNewEq___boxed(lean_object* v_a_5069_, lean_object* v_b_5070_, lean_object* v_a_5071_, lean_object* v_a_5072_, lean_object* v_a_5073_, lean_object* v_a_5074_, lean_object* v_a_5075_, lean_object* v_a_5076_, lean_object* v_a_5077_, lean_object* v_a_5078_, lean_object* v_a_5079_, lean_object* v_a_5080_, lean_object* v_a_5081_){
_start:
{
lean_object* v_res_5082_; 
v_res_5082_ = l_Lean_Meta_Grind_Order_processNewEq(v_a_5069_, v_b_5070_, v_a_5071_, v_a_5072_, v_a_5073_, v_a_5074_, v_a_5075_, v_a_5076_, v_a_5077_, v_a_5078_, v_a_5079_, v_a_5080_);
lean_dec(v_a_5080_);
lean_dec_ref(v_a_5079_);
lean_dec(v_a_5078_);
lean_dec_ref(v_a_5077_);
lean_dec(v_a_5076_);
lean_dec_ref(v_a_5075_);
lean_dec(v_a_5074_);
lean_dec_ref(v_a_5073_);
lean_dec(v_a_5072_);
lean_dec(v_a_5071_);
return v_res_5082_;
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
