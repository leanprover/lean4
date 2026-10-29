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
lean_object* l_Lean_Meta_Grind_alreadyInternalized___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqv___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Int_mkType;
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_mkApp7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_array_push(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
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
lean_object* l_Lean_Meta_Grind_instInhabitedGoalM___redArg();
lean_object* l_instInhabitedReaderT___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_getNodeId___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_mkLePreorderPrefix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_mkOrdRingPrefix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
lean_object* lean_grind_mk_eq_proof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getDecLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_synthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_UInt64_ofNat___boxed(lean_object*);
lean_object* l_instHashableProd___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instDecidableEqNat___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instBEqProd___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__1;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__2_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__3_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__4_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__5_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt64_ofNat___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__6_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instHashableProd___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__6_value),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__6_value)} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__7_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__8;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__9;
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
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isShorter___redArg(lean_object* v_u_553_, lean_object* v_v_554_, lean_object* v_k_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_){
_start:
{
lean_object* v___x_560_; 
v___x_560_ = l_Lean_Meta_Grind_Order_getDist_x3f___redArg(v_u_553_, v_v_554_, v_a_556_, v_a_557_, v_a_558_);
if (lean_obj_tag(v___x_560_) == 0)
{
lean_object* v_a_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_580_; 
v_a_561_ = lean_ctor_get(v___x_560_, 0);
v_isSharedCheck_580_ = !lean_is_exclusive(v___x_560_);
if (v_isSharedCheck_580_ == 0)
{
v___x_563_ = v___x_560_;
v_isShared_564_ = v_isSharedCheck_580_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_a_561_);
lean_dec(v___x_560_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_580_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
if (lean_obj_tag(v_a_561_) == 1)
{
lean_object* v_val_565_; uint8_t v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; uint8_t v___x_570_; lean_object* v___x_571_; lean_object* v___x_573_; 
v_val_565_ = lean_ctor_get(v_a_561_, 0);
lean_inc(v_val_565_);
lean_dec_ref_known(v_a_561_, 1);
v___x_566_ = l_Lean_Meta_Grind_Order_Weight_compare(v_k_555_, v_val_565_);
lean_dec(v_val_565_);
v___x_567_ = lean_box(v___x_566_);
v___x_568_ = lean_obj_tag_nat(v___x_567_);
lean_dec(v___x_567_);
v___x_569_ = lean_unsigned_to_nat(0u);
v___x_570_ = lean_nat_dec_eq(v___x_568_, v___x_569_);
v___x_571_ = lean_box(v___x_570_);
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 0, v___x_571_);
v___x_573_ = v___x_563_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v___x_571_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
return v___x_573_;
}
}
else
{
uint8_t v___x_575_; lean_object* v___x_576_; lean_object* v___x_578_; 
lean_dec(v_a_561_);
v___x_575_ = 1;
v___x_576_ = lean_box(v___x_575_);
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 0, v___x_576_);
v___x_578_ = v___x_563_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v___x_576_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
}
}
else
{
lean_object* v_a_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_588_; 
v_a_581_ = lean_ctor_get(v___x_560_, 0);
v_isSharedCheck_588_ = !lean_is_exclusive(v___x_560_);
if (v_isSharedCheck_588_ == 0)
{
v___x_583_ = v___x_560_;
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_a_581_);
lean_dec(v___x_560_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_586_; 
if (v_isShared_584_ == 0)
{
v___x_586_ = v___x_583_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_a_581_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isShorter___redArg___boxed(lean_object* v_u_589_, lean_object* v_v_590_, lean_object* v_k_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isShorter___redArg(v_u_589_, v_v_590_, v_k_591_, v_a_592_, v_a_593_, v_a_594_);
lean_dec_ref(v_a_594_);
lean_dec(v_a_593_);
lean_dec(v_a_592_);
lean_dec_ref(v_k_591_);
lean_dec(v_v_590_);
lean_dec(v_u_589_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isShorter(lean_object* v_u_597_, lean_object* v_v_598_, lean_object* v_k_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_){
_start:
{
lean_object* v___x_612_; 
v___x_612_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isShorter___redArg(v_u_597_, v_v_598_, v_k_599_, v_a_600_, v_a_601_, v_a_609_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isShorter___boxed(lean_object* v_u_613_, lean_object* v_v_614_, lean_object* v_k_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isShorter(v_u_613_, v_v_614_, v_k_615_, v_a_616_, v_a_617_, v_a_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_);
lean_dec(v_a_626_);
lean_dec_ref(v_a_625_);
lean_dec(v_a_624_);
lean_dec_ref(v_a_623_);
lean_dec(v_a_622_);
lean_dec_ref(v_a_621_);
lean_dec(v_a_620_);
lean_dec_ref(v_a_619_);
lean_dec(v_a_618_);
lean_dec(v_a_617_);
lean_dec(v_a_616_);
lean_dec_ref(v_k_615_);
lean_dec(v_v_614_);
lean_dec(v_u_613_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___lam__0(lean_object* v_p_629_, lean_object* v_s_630_){
_start:
{
lean_object* v_id_631_; lean_object* v_nodes_632_; lean_object* v_nodeMap_633_; lean_object* v_cnstrs_634_; lean_object* v_cnstrsOf_635_; lean_object* v_sources_636_; lean_object* v_targets_637_; lean_object* v_proofs_638_; lean_object* v_propagate_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_647_; 
v_id_631_ = lean_ctor_get(v_s_630_, 0);
v_nodes_632_ = lean_ctor_get(v_s_630_, 1);
v_nodeMap_633_ = lean_ctor_get(v_s_630_, 2);
v_cnstrs_634_ = lean_ctor_get(v_s_630_, 3);
v_cnstrsOf_635_ = lean_ctor_get(v_s_630_, 4);
v_sources_636_ = lean_ctor_get(v_s_630_, 5);
v_targets_637_ = lean_ctor_get(v_s_630_, 6);
v_proofs_638_ = lean_ctor_get(v_s_630_, 7);
v_propagate_639_ = lean_ctor_get(v_s_630_, 8);
v_isSharedCheck_647_ = !lean_is_exclusive(v_s_630_);
if (v_isSharedCheck_647_ == 0)
{
v___x_641_ = v_s_630_;
v_isShared_642_ = v_isSharedCheck_647_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_propagate_639_);
lean_inc(v_proofs_638_);
lean_inc(v_targets_637_);
lean_inc(v_sources_636_);
lean_inc(v_cnstrsOf_635_);
lean_inc(v_cnstrs_634_);
lean_inc(v_nodeMap_633_);
lean_inc(v_nodes_632_);
lean_inc(v_id_631_);
lean_dec(v_s_630_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_647_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_643_; lean_object* v___x_645_; 
v___x_643_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_643_, 0, v_p_629_);
lean_ctor_set(v___x_643_, 1, v_propagate_639_);
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 8, v___x_643_);
v___x_645_ = v___x_641_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_id_631_);
lean_ctor_set(v_reuseFailAlloc_646_, 1, v_nodes_632_);
lean_ctor_set(v_reuseFailAlloc_646_, 2, v_nodeMap_633_);
lean_ctor_set(v_reuseFailAlloc_646_, 3, v_cnstrs_634_);
lean_ctor_set(v_reuseFailAlloc_646_, 4, v_cnstrsOf_635_);
lean_ctor_set(v_reuseFailAlloc_646_, 5, v_sources_636_);
lean_ctor_set(v_reuseFailAlloc_646_, 6, v_targets_637_);
lean_ctor_set(v_reuseFailAlloc_646_, 7, v_proofs_638_);
lean_ctor_set(v_reuseFailAlloc_646_, 8, v___x_643_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0_spec__0(lean_object* v_msgData_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_){
_start:
{
lean_object* v___x_654_; lean_object* v_env_655_; uint8_t v___x_656_; lean_object* v_env_657_; lean_object* v___x_658_; lean_object* v_toCold_659_; lean_object* v_mctx_660_; lean_object* v_lctx_661_; lean_object* v_options_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_654_ = lean_st_ref_get(v___y_652_);
v_env_655_ = lean_ctor_get(v___x_654_, 0);
lean_inc_ref(v_env_655_);
lean_dec(v___x_654_);
v___x_656_ = 0;
v_env_657_ = l_Lean_Environment_setRecordingDeps(v_env_655_, v___x_656_);
v___x_658_ = lean_st_ref_get(v___y_650_);
v_toCold_659_ = lean_ctor_get(v___y_651_, 0);
v_mctx_660_ = lean_ctor_get(v___x_658_, 0);
lean_inc_ref(v_mctx_660_);
lean_dec(v___x_658_);
v_lctx_661_ = lean_ctor_get(v___y_649_, 2);
v_options_662_ = lean_ctor_get(v_toCold_659_, 2);
lean_inc_ref(v_options_662_);
lean_inc_ref(v_lctx_661_);
v___x_663_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_663_, 0, v_env_657_);
lean_ctor_set(v___x_663_, 1, v_mctx_660_);
lean_ctor_set(v___x_663_, 2, v_lctx_661_);
lean_ctor_set(v___x_663_, 3, v_options_662_);
v___x_664_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_664_, 0, v___x_663_);
lean_ctor_set(v___x_664_, 1, v_msgData_648_);
v___x_665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_665_, 0, v___x_664_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0_spec__0___boxed(lean_object* v_msgData_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_){
_start:
{
lean_object* v_res_672_; 
v_res_672_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0_spec__0(v_msgData_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_);
lean_dec(v___y_670_);
lean_dec_ref(v___y_669_);
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
return v_res_672_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_673_; double v___x_674_; 
v___x_673_ = lean_unsigned_to_nat(0u);
v___x_674_ = lean_float_of_nat(v___x_673_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(lean_object* v_cls_678_, lean_object* v_msg_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_){
_start:
{
lean_object* v_ref_685_; lean_object* v___x_686_; lean_object* v_a_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_732_; 
v_ref_685_ = lean_ctor_get(v___y_682_, 2);
v___x_686_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0_spec__0(v_msg_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_);
v_a_687_ = lean_ctor_get(v___x_686_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_686_);
if (v_isSharedCheck_732_ == 0)
{
v___x_689_ = v___x_686_;
v_isShared_690_ = v_isSharedCheck_732_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_a_687_);
lean_dec(v___x_686_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_732_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v___x_691_; lean_object* v_traceState_692_; lean_object* v_env_693_; lean_object* v_nextMacroScope_694_; lean_object* v_ngen_695_; lean_object* v_auxDeclNGen_696_; lean_object* v_cache_697_; lean_object* v_recordedDeps_698_; lean_object* v_messages_699_; lean_object* v_infoState_700_; lean_object* v_snapshotTasks_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_731_; 
v___x_691_ = lean_st_ref_take(v___y_683_);
v_traceState_692_ = lean_ctor_get(v___x_691_, 4);
v_env_693_ = lean_ctor_get(v___x_691_, 0);
v_nextMacroScope_694_ = lean_ctor_get(v___x_691_, 1);
v_ngen_695_ = lean_ctor_get(v___x_691_, 2);
v_auxDeclNGen_696_ = lean_ctor_get(v___x_691_, 3);
v_cache_697_ = lean_ctor_get(v___x_691_, 5);
v_recordedDeps_698_ = lean_ctor_get(v___x_691_, 6);
v_messages_699_ = lean_ctor_get(v___x_691_, 7);
v_infoState_700_ = lean_ctor_get(v___x_691_, 8);
v_snapshotTasks_701_ = lean_ctor_get(v___x_691_, 9);
v_isSharedCheck_731_ = !lean_is_exclusive(v___x_691_);
if (v_isSharedCheck_731_ == 0)
{
v___x_703_ = v___x_691_;
v_isShared_704_ = v_isSharedCheck_731_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_snapshotTasks_701_);
lean_inc(v_infoState_700_);
lean_inc(v_messages_699_);
lean_inc(v_recordedDeps_698_);
lean_inc(v_cache_697_);
lean_inc(v_traceState_692_);
lean_inc(v_auxDeclNGen_696_);
lean_inc(v_ngen_695_);
lean_inc(v_nextMacroScope_694_);
lean_inc(v_env_693_);
lean_dec(v___x_691_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_731_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
uint64_t v_tid_705_; lean_object* v_traces_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_730_; 
v_tid_705_ = lean_ctor_get_uint64(v_traceState_692_, sizeof(void*)*1);
v_traces_706_ = lean_ctor_get(v_traceState_692_, 0);
v_isSharedCheck_730_ = !lean_is_exclusive(v_traceState_692_);
if (v_isSharedCheck_730_ == 0)
{
v___x_708_ = v_traceState_692_;
v_isShared_709_ = v_isSharedCheck_730_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_traces_706_);
lean_dec(v_traceState_692_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_730_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_710_; lean_object* v___x_711_; double v___x_712_; uint8_t v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_721_; 
v___x_710_ = lean_box(0);
v___x_711_ = lean_box(0);
v___x_712_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg___closed__0);
v___x_713_ = 0;
v___x_714_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg___closed__1));
v___x_715_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_715_, 0, v_cls_678_);
lean_ctor_set(v___x_715_, 1, v___x_711_);
lean_ctor_set(v___x_715_, 2, v___x_714_);
lean_ctor_set_float(v___x_715_, sizeof(void*)*3, v___x_712_);
lean_ctor_set_float(v___x_715_, sizeof(void*)*3 + 8, v___x_712_);
lean_ctor_set_uint8(v___x_715_, sizeof(void*)*3 + 16, v___x_713_);
v___x_716_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg___closed__2));
v___x_717_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_717_, 0, v___x_715_);
lean_ctor_set(v___x_717_, 1, v_a_687_);
lean_ctor_set(v___x_717_, 2, v___x_716_);
lean_inc(v_ref_685_);
v___x_718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_718_, 0, v_ref_685_);
lean_ctor_set(v___x_718_, 1, v___x_717_);
v___x_719_ = l_Lean_PersistentArray_push___redArg(v_traces_706_, v___x_718_);
if (v_isShared_709_ == 0)
{
lean_ctor_set(v___x_708_, 0, v___x_719_);
v___x_721_ = v___x_708_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v___x_719_);
lean_ctor_set_uint64(v_reuseFailAlloc_729_, sizeof(void*)*1, v_tid_705_);
v___x_721_ = v_reuseFailAlloc_729_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
lean_object* v___x_723_; 
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 4, v___x_721_);
v___x_723_ = v___x_703_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_env_693_);
lean_ctor_set(v_reuseFailAlloc_728_, 1, v_nextMacroScope_694_);
lean_ctor_set(v_reuseFailAlloc_728_, 2, v_ngen_695_);
lean_ctor_set(v_reuseFailAlloc_728_, 3, v_auxDeclNGen_696_);
lean_ctor_set(v_reuseFailAlloc_728_, 4, v___x_721_);
lean_ctor_set(v_reuseFailAlloc_728_, 5, v_cache_697_);
lean_ctor_set(v_reuseFailAlloc_728_, 6, v_recordedDeps_698_);
lean_ctor_set(v_reuseFailAlloc_728_, 7, v_messages_699_);
lean_ctor_set(v_reuseFailAlloc_728_, 8, v_infoState_700_);
lean_ctor_set(v_reuseFailAlloc_728_, 9, v_snapshotTasks_701_);
v___x_723_ = v_reuseFailAlloc_728_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
lean_object* v___x_724_; lean_object* v___x_726_; 
v___x_724_ = lean_st_ref_put(v___y_683_, v___x_723_);
if (v_isShared_690_ == 0)
{
lean_ctor_set(v___x_689_, 0, v___x_710_);
v___x_726_ = v___x_689_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v___x_710_);
v___x_726_ = v_reuseFailAlloc_727_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
return v___x_726_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg___boxed(lean_object* v_cls_733_, lean_object* v_msg_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_){
_start:
{
lean_object* v_res_740_; 
v_res_740_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(v_cls_733_, v_msg_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_);
lean_dec(v___y_738_);
lean_dec_ref(v___y_737_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
return v_res_740_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__7(void){
_start:
{
lean_object* v_cls_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
v_cls_753_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__4));
v___x_754_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__6));
v___x_755_ = l_Lean_Name_append(v___x_754_, v_cls_753_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate(lean_object* v_p_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_){
_start:
{
lean_object* v_toCold_769_; lean_object* v_options_770_; lean_object* v_inheritedTraceOptions_771_; uint8_t v_hasTrace_772_; lean_object* v___f_773_; 
v_toCold_769_ = lean_ctor_get(v_a_766_, 0);
v_options_770_ = lean_ctor_get(v_toCold_769_, 2);
v_inheritedTraceOptions_771_ = lean_ctor_get(v_toCold_769_, 11);
v_hasTrace_772_ = lean_ctor_get_uint8(v_options_770_, sizeof(void*)*1);
lean_inc_ref(v_p_756_);
v___f_773_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___lam__0), 2, 1);
lean_closure_set(v___f_773_, 0, v_p_756_);
if (v_hasTrace_772_ == 0)
{
lean_object* v___x_774_; 
lean_dec_ref(v_p_756_);
v___x_774_ = l_Lean_Meta_Grind_Order_modifyStruct___redArg(v___f_773_, v_a_757_, v_a_758_);
return v___x_774_;
}
else
{
lean_object* v_cls_775_; lean_object* v___x_776_; uint8_t v___x_777_; 
v_cls_775_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__4));
v___x_776_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__7, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__7);
v___x_777_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_771_, v_options_770_, v___x_776_);
if (v___x_777_ == 0)
{
lean_object* v___x_778_; 
lean_dec_ref(v_p_756_);
v___x_778_ = l_Lean_Meta_Grind_Order_modifyStruct___redArg(v___f_773_, v_a_757_, v_a_758_);
return v___x_778_;
}
else
{
lean_object* v___x_779_; 
v___x_779_ = l_Lean_Meta_Grind_Order_ToPropagate_pp___redArg(v_p_756_, v_a_757_, v_a_758_, v_a_766_);
if (lean_obj_tag(v___x_779_) == 0)
{
lean_object* v_a_780_; lean_object* v___x_781_; 
v_a_780_ = lean_ctor_get(v___x_779_, 0);
lean_inc(v_a_780_);
lean_dec_ref_known(v___x_779_, 1);
v___x_781_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(v_cls_775_, v_a_780_, v_a_764_, v_a_765_, v_a_766_, v_a_767_);
if (lean_obj_tag(v___x_781_) == 0)
{
lean_object* v___x_782_; 
lean_dec_ref_known(v___x_781_, 1);
v___x_782_ = l_Lean_Meta_Grind_Order_modifyStruct___redArg(v___f_773_, v_a_757_, v_a_758_);
return v___x_782_;
}
else
{
lean_dec_ref(v___f_773_);
return v___x_781_;
}
}
else
{
lean_object* v_a_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_790_; 
lean_dec_ref(v___f_773_);
v_a_783_ = lean_ctor_get(v___x_779_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_790_ == 0)
{
v___x_785_ = v___x_779_;
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_a_783_);
lean_dec(v___x_779_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_788_; 
if (v_isShared_786_ == 0)
{
v___x_788_ = v___x_785_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_a_783_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___boxed(lean_object* v_p_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate(v_p_791_, v_a_792_, v_a_793_, v_a_794_, v_a_795_, v_a_796_, v_a_797_, v_a_798_, v_a_799_, v_a_800_, v_a_801_, v_a_802_);
lean_dec(v_a_802_);
lean_dec_ref(v_a_801_);
lean_dec(v_a_800_);
lean_dec_ref(v_a_799_);
lean_dec(v_a_798_);
lean_dec_ref(v_a_797_);
lean_dec(v_a_796_);
lean_dec_ref(v_a_795_);
lean_dec(v_a_794_);
lean_dec(v_a_793_);
lean_dec(v_a_792_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0(lean_object* v_cls_805_, lean_object* v_msg_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_){
_start:
{
lean_object* v___x_819_; 
v___x_819_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(v_cls_805_, v_msg_806_, v___y_814_, v___y_815_, v___y_816_, v___y_817_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___boxed(lean_object* v_cls_820_, lean_object* v_msg_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_){
_start:
{
lean_object* v_res_834_; 
v_res_834_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0(v_cls_820_, v_msg_821_, v___y_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_);
lean_dec(v___y_832_);
lean_dec_ref(v___y_831_);
lean_dec(v___y_830_);
lean_dec_ref(v___y_829_);
lean_dec(v___y_828_);
lean_dec_ref(v___y_827_);
lean_dec(v___y_826_);
lean_dec_ref(v___y_825_);
lean_dec(v___y_824_);
lean_dec(v___y_823_);
lean_dec(v___y_822_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_835_, lean_object* v_vals_836_, lean_object* v_i_837_, lean_object* v_k_838_){
_start:
{
lean_object* v___x_839_; uint8_t v___x_840_; 
v___x_839_ = lean_array_get_size(v_keys_835_);
v___x_840_ = lean_nat_dec_lt(v_i_837_, v___x_839_);
if (v___x_840_ == 0)
{
lean_object* v___x_841_; 
lean_dec(v_i_837_);
v___x_841_ = lean_box(0);
return v___x_841_;
}
else
{
lean_object* v_k_x27_842_; size_t v___x_843_; size_t v___x_844_; uint8_t v___x_845_; 
v_k_x27_842_ = lean_array_fget_borrowed(v_keys_835_, v_i_837_);
v___x_843_ = lean_ptr_addr(v_k_838_);
v___x_844_ = lean_ptr_addr(v_k_x27_842_);
v___x_845_ = lean_usize_dec_eq(v___x_843_, v___x_844_);
if (v___x_845_ == 0)
{
lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_846_ = lean_unsigned_to_nat(1u);
v___x_847_ = lean_nat_add(v_i_837_, v___x_846_);
lean_dec(v_i_837_);
v_i_837_ = v___x_847_;
goto _start;
}
else
{
lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_849_ = lean_array_fget_borrowed(v_vals_836_, v_i_837_);
lean_dec(v_i_837_);
lean_inc(v___x_849_);
v___x_850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_850_, 0, v___x_849_);
return v___x_850_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_851_, lean_object* v_vals_852_, lean_object* v_i_853_, lean_object* v_k_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0_spec__1___redArg(v_keys_851_, v_vals_852_, v_i_853_, v_k_854_);
lean_dec_ref(v_k_854_);
lean_dec_ref(v_vals_852_);
lean_dec_ref(v_keys_851_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg(lean_object* v_x_856_, size_t v_x_857_, lean_object* v_x_858_){
_start:
{
if (lean_obj_tag(v_x_856_) == 0)
{
lean_object* v_es_859_; lean_object* v___x_860_; size_t v___x_861_; size_t v___x_862_; lean_object* v_j_863_; lean_object* v___x_864_; 
v_es_859_ = lean_ctor_get(v_x_856_, 0);
v___x_860_ = lean_box(2);
v___x_861_ = ((size_t)31ULL);
v___x_862_ = lean_usize_land(v_x_857_, v___x_861_);
v_j_863_ = lean_usize_to_nat(v___x_862_);
v___x_864_ = lean_array_get_borrowed(v___x_860_, v_es_859_, v_j_863_);
lean_dec(v_j_863_);
switch(lean_obj_tag(v___x_864_))
{
case 0:
{
lean_object* v_key_865_; lean_object* v_val_866_; size_t v___x_867_; size_t v___x_868_; uint8_t v___x_869_; 
v_key_865_ = lean_ctor_get(v___x_864_, 0);
v_val_866_ = lean_ctor_get(v___x_864_, 1);
v___x_867_ = lean_ptr_addr(v_x_858_);
v___x_868_ = lean_ptr_addr(v_key_865_);
v___x_869_ = lean_usize_dec_eq(v___x_867_, v___x_868_);
if (v___x_869_ == 0)
{
lean_object* v___x_870_; 
v___x_870_ = lean_box(0);
return v___x_870_;
}
else
{
lean_object* v___x_871_; 
lean_inc(v_val_866_);
v___x_871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_871_, 0, v_val_866_);
return v___x_871_;
}
}
case 1:
{
lean_object* v_node_872_; size_t v___x_873_; size_t v___x_874_; 
v_node_872_ = lean_ctor_get(v___x_864_, 0);
v___x_873_ = ((size_t)5ULL);
v___x_874_ = lean_usize_shift_right(v_x_857_, v___x_873_);
v_x_856_ = v_node_872_;
v_x_857_ = v___x_874_;
goto _start;
}
default: 
{
lean_object* v___x_876_; 
v___x_876_ = lean_box(0);
return v___x_876_;
}
}
}
else
{
lean_object* v_ks_877_; lean_object* v_vs_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
v_ks_877_ = lean_ctor_get(v_x_856_, 0);
v_vs_878_ = lean_ctor_get(v_x_856_, 1);
v___x_879_ = lean_unsigned_to_nat(0u);
v___x_880_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0_spec__1___redArg(v_ks_877_, v_vs_878_, v___x_879_, v_x_858_);
return v___x_880_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg___boxed(lean_object* v_x_881_, lean_object* v_x_882_, lean_object* v_x_883_){
_start:
{
size_t v_x_9901__boxed_884_; lean_object* v_res_885_; 
v_x_9901__boxed_884_ = lean_unbox_usize(v_x_882_);
lean_dec(v_x_882_);
v_res_885_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg(v_x_881_, v_x_9901__boxed_884_, v_x_883_);
lean_dec_ref(v_x_883_);
lean_dec_ref(v_x_881_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(lean_object* v_x_886_, lean_object* v_x_887_){
_start:
{
size_t v___x_888_; size_t v___x_889_; size_t v___x_890_; uint64_t v___x_891_; size_t v___x_892_; lean_object* v___x_893_; 
v___x_888_ = lean_ptr_addr(v_x_887_);
v___x_889_ = ((size_t)3ULL);
v___x_890_ = lean_usize_shift_right(v___x_888_, v___x_889_);
v___x_891_ = lean_usize_to_uint64(v___x_890_);
v___x_892_ = lean_uint64_to_usize(v___x_891_);
v___x_893_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg(v_x_886_, v___x_892_, v_x_887_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg___boxed(lean_object* v_x_894_, lean_object* v_x_895_){
_start:
{
lean_object* v_res_896_; 
v_res_896_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_x_894_, v_x_895_);
lean_dec_ref(v_x_895_);
lean_dec_ref(v_x_894_);
return v_res_896_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5(void){
_start:
{
lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_906_ = lean_box(0);
v___x_907_ = ((lean_object*)(l_Lean_Meta_Grind_Order_propagateEqTrue___closed__4));
v___x_908_ = l_Lean_mkConst(v___x_907_, v___x_906_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateEqTrue(lean_object* v_c_909_, lean_object* v_e_910_, lean_object* v_u_911_, lean_object* v_v_912_, lean_object* v_k_913_, lean_object* v_k_x27_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_){
_start:
{
lean_object* v_h_928_; lean_object* v___y_929_; lean_object* v___y_930_; lean_object* v___y_931_; lean_object* v___y_932_; lean_object* v___y_933_; lean_object* v___y_934_; lean_object* v___y_935_; lean_object* v___x_955_; 
v___x_955_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath(v_u_911_, v_v_912_, v_a_915_, v_a_916_, v_a_917_, v_a_918_, v_a_919_, v_a_920_, v_a_921_, v_a_922_, v_a_923_, v_a_924_, v_a_925_);
if (lean_obj_tag(v___x_955_) == 0)
{
lean_object* v_a_956_; lean_object* v___x_957_; 
v_a_956_ = lean_ctor_get(v___x_955_, 0);
lean_inc(v_a_956_);
lean_dec_ref_known(v___x_955_, 1);
v___x_957_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_u_911_, v_a_915_, v_a_916_, v_a_924_);
if (lean_obj_tag(v___x_957_) == 0)
{
lean_object* v_a_958_; lean_object* v___x_959_; 
v_a_958_ = lean_ctor_get(v___x_957_, 0);
lean_inc(v_a_958_);
lean_dec_ref_known(v___x_957_, 1);
v___x_959_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_v_912_, v_a_915_, v_a_916_, v_a_924_);
if (lean_obj_tag(v___x_959_) == 0)
{
lean_object* v_a_960_; lean_object* v___x_961_; 
v_a_960_ = lean_ctor_get(v___x_959_, 0);
lean_inc(v_a_960_);
lean_dec_ref_known(v___x_959_, 1);
v___x_961_ = l_Lean_Meta_Grind_Order_mkPropagateEqTrueProof(v_a_958_, v_a_960_, v_k_913_, v_a_956_, v_k_x27_914_, v_a_915_, v_a_916_, v_a_917_, v_a_918_, v_a_919_, v_a_920_, v_a_921_, v_a_922_, v_a_923_, v_a_924_, v_a_925_);
if (lean_obj_tag(v___x_961_) == 0)
{
lean_object* v_h_x3f_962_; 
v_h_x3f_962_ = lean_ctor_get(v_c_909_, 4);
lean_inc(v_h_x3f_962_);
if (lean_obj_tag(v_h_x3f_962_) == 1)
{
lean_object* v_a_963_; lean_object* v_e_964_; lean_object* v_val_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
v_a_963_ = lean_ctor_get(v___x_961_, 0);
lean_inc(v_a_963_);
lean_dec_ref_known(v___x_961_, 1);
v_e_964_ = lean_ctor_get(v_c_909_, 3);
lean_inc_ref(v_e_964_);
lean_dec_ref(v_c_909_);
v_val_965_ = lean_ctor_get(v_h_x3f_962_, 0);
lean_inc(v_val_965_);
lean_dec_ref_known(v_h_x3f_962_, 1);
v___x_966_ = lean_obj_once(&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5, &l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5_once, _init_l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5);
lean_inc_ref(v_e_910_);
v___x_967_ = l_Lean_mkApp4(v___x_966_, v_e_910_, v_e_964_, v_val_965_, v_a_963_);
v_h_928_ = v___x_967_;
v___y_929_ = v_a_916_;
v___y_930_ = v_a_918_;
v___y_931_ = v_a_920_;
v___y_932_ = v_a_922_;
v___y_933_ = v_a_923_;
v___y_934_ = v_a_924_;
v___y_935_ = v_a_925_;
goto v___jp_927_;
}
else
{
lean_object* v_a_968_; 
lean_dec(v_h_x3f_962_);
lean_dec_ref(v_c_909_);
v_a_968_ = lean_ctor_get(v___x_961_, 0);
lean_inc(v_a_968_);
lean_dec_ref_known(v___x_961_, 1);
v_h_928_ = v_a_968_;
v___y_929_ = v_a_916_;
v___y_930_ = v_a_918_;
v___y_931_ = v_a_920_;
v___y_932_ = v_a_922_;
v___y_933_ = v_a_923_;
v___y_934_ = v_a_924_;
v___y_935_ = v_a_925_;
goto v___jp_927_;
}
}
else
{
lean_object* v_a_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_976_; 
lean_dec_ref(v_e_910_);
lean_dec_ref(v_c_909_);
v_a_969_ = lean_ctor_get(v___x_961_, 0);
v_isSharedCheck_976_ = !lean_is_exclusive(v___x_961_);
if (v_isSharedCheck_976_ == 0)
{
v___x_971_ = v___x_961_;
v_isShared_972_ = v_isSharedCheck_976_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_a_969_);
lean_dec(v___x_961_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_976_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___x_974_; 
if (v_isShared_972_ == 0)
{
v___x_974_ = v___x_971_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v_a_969_);
v___x_974_ = v_reuseFailAlloc_975_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
return v___x_974_;
}
}
}
}
else
{
lean_object* v_a_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_984_; 
lean_dec(v_a_958_);
lean_dec(v_a_956_);
lean_dec_ref(v_e_910_);
lean_dec_ref(v_c_909_);
v_a_977_ = lean_ctor_get(v___x_959_, 0);
v_isSharedCheck_984_ = !lean_is_exclusive(v___x_959_);
if (v_isSharedCheck_984_ == 0)
{
v___x_979_ = v___x_959_;
v_isShared_980_ = v_isSharedCheck_984_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_a_977_);
lean_dec(v___x_959_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_984_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v___x_982_; 
if (v_isShared_980_ == 0)
{
v___x_982_ = v___x_979_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v_a_977_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
return v___x_982_;
}
}
}
}
else
{
lean_object* v_a_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_992_; 
lean_dec(v_a_956_);
lean_dec_ref(v_e_910_);
lean_dec_ref(v_c_909_);
v_a_985_ = lean_ctor_get(v___x_957_, 0);
v_isSharedCheck_992_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_992_ == 0)
{
v___x_987_ = v___x_957_;
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_a_985_);
lean_dec(v___x_957_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_990_; 
if (v_isShared_988_ == 0)
{
v___x_990_ = v___x_987_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v_a_985_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
return v___x_990_;
}
}
}
}
else
{
lean_object* v_a_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1000_; 
lean_dec_ref(v_e_910_);
lean_dec_ref(v_c_909_);
v_a_993_ = lean_ctor_get(v___x_955_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_955_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_995_ = v___x_955_;
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_a_993_);
lean_dec(v___x_955_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_998_; 
if (v_isShared_996_ == 0)
{
v___x_998_ = v___x_995_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_a_993_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
}
v___jp_927_:
{
lean_object* v___x_936_; 
v___x_936_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v___y_929_, v___y_934_);
if (lean_obj_tag(v___x_936_) == 0)
{
lean_object* v_a_937_; lean_object* v_termMapInv_938_; lean_object* v___x_939_; 
v_a_937_ = lean_ctor_get(v___x_936_, 0);
lean_inc(v_a_937_);
lean_dec_ref_known(v___x_936_, 1);
v_termMapInv_938_ = lean_ctor_get(v_a_937_, 4);
lean_inc_ref(v_termMapInv_938_);
lean_dec(v_a_937_);
v___x_939_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMapInv_938_, v_e_910_);
lean_dec_ref(v_termMapInv_938_);
if (lean_obj_tag(v___x_939_) == 1)
{
lean_object* v_val_940_; lean_object* v_fst_941_; lean_object* v_snd_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
v_val_940_ = lean_ctor_get(v___x_939_, 0);
lean_inc(v_val_940_);
lean_dec_ref_known(v___x_939_, 1);
v_fst_941_ = lean_ctor_get(v_val_940_, 0);
lean_inc_n(v_fst_941_, 2);
v_snd_942_ = lean_ctor_get(v_val_940_, 1);
lean_inc(v_snd_942_);
lean_dec(v_val_940_);
v___x_943_ = lean_obj_once(&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5, &l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5_once, _init_l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5);
v___x_944_ = l_Lean_mkApp4(v___x_943_, v_fst_941_, v_e_910_, v_snd_942_, v_h_928_);
v___x_945_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_fst_941_, v___x_944_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
return v___x_945_;
}
else
{
lean_object* v___x_946_; 
lean_dec(v___x_939_);
v___x_946_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_e_910_, v_h_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
return v___x_946_;
}
}
else
{
lean_object* v_a_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_954_; 
lean_dec_ref(v_h_928_);
lean_dec_ref(v_e_910_);
v_a_947_ = lean_ctor_get(v___x_936_, 0);
v_isSharedCheck_954_ = !lean_is_exclusive(v___x_936_);
if (v_isSharedCheck_954_ == 0)
{
v___x_949_ = v___x_936_;
v_isShared_950_ = v_isSharedCheck_954_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_a_947_);
lean_dec(v___x_936_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_954_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v___x_952_; 
if (v_isShared_950_ == 0)
{
v___x_952_ = v___x_949_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v_a_947_);
v___x_952_ = v_reuseFailAlloc_953_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
return v___x_952_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateEqTrue___boxed(lean_object** _args){
lean_object* v_c_1001_ = _args[0];
lean_object* v_e_1002_ = _args[1];
lean_object* v_u_1003_ = _args[2];
lean_object* v_v_1004_ = _args[3];
lean_object* v_k_1005_ = _args[4];
lean_object* v_k_x27_1006_ = _args[5];
lean_object* v_a_1007_ = _args[6];
lean_object* v_a_1008_ = _args[7];
lean_object* v_a_1009_ = _args[8];
lean_object* v_a_1010_ = _args[9];
lean_object* v_a_1011_ = _args[10];
lean_object* v_a_1012_ = _args[11];
lean_object* v_a_1013_ = _args[12];
lean_object* v_a_1014_ = _args[13];
lean_object* v_a_1015_ = _args[14];
lean_object* v_a_1016_ = _args[15];
lean_object* v_a_1017_ = _args[16];
lean_object* v_a_1018_ = _args[17];
_start:
{
lean_object* v_res_1019_; 
v_res_1019_ = l_Lean_Meta_Grind_Order_propagateEqTrue(v_c_1001_, v_e_1002_, v_u_1003_, v_v_1004_, v_k_1005_, v_k_x27_1006_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_);
lean_dec(v_a_1017_);
lean_dec_ref(v_a_1016_);
lean_dec(v_a_1015_);
lean_dec_ref(v_a_1014_);
lean_dec(v_a_1013_);
lean_dec_ref(v_a_1012_);
lean_dec(v_a_1011_);
lean_dec_ref(v_a_1010_);
lean_dec(v_a_1009_);
lean_dec(v_a_1008_);
lean_dec(v_a_1007_);
lean_dec_ref(v_k_x27_1006_);
lean_dec_ref(v_k_1005_);
lean_dec(v_v_1004_);
lean_dec(v_u_1003_);
return v_res_1019_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0(lean_object* v_00_u03b2_1020_, lean_object* v_x_1021_, lean_object* v_x_1022_){
_start:
{
lean_object* v___x_1023_; 
v___x_1023_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_x_1021_, v_x_1022_);
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___boxed(lean_object* v_00_u03b2_1024_, lean_object* v_x_1025_, lean_object* v_x_1026_){
_start:
{
lean_object* v_res_1027_; 
v_res_1027_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0(v_00_u03b2_1024_, v_x_1025_, v_x_1026_);
lean_dec_ref(v_x_1026_);
lean_dec_ref(v_x_1025_);
return v_res_1027_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0(lean_object* v_00_u03b2_1028_, lean_object* v_x_1029_, size_t v_x_1030_, lean_object* v_x_1031_){
_start:
{
lean_object* v___x_1032_; 
v___x_1032_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg(v_x_1029_, v_x_1030_, v_x_1031_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1033_, lean_object* v_x_1034_, lean_object* v_x_1035_, lean_object* v_x_1036_){
_start:
{
size_t v_x_10169__boxed_1037_; lean_object* v_res_1038_; 
v_x_10169__boxed_1037_ = lean_unbox_usize(v_x_1035_);
lean_dec(v_x_1035_);
v_res_1038_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0(v_00_u03b2_1033_, v_x_1034_, v_x_10169__boxed_1037_, v_x_1036_);
lean_dec_ref(v_x_1036_);
lean_dec_ref(v_x_1034_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1039_, lean_object* v_keys_1040_, lean_object* v_vals_1041_, lean_object* v_heq_1042_, lean_object* v_i_1043_, lean_object* v_k_1044_){
_start:
{
lean_object* v___x_1045_; 
v___x_1045_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0_spec__1___redArg(v_keys_1040_, v_vals_1041_, v_i_1043_, v_k_1044_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1046_, lean_object* v_keys_1047_, lean_object* v_vals_1048_, lean_object* v_heq_1049_, lean_object* v_i_1050_, lean_object* v_k_1051_){
_start:
{
lean_object* v_res_1052_; 
v_res_1052_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0_spec__1(v_00_u03b2_1046_, v_keys_1047_, v_vals_1048_, v_heq_1049_, v_i_1050_, v_k_1051_);
lean_dec_ref(v_k_1051_);
lean_dec_ref(v_vals_1048_);
lean_dec_ref(v_keys_1047_);
return v_res_1052_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1053_; 
v___x_1053_ = l_Lean_Meta_Grind_instInhabitedGoalM___redArg();
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0(lean_object* v_msg_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_){
_start:
{
lean_object* v___x_1067_; lean_object* v___f_1068_; lean_object* v___x_5398__overap_1069_; lean_object* v___x_1070_; 
v___x_1067_ = lean_obj_once(&l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0___closed__0, &l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0___closed__0_once, _init_l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0___closed__0);
v___f_1068_ = lean_alloc_closure((void*)(l_instInhabitedReaderT___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1068_, 0, v___x_1067_);
v___x_5398__overap_1069_ = lean_panic_fn_borrowed(v___f_1068_, v_msg_1054_);
lean_dec_ref(v___f_1068_);
lean_inc(v___y_1065_);
lean_inc_ref(v___y_1064_);
lean_inc(v___y_1063_);
lean_inc_ref(v___y_1062_);
lean_inc(v___y_1061_);
lean_inc_ref(v___y_1060_);
lean_inc(v___y_1059_);
lean_inc_ref(v___y_1058_);
lean_inc(v___y_1057_);
lean_inc(v___y_1056_);
lean_inc(v___y_1055_);
v___x_1070_ = lean_apply_12(v___x_5398__overap_1069_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, lean_box(0));
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0___boxed(lean_object* v_msg_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_){
_start:
{
lean_object* v_res_1084_; 
v_res_1084_ = l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0(v_msg_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_);
lean_dec(v___y_1082_);
lean_dec_ref(v___y_1081_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
lean_dec(v___y_1074_);
lean_dec(v___y_1073_);
lean_dec(v___y_1072_);
return v_res_1084_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__3(void){
_start:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1088_ = ((lean_object*)(l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__2));
v___x_1089_ = lean_unsigned_to_nat(2u);
v___x_1090_ = lean_unsigned_to_nat(80u);
v___x_1091_ = ((lean_object*)(l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__1));
v___x_1092_ = ((lean_object*)(l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__0));
v___x_1093_ = l_mkPanicMessageWithDecl(v___x_1092_, v___x_1091_, v___x_1090_, v___x_1089_, v___x_1088_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateSelfEqTrue(lean_object* v_c_1094_, lean_object* v_e_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_){
_start:
{
lean_object* v_h_1109_; lean_object* v___y_1110_; lean_object* v___y_1111_; lean_object* v___y_1112_; lean_object* v___y_1113_; lean_object* v___y_1114_; lean_object* v___y_1115_; lean_object* v___y_1116_; lean_object* v_u_1136_; lean_object* v_v_1137_; lean_object* v_e_1138_; lean_object* v_h_x3f_1139_; lean_object* v___x_1140_; 
v_u_1136_ = lean_ctor_get(v_c_1094_, 0);
v_v_1137_ = lean_ctor_get(v_c_1094_, 1);
v_e_1138_ = lean_ctor_get(v_c_1094_, 3);
lean_inc_ref(v_e_1138_);
v_h_x3f_1139_ = lean_ctor_get(v_c_1094_, 4);
lean_inc(v_h_x3f_1139_);
v___x_1140_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_u_1136_, v_a_1096_, v_a_1097_, v_a_1105_);
if (lean_obj_tag(v___x_1140_) == 0)
{
lean_object* v_a_1141_; uint8_t v___x_1142_; 
v_a_1141_ = lean_ctor_get(v___x_1140_, 0);
lean_inc(v_a_1141_);
lean_dec_ref_known(v___x_1140_, 1);
v___x_1142_ = lean_nat_dec_eq(v_u_1136_, v_v_1137_);
if (v___x_1142_ == 0)
{
lean_object* v___x_1143_; lean_object* v___x_1144_; 
lean_dec(v_a_1141_);
lean_dec(v_h_x3f_1139_);
lean_dec_ref(v_e_1138_);
lean_dec_ref(v_e_1095_);
lean_dec_ref(v_c_1094_);
v___x_1143_ = lean_obj_once(&l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__3, &l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__3_once, _init_l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__3);
v___x_1144_ = l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0(v___x_1143_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_);
return v___x_1144_;
}
else
{
lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1145_ = l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(v_c_1094_);
lean_dec_ref(v_c_1094_);
v___x_1146_ = l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof(v_a_1141_, v___x_1145_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_);
lean_dec_ref(v___x_1145_);
if (lean_obj_tag(v___x_1146_) == 0)
{
if (lean_obj_tag(v_h_x3f_1139_) == 1)
{
lean_object* v_a_1147_; lean_object* v_val_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; 
v_a_1147_ = lean_ctor_get(v___x_1146_, 0);
lean_inc(v_a_1147_);
lean_dec_ref_known(v___x_1146_, 1);
v_val_1148_ = lean_ctor_get(v_h_x3f_1139_, 0);
lean_inc(v_val_1148_);
lean_dec_ref_known(v_h_x3f_1139_, 1);
v___x_1149_ = lean_obj_once(&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5, &l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5_once, _init_l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5);
lean_inc_ref(v_e_1095_);
v___x_1150_ = l_Lean_mkApp4(v___x_1149_, v_e_1095_, v_e_1138_, v_val_1148_, v_a_1147_);
v_h_1109_ = v___x_1150_;
v___y_1110_ = v_a_1097_;
v___y_1111_ = v_a_1099_;
v___y_1112_ = v_a_1101_;
v___y_1113_ = v_a_1103_;
v___y_1114_ = v_a_1104_;
v___y_1115_ = v_a_1105_;
v___y_1116_ = v_a_1106_;
goto v___jp_1108_;
}
else
{
lean_object* v_a_1151_; 
lean_dec(v_h_x3f_1139_);
lean_dec_ref(v_e_1138_);
v_a_1151_ = lean_ctor_get(v___x_1146_, 0);
lean_inc(v_a_1151_);
lean_dec_ref_known(v___x_1146_, 1);
v_h_1109_ = v_a_1151_;
v___y_1110_ = v_a_1097_;
v___y_1111_ = v_a_1099_;
v___y_1112_ = v_a_1101_;
v___y_1113_ = v_a_1103_;
v___y_1114_ = v_a_1104_;
v___y_1115_ = v_a_1105_;
v___y_1116_ = v_a_1106_;
goto v___jp_1108_;
}
}
else
{
lean_object* v_a_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1159_; 
lean_dec(v_h_x3f_1139_);
lean_dec_ref(v_e_1138_);
lean_dec_ref(v_e_1095_);
v_a_1152_ = lean_ctor_get(v___x_1146_, 0);
v_isSharedCheck_1159_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1154_ = v___x_1146_;
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_a_1152_);
lean_dec(v___x_1146_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1157_; 
if (v_isShared_1155_ == 0)
{
v___x_1157_ = v___x_1154_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_a_1152_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
}
}
else
{
lean_object* v_a_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1167_; 
lean_dec(v_h_x3f_1139_);
lean_dec_ref(v_e_1138_);
lean_dec_ref(v_e_1095_);
lean_dec_ref(v_c_1094_);
v_a_1160_ = lean_ctor_get(v___x_1140_, 0);
v_isSharedCheck_1167_ = !lean_is_exclusive(v___x_1140_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1162_ = v___x_1140_;
v_isShared_1163_ = v_isSharedCheck_1167_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_a_1160_);
lean_dec(v___x_1140_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1167_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1165_; 
if (v_isShared_1163_ == 0)
{
v___x_1165_ = v___x_1162_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_a_1160_);
v___x_1165_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
return v___x_1165_;
}
}
}
v___jp_1108_:
{
lean_object* v___x_1117_; 
v___x_1117_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v___y_1110_, v___y_1115_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_object* v_a_1118_; lean_object* v_termMapInv_1119_; lean_object* v___x_1120_; 
v_a_1118_ = lean_ctor_get(v___x_1117_, 0);
lean_inc(v_a_1118_);
lean_dec_ref_known(v___x_1117_, 1);
v_termMapInv_1119_ = lean_ctor_get(v_a_1118_, 4);
lean_inc_ref(v_termMapInv_1119_);
lean_dec(v_a_1118_);
v___x_1120_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMapInv_1119_, v_e_1095_);
lean_dec_ref(v_termMapInv_1119_);
if (lean_obj_tag(v___x_1120_) == 1)
{
lean_object* v_val_1121_; lean_object* v_fst_1122_; lean_object* v_snd_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
v_val_1121_ = lean_ctor_get(v___x_1120_, 0);
lean_inc(v_val_1121_);
lean_dec_ref_known(v___x_1120_, 1);
v_fst_1122_ = lean_ctor_get(v_val_1121_, 0);
lean_inc_n(v_fst_1122_, 2);
v_snd_1123_ = lean_ctor_get(v_val_1121_, 1);
lean_inc(v_snd_1123_);
lean_dec(v_val_1121_);
v___x_1124_ = lean_obj_once(&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5, &l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5_once, _init_l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5);
v___x_1125_ = l_Lean_mkApp4(v___x_1124_, v_fst_1122_, v_e_1095_, v_snd_1123_, v_h_1109_);
v___x_1126_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_fst_1122_, v___x_1125_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_);
return v___x_1126_;
}
else
{
lean_object* v___x_1127_; 
lean_dec(v___x_1120_);
v___x_1127_ = l_Lean_Meta_Grind_pushEqTrue___redArg(v_e_1095_, v_h_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_);
return v___x_1127_;
}
}
else
{
lean_object* v_a_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1135_; 
lean_dec_ref(v_h_1109_);
lean_dec_ref(v_e_1095_);
v_a_1128_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1135_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1130_ = v___x_1117_;
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_a_1128_);
lean_dec(v___x_1117_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1133_; 
if (v_isShared_1131_ == 0)
{
v___x_1133_ = v___x_1130_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_a_1128_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateSelfEqTrue___boxed(lean_object* v_c_1168_, lean_object* v_e_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_){
_start:
{
lean_object* v_res_1182_; 
v_res_1182_ = l_Lean_Meta_Grind_Order_propagateSelfEqTrue(v_c_1168_, v_e_1169_, v_a_1170_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_);
lean_dec(v_a_1180_);
lean_dec_ref(v_a_1179_);
lean_dec(v_a_1178_);
lean_dec_ref(v_a_1177_);
lean_dec(v_a_1176_);
lean_dec_ref(v_a_1175_);
lean_dec(v_a_1174_);
lean_dec_ref(v_a_1173_);
lean_dec(v_a_1172_);
lean_dec(v_a_1171_);
lean_dec(v_a_1170_);
return v_res_1182_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2(void){
_start:
{
lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1189_ = lean_box(0);
v___x_1190_ = ((lean_object*)(l_Lean_Meta_Grind_Order_propagateEqFalse___closed__1));
v___x_1191_ = l_Lean_mkConst(v___x_1190_, v___x_1189_);
return v___x_1191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateEqFalse(lean_object* v_c_1192_, lean_object* v_e_1193_, lean_object* v_u_1194_, lean_object* v_v_1195_, lean_object* v_k_1196_, lean_object* v_k_x27_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_){
_start:
{
lean_object* v_h_1211_; lean_object* v___y_1212_; lean_object* v___y_1213_; lean_object* v___y_1214_; lean_object* v___y_1215_; lean_object* v___y_1216_; lean_object* v___y_1217_; lean_object* v___y_1218_; lean_object* v___x_1238_; 
v___x_1238_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath(v_u_1194_, v_v_1195_, v_a_1198_, v_a_1199_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_);
if (lean_obj_tag(v___x_1238_) == 0)
{
lean_object* v_a_1239_; lean_object* v___x_1240_; 
v_a_1239_ = lean_ctor_get(v___x_1238_, 0);
lean_inc(v_a_1239_);
lean_dec_ref_known(v___x_1238_, 1);
v___x_1240_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_u_1194_, v_a_1198_, v_a_1199_, v_a_1207_);
if (lean_obj_tag(v___x_1240_) == 0)
{
lean_object* v_a_1241_; lean_object* v___x_1242_; 
v_a_1241_ = lean_ctor_get(v___x_1240_, 0);
lean_inc(v_a_1241_);
lean_dec_ref_known(v___x_1240_, 1);
v___x_1242_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_v_1195_, v_a_1198_, v_a_1199_, v_a_1207_);
if (lean_obj_tag(v___x_1242_) == 0)
{
lean_object* v_a_1243_; lean_object* v___x_1244_; 
v_a_1243_ = lean_ctor_get(v___x_1242_, 0);
lean_inc(v_a_1243_);
lean_dec_ref_known(v___x_1242_, 1);
v___x_1244_ = l_Lean_Meta_Grind_Order_mkPropagateEqFalseProof(v_a_1241_, v_a_1243_, v_k_1196_, v_a_1239_, v_k_x27_1197_, v_a_1198_, v_a_1199_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_);
if (lean_obj_tag(v___x_1244_) == 0)
{
lean_object* v_h_x3f_1245_; 
v_h_x3f_1245_ = lean_ctor_get(v_c_1192_, 4);
lean_inc(v_h_x3f_1245_);
if (lean_obj_tag(v_h_x3f_1245_) == 1)
{
lean_object* v_a_1246_; lean_object* v_e_1247_; lean_object* v_val_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
v_a_1246_ = lean_ctor_get(v___x_1244_, 0);
lean_inc(v_a_1246_);
lean_dec_ref_known(v___x_1244_, 1);
v_e_1247_ = lean_ctor_get(v_c_1192_, 3);
lean_inc_ref(v_e_1247_);
lean_dec_ref(v_c_1192_);
v_val_1248_ = lean_ctor_get(v_h_x3f_1245_, 0);
lean_inc(v_val_1248_);
lean_dec_ref_known(v_h_x3f_1245_, 1);
v___x_1249_ = lean_obj_once(&l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2, &l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2_once, _init_l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2);
lean_inc_ref(v_e_1193_);
v___x_1250_ = l_Lean_mkApp4(v___x_1249_, v_e_1193_, v_e_1247_, v_val_1248_, v_a_1246_);
v_h_1211_ = v___x_1250_;
v___y_1212_ = v_a_1199_;
v___y_1213_ = v_a_1201_;
v___y_1214_ = v_a_1203_;
v___y_1215_ = v_a_1205_;
v___y_1216_ = v_a_1206_;
v___y_1217_ = v_a_1207_;
v___y_1218_ = v_a_1208_;
goto v___jp_1210_;
}
else
{
lean_object* v_a_1251_; 
lean_dec(v_h_x3f_1245_);
lean_dec_ref(v_c_1192_);
v_a_1251_ = lean_ctor_get(v___x_1244_, 0);
lean_inc(v_a_1251_);
lean_dec_ref_known(v___x_1244_, 1);
v_h_1211_ = v_a_1251_;
v___y_1212_ = v_a_1199_;
v___y_1213_ = v_a_1201_;
v___y_1214_ = v_a_1203_;
v___y_1215_ = v_a_1205_;
v___y_1216_ = v_a_1206_;
v___y_1217_ = v_a_1207_;
v___y_1218_ = v_a_1208_;
goto v___jp_1210_;
}
}
else
{
lean_object* v_a_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1259_; 
lean_dec_ref(v_e_1193_);
lean_dec_ref(v_c_1192_);
v_a_1252_ = lean_ctor_get(v___x_1244_, 0);
v_isSharedCheck_1259_ = !lean_is_exclusive(v___x_1244_);
if (v_isSharedCheck_1259_ == 0)
{
v___x_1254_ = v___x_1244_;
v_isShared_1255_ = v_isSharedCheck_1259_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_a_1252_);
lean_dec(v___x_1244_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1259_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v___x_1257_; 
if (v_isShared_1255_ == 0)
{
v___x_1257_ = v___x_1254_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v_a_1252_);
v___x_1257_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
return v___x_1257_;
}
}
}
}
else
{
lean_object* v_a_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1267_; 
lean_dec(v_a_1241_);
lean_dec(v_a_1239_);
lean_dec_ref(v_e_1193_);
lean_dec_ref(v_c_1192_);
v_a_1260_ = lean_ctor_get(v___x_1242_, 0);
v_isSharedCheck_1267_ = !lean_is_exclusive(v___x_1242_);
if (v_isSharedCheck_1267_ == 0)
{
v___x_1262_ = v___x_1242_;
v_isShared_1263_ = v_isSharedCheck_1267_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_a_1260_);
lean_dec(v___x_1242_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1267_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v___x_1265_; 
if (v_isShared_1263_ == 0)
{
v___x_1265_ = v___x_1262_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v_a_1260_);
v___x_1265_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
return v___x_1265_;
}
}
}
}
else
{
lean_object* v_a_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1275_; 
lean_dec(v_a_1239_);
lean_dec_ref(v_e_1193_);
lean_dec_ref(v_c_1192_);
v_a_1268_ = lean_ctor_get(v___x_1240_, 0);
v_isSharedCheck_1275_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1270_ = v___x_1240_;
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_a_1268_);
lean_dec(v___x_1240_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v___x_1273_; 
if (v_isShared_1271_ == 0)
{
v___x_1273_ = v___x_1270_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_a_1268_);
v___x_1273_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
return v___x_1273_;
}
}
}
}
else
{
lean_object* v_a_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1283_; 
lean_dec_ref(v_e_1193_);
lean_dec_ref(v_c_1192_);
v_a_1276_ = lean_ctor_get(v___x_1238_, 0);
v_isSharedCheck_1283_ = !lean_is_exclusive(v___x_1238_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1278_ = v___x_1238_;
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_a_1276_);
lean_dec(v___x_1238_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1283_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___x_1281_; 
if (v_isShared_1279_ == 0)
{
v___x_1281_ = v___x_1278_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v_a_1276_);
v___x_1281_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
return v___x_1281_;
}
}
}
v___jp_1210_:
{
lean_object* v___x_1219_; 
v___x_1219_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v___y_1212_, v___y_1217_);
if (lean_obj_tag(v___x_1219_) == 0)
{
lean_object* v_a_1220_; lean_object* v_termMapInv_1221_; lean_object* v___x_1222_; 
v_a_1220_ = lean_ctor_get(v___x_1219_, 0);
lean_inc(v_a_1220_);
lean_dec_ref_known(v___x_1219_, 1);
v_termMapInv_1221_ = lean_ctor_get(v_a_1220_, 4);
lean_inc_ref(v_termMapInv_1221_);
lean_dec(v_a_1220_);
v___x_1222_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMapInv_1221_, v_e_1193_);
lean_dec_ref(v_termMapInv_1221_);
if (lean_obj_tag(v___x_1222_) == 1)
{
lean_object* v_val_1223_; lean_object* v_fst_1224_; lean_object* v_snd_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; 
v_val_1223_ = lean_ctor_get(v___x_1222_, 0);
lean_inc(v_val_1223_);
lean_dec_ref_known(v___x_1222_, 1);
v_fst_1224_ = lean_ctor_get(v_val_1223_, 0);
lean_inc_n(v_fst_1224_, 2);
v_snd_1225_ = lean_ctor_get(v_val_1223_, 1);
lean_inc(v_snd_1225_);
lean_dec(v_val_1223_);
v___x_1226_ = lean_obj_once(&l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2, &l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2_once, _init_l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2);
v___x_1227_ = l_Lean_mkApp4(v___x_1226_, v_fst_1224_, v_e_1193_, v_snd_1225_, v_h_1211_);
v___x_1228_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_fst_1224_, v___x_1227_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_);
return v___x_1228_;
}
else
{
lean_object* v___x_1229_; 
lean_dec(v___x_1222_);
v___x_1229_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_e_1193_, v_h_1211_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_);
return v___x_1229_;
}
}
else
{
lean_object* v_a_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1237_; 
lean_dec_ref(v_h_1211_);
lean_dec_ref(v_e_1193_);
v_a_1230_ = lean_ctor_get(v___x_1219_, 0);
v_isSharedCheck_1237_ = !lean_is_exclusive(v___x_1219_);
if (v_isSharedCheck_1237_ == 0)
{
v___x_1232_ = v___x_1219_;
v_isShared_1233_ = v_isSharedCheck_1237_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_a_1230_);
lean_dec(v___x_1219_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1237_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v___x_1235_; 
if (v_isShared_1233_ == 0)
{
v___x_1235_ = v___x_1232_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v_a_1230_);
v___x_1235_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
return v___x_1235_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateEqFalse___boxed(lean_object** _args){
lean_object* v_c_1284_ = _args[0];
lean_object* v_e_1285_ = _args[1];
lean_object* v_u_1286_ = _args[2];
lean_object* v_v_1287_ = _args[3];
lean_object* v_k_1288_ = _args[4];
lean_object* v_k_x27_1289_ = _args[5];
lean_object* v_a_1290_ = _args[6];
lean_object* v_a_1291_ = _args[7];
lean_object* v_a_1292_ = _args[8];
lean_object* v_a_1293_ = _args[9];
lean_object* v_a_1294_ = _args[10];
lean_object* v_a_1295_ = _args[11];
lean_object* v_a_1296_ = _args[12];
lean_object* v_a_1297_ = _args[13];
lean_object* v_a_1298_ = _args[14];
lean_object* v_a_1299_ = _args[15];
lean_object* v_a_1300_ = _args[16];
lean_object* v_a_1301_ = _args[17];
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l_Lean_Meta_Grind_Order_propagateEqFalse(v_c_1284_, v_e_1285_, v_u_1286_, v_v_1287_, v_k_1288_, v_k_x27_1289_, v_a_1290_, v_a_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_);
lean_dec(v_a_1300_);
lean_dec_ref(v_a_1299_);
lean_dec(v_a_1298_);
lean_dec_ref(v_a_1297_);
lean_dec(v_a_1296_);
lean_dec_ref(v_a_1295_);
lean_dec(v_a_1294_);
lean_dec_ref(v_a_1293_);
lean_dec(v_a_1292_);
lean_dec(v_a_1291_);
lean_dec(v_a_1290_);
lean_dec_ref(v_k_x27_1289_);
lean_dec_ref(v_k_1288_);
lean_dec(v_v_1287_);
lean_dec(v_u_1286_);
return v_res_1302_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_propagateSelfEqFalse___closed__1(void){
_start:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1304_ = ((lean_object*)(l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__2));
v___x_1305_ = lean_unsigned_to_nat(2u);
v___x_1306_ = lean_unsigned_to_nat(105u);
v___x_1307_ = ((lean_object*)(l_Lean_Meta_Grind_Order_propagateSelfEqFalse___closed__0));
v___x_1308_ = ((lean_object*)(l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__0));
v___x_1309_ = l_mkPanicMessageWithDecl(v___x_1308_, v___x_1307_, v___x_1306_, v___x_1305_, v___x_1304_);
return v___x_1309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateSelfEqFalse(lean_object* v_c_1310_, lean_object* v_e_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_){
_start:
{
lean_object* v_h_1325_; lean_object* v___y_1326_; lean_object* v___y_1327_; lean_object* v___y_1328_; lean_object* v___y_1329_; lean_object* v___y_1330_; lean_object* v___y_1331_; lean_object* v___y_1332_; lean_object* v_u_1352_; lean_object* v_v_1353_; lean_object* v_e_1354_; lean_object* v_h_x3f_1355_; lean_object* v___x_1356_; 
v_u_1352_ = lean_ctor_get(v_c_1310_, 0);
v_v_1353_ = lean_ctor_get(v_c_1310_, 1);
v_e_1354_ = lean_ctor_get(v_c_1310_, 3);
lean_inc_ref(v_e_1354_);
v_h_x3f_1355_ = lean_ctor_get(v_c_1310_, 4);
lean_inc(v_h_x3f_1355_);
v___x_1356_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_u_1352_, v_a_1312_, v_a_1313_, v_a_1321_);
if (lean_obj_tag(v___x_1356_) == 0)
{
lean_object* v_a_1357_; uint8_t v___x_1358_; 
v_a_1357_ = lean_ctor_get(v___x_1356_, 0);
lean_inc(v_a_1357_);
lean_dec_ref_known(v___x_1356_, 1);
v___x_1358_ = lean_nat_dec_eq(v_u_1352_, v_v_1353_);
if (v___x_1358_ == 0)
{
lean_object* v___x_1359_; lean_object* v___x_1360_; 
lean_dec(v_a_1357_);
lean_dec(v_h_x3f_1355_);
lean_dec_ref(v_e_1354_);
lean_dec_ref(v_e_1311_);
lean_dec_ref(v_c_1310_);
v___x_1359_ = lean_obj_once(&l_Lean_Meta_Grind_Order_propagateSelfEqFalse___closed__1, &l_Lean_Meta_Grind_Order_propagateSelfEqFalse___closed__1_once, _init_l_Lean_Meta_Grind_Order_propagateSelfEqFalse___closed__1);
v___x_1360_ = l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0(v___x_1359_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_);
return v___x_1360_;
}
else
{
lean_object* v___x_1361_; lean_object* v___x_1362_; 
v___x_1361_ = l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(v_c_1310_);
lean_dec_ref(v_c_1310_);
v___x_1362_ = l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof(v_a_1357_, v___x_1361_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_);
lean_dec_ref(v___x_1361_);
if (lean_obj_tag(v___x_1362_) == 0)
{
if (lean_obj_tag(v_h_x3f_1355_) == 1)
{
lean_object* v_a_1363_; lean_object* v_val_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; 
v_a_1363_ = lean_ctor_get(v___x_1362_, 0);
lean_inc(v_a_1363_);
lean_dec_ref_known(v___x_1362_, 1);
v_val_1364_ = lean_ctor_get(v_h_x3f_1355_, 0);
lean_inc(v_val_1364_);
lean_dec_ref_known(v_h_x3f_1355_, 1);
v___x_1365_ = lean_obj_once(&l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2, &l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2_once, _init_l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2);
lean_inc_ref(v_e_1311_);
v___x_1366_ = l_Lean_mkApp4(v___x_1365_, v_e_1311_, v_e_1354_, v_val_1364_, v_a_1363_);
v_h_1325_ = v___x_1366_;
v___y_1326_ = v_a_1313_;
v___y_1327_ = v_a_1315_;
v___y_1328_ = v_a_1317_;
v___y_1329_ = v_a_1319_;
v___y_1330_ = v_a_1320_;
v___y_1331_ = v_a_1321_;
v___y_1332_ = v_a_1322_;
goto v___jp_1324_;
}
else
{
lean_object* v_a_1367_; 
lean_dec(v_h_x3f_1355_);
lean_dec_ref(v_e_1354_);
v_a_1367_ = lean_ctor_get(v___x_1362_, 0);
lean_inc(v_a_1367_);
lean_dec_ref_known(v___x_1362_, 1);
v_h_1325_ = v_a_1367_;
v___y_1326_ = v_a_1313_;
v___y_1327_ = v_a_1315_;
v___y_1328_ = v_a_1317_;
v___y_1329_ = v_a_1319_;
v___y_1330_ = v_a_1320_;
v___y_1331_ = v_a_1321_;
v___y_1332_ = v_a_1322_;
goto v___jp_1324_;
}
}
else
{
lean_object* v_a_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1375_; 
lean_dec(v_h_x3f_1355_);
lean_dec_ref(v_e_1354_);
lean_dec_ref(v_e_1311_);
v_a_1368_ = lean_ctor_get(v___x_1362_, 0);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1362_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1370_ = v___x_1362_;
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_a_1368_);
lean_dec(v___x_1362_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1373_; 
if (v_isShared_1371_ == 0)
{
v___x_1373_ = v___x_1370_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_a_1368_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
}
}
}
else
{
lean_object* v_a_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1383_; 
lean_dec(v_h_x3f_1355_);
lean_dec_ref(v_e_1354_);
lean_dec_ref(v_e_1311_);
lean_dec_ref(v_c_1310_);
v_a_1376_ = lean_ctor_get(v___x_1356_, 0);
v_isSharedCheck_1383_ = !lean_is_exclusive(v___x_1356_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1378_ = v___x_1356_;
v_isShared_1379_ = v_isSharedCheck_1383_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_a_1376_);
lean_dec(v___x_1356_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1383_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
lean_object* v___x_1381_; 
if (v_isShared_1379_ == 0)
{
v___x_1381_ = v___x_1378_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v_a_1376_);
v___x_1381_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
return v___x_1381_;
}
}
}
v___jp_1324_:
{
lean_object* v___x_1333_; 
v___x_1333_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v___y_1326_, v___y_1331_);
if (lean_obj_tag(v___x_1333_) == 0)
{
lean_object* v_a_1334_; lean_object* v_termMapInv_1335_; lean_object* v___x_1336_; 
v_a_1334_ = lean_ctor_get(v___x_1333_, 0);
lean_inc(v_a_1334_);
lean_dec_ref_known(v___x_1333_, 1);
v_termMapInv_1335_ = lean_ctor_get(v_a_1334_, 4);
lean_inc_ref(v_termMapInv_1335_);
lean_dec(v_a_1334_);
v___x_1336_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMapInv_1335_, v_e_1311_);
lean_dec_ref(v_termMapInv_1335_);
if (lean_obj_tag(v___x_1336_) == 1)
{
lean_object* v_val_1337_; lean_object* v_fst_1338_; lean_object* v_snd_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; 
v_val_1337_ = lean_ctor_get(v___x_1336_, 0);
lean_inc(v_val_1337_);
lean_dec_ref_known(v___x_1336_, 1);
v_fst_1338_ = lean_ctor_get(v_val_1337_, 0);
lean_inc_n(v_fst_1338_, 2);
v_snd_1339_ = lean_ctor_get(v_val_1337_, 1);
lean_inc(v_snd_1339_);
lean_dec(v_val_1337_);
v___x_1340_ = lean_obj_once(&l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2, &l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2_once, _init_l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2);
v___x_1341_ = l_Lean_mkApp4(v___x_1340_, v_fst_1338_, v_e_1311_, v_snd_1339_, v_h_1325_);
v___x_1342_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_fst_1338_, v___x_1341_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_);
return v___x_1342_;
}
else
{
lean_object* v___x_1343_; 
lean_dec(v___x_1336_);
v___x_1343_ = l_Lean_Meta_Grind_pushEqFalse___redArg(v_e_1311_, v_h_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_);
return v___x_1343_;
}
}
else
{
lean_object* v_a_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1351_; 
lean_dec_ref(v_h_1325_);
lean_dec_ref(v_e_1311_);
v_a_1344_ = lean_ctor_get(v___x_1333_, 0);
v_isSharedCheck_1351_ = !lean_is_exclusive(v___x_1333_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1346_ = v___x_1333_;
v_isShared_1347_ = v_isSharedCheck_1351_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_a_1344_);
lean_dec(v___x_1333_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1351_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v___x_1349_; 
if (v_isShared_1347_ == 0)
{
v___x_1349_ = v___x_1346_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_a_1344_);
v___x_1349_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
return v___x_1349_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateSelfEqFalse___boxed(lean_object* v_c_1384_, lean_object* v_e_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_){
_start:
{
lean_object* v_res_1398_; 
v_res_1398_ = l_Lean_Meta_Grind_Order_propagateSelfEqFalse(v_c_1384_, v_e_1385_, v_a_1386_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_);
lean_dec(v_a_1396_);
lean_dec_ref(v_a_1395_);
lean_dec(v_a_1394_);
lean_dec_ref(v_a_1393_);
lean_dec(v_a_1392_);
lean_dec_ref(v_a_1391_);
lean_dec(v_a_1390_);
lean_dec_ref(v_a_1389_);
lean_dec(v_a_1388_);
lean_dec(v_a_1387_);
lean_dec(v_a_1386_);
return v_res_1398_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f___redArg(lean_object* v_e_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_){
_start:
{
lean_object* v___x_1403_; 
v___x_1403_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_1400_, v_a_1401_);
if (lean_obj_tag(v___x_1403_) == 0)
{
lean_object* v_a_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1413_; 
v_a_1404_ = lean_ctor_get(v___x_1403_, 0);
v_isSharedCheck_1413_ = !lean_is_exclusive(v___x_1403_);
if (v_isSharedCheck_1413_ == 0)
{
v___x_1406_ = v___x_1403_;
v_isShared_1407_ = v_isSharedCheck_1413_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_a_1404_);
lean_dec(v___x_1403_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1413_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v_termMapInv_1408_; lean_object* v___x_1409_; lean_object* v___x_1411_; 
v_termMapInv_1408_ = lean_ctor_get(v_a_1404_, 4);
lean_inc_ref(v_termMapInv_1408_);
lean_dec(v_a_1404_);
v___x_1409_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMapInv_1408_, v_e_1399_);
lean_dec_ref(v_termMapInv_1408_);
if (v_isShared_1407_ == 0)
{
lean_ctor_set(v___x_1406_, 0, v___x_1409_);
v___x_1411_ = v___x_1406_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v___x_1409_);
v___x_1411_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
return v___x_1411_;
}
}
}
else
{
lean_object* v_a_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1421_; 
v_a_1414_ = lean_ctor_get(v___x_1403_, 0);
v_isSharedCheck_1421_ = !lean_is_exclusive(v___x_1403_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1416_ = v___x_1403_;
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_a_1414_);
lean_dec(v___x_1403_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1419_; 
if (v_isShared_1417_ == 0)
{
v___x_1419_ = v___x_1416_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_a_1414_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f___redArg___boxed(lean_object* v_e_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_){
_start:
{
lean_object* v_res_1426_; 
v_res_1426_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f___redArg(v_e_1422_, v_a_1423_, v_a_1424_);
lean_dec_ref(v_a_1424_);
lean_dec(v_a_1423_);
lean_dec_ref(v_e_1422_);
return v_res_1426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f(lean_object* v_e_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_){
_start:
{
lean_object* v___x_1439_; 
v___x_1439_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f___redArg(v_e_1427_, v_a_1428_, v_a_1436_);
return v___x_1439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f___boxed(lean_object* v_e_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_, lean_object* v_a_1451_){
_start:
{
lean_object* v_res_1452_; 
v_res_1452_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f(v_e_1440_, v_a_1441_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_, v_a_1450_);
lean_dec(v_a_1450_);
lean_dec_ref(v_a_1449_);
lean_dec(v_a_1448_);
lean_dec_ref(v_a_1447_);
lean_dec(v_a_1446_);
lean_dec_ref(v_a_1445_);
lean_dec(v_a_1444_);
lean_dec_ref(v_a_1443_);
lean_dec(v_a_1442_);
lean_dec(v_a_1441_);
lean_dec_ref(v_e_1440_);
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending___lam__0(lean_object* v_s_1453_){
_start:
{
lean_object* v_id_1454_; lean_object* v_nodes_1455_; lean_object* v_nodeMap_1456_; lean_object* v_cnstrs_1457_; lean_object* v_cnstrsOf_1458_; lean_object* v_sources_1459_; lean_object* v_targets_1460_; lean_object* v_proofs_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1469_; 
v_id_1454_ = lean_ctor_get(v_s_1453_, 0);
v_nodes_1455_ = lean_ctor_get(v_s_1453_, 1);
v_nodeMap_1456_ = lean_ctor_get(v_s_1453_, 2);
v_cnstrs_1457_ = lean_ctor_get(v_s_1453_, 3);
v_cnstrsOf_1458_ = lean_ctor_get(v_s_1453_, 4);
v_sources_1459_ = lean_ctor_get(v_s_1453_, 5);
v_targets_1460_ = lean_ctor_get(v_s_1453_, 6);
v_proofs_1461_ = lean_ctor_get(v_s_1453_, 7);
v_isSharedCheck_1469_ = !lean_is_exclusive(v_s_1453_);
if (v_isSharedCheck_1469_ == 0)
{
lean_object* v_unused_1470_; 
v_unused_1470_ = lean_ctor_get(v_s_1453_, 8);
lean_dec(v_unused_1470_);
v___x_1463_ = v_s_1453_;
v_isShared_1464_ = v_isSharedCheck_1469_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_proofs_1461_);
lean_inc(v_targets_1460_);
lean_inc(v_sources_1459_);
lean_inc(v_cnstrsOf_1458_);
lean_inc(v_cnstrs_1457_);
lean_inc(v_nodeMap_1456_);
lean_inc(v_nodes_1455_);
lean_inc(v_id_1454_);
lean_dec(v_s_1453_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1469_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v___x_1465_; lean_object* v___x_1467_; 
v___x_1465_ = lean_box(0);
if (v_isShared_1464_ == 0)
{
lean_ctor_set(v___x_1463_, 8, v___x_1465_);
v___x_1467_ = v___x_1463_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v_id_1454_);
lean_ctor_set(v_reuseFailAlloc_1468_, 1, v_nodes_1455_);
lean_ctor_set(v_reuseFailAlloc_1468_, 2, v_nodeMap_1456_);
lean_ctor_set(v_reuseFailAlloc_1468_, 3, v_cnstrs_1457_);
lean_ctor_set(v_reuseFailAlloc_1468_, 4, v_cnstrsOf_1458_);
lean_ctor_set(v_reuseFailAlloc_1468_, 5, v_sources_1459_);
lean_ctor_set(v_reuseFailAlloc_1468_, 6, v_targets_1460_);
lean_ctor_set(v_reuseFailAlloc_1468_, 7, v_proofs_1461_);
lean_ctor_set(v_reuseFailAlloc_1468_, 8, v___x_1465_);
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
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; 
v___x_1477_ = lean_box(0);
v___x_1478_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg___closed__1));
v___x_1479_ = l_Lean_mkConst(v___x_1478_, v___x_1477_);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg(lean_object* v_as_x27_1480_, lean_object* v_b_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_){
_start:
{
if (lean_obj_tag(v_as_x27_1480_) == 0)
{
lean_object* v___x_1494_; 
v___x_1494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1494_, 0, v_b_1481_);
return v___x_1494_;
}
else
{
lean_object* v_head_1495_; lean_object* v_tail_1496_; lean_object* v___x_1497_; 
v_head_1495_ = lean_ctor_get(v_as_x27_1480_, 0);
v_tail_1496_ = lean_ctor_get(v_as_x27_1480_, 1);
v___x_1497_ = lean_box(0);
switch(lean_obj_tag(v_head_1495_))
{
case 0:
{
lean_object* v_c_1498_; lean_object* v_e_1499_; lean_object* v_u_1500_; lean_object* v_v_1501_; lean_object* v_k_1502_; lean_object* v_k_x27_1503_; lean_object* v___x_1504_; 
v_c_1498_ = lean_ctor_get(v_head_1495_, 0);
v_e_1499_ = lean_ctor_get(v_head_1495_, 1);
v_u_1500_ = lean_ctor_get(v_head_1495_, 2);
v_v_1501_ = lean_ctor_get(v_head_1495_, 3);
v_k_1502_ = lean_ctor_get(v_head_1495_, 4);
v_k_x27_1503_ = lean_ctor_get(v_head_1495_, 5);
lean_inc_ref(v_e_1499_);
lean_inc_ref(v_c_1498_);
v___x_1504_ = l_Lean_Meta_Grind_Order_propagateEqTrue(v_c_1498_, v_e_1499_, v_u_1500_, v_v_1501_, v_k_1502_, v_k_x27_1503_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_);
if (lean_obj_tag(v___x_1504_) == 0)
{
lean_dec_ref_known(v___x_1504_, 1);
v_as_x27_1480_ = v_tail_1496_;
v_b_1481_ = v___x_1497_;
goto _start;
}
else
{
return v___x_1504_;
}
}
case 1:
{
lean_object* v_c_1506_; lean_object* v_e_1507_; lean_object* v_u_1508_; lean_object* v_v_1509_; lean_object* v_k_1510_; lean_object* v_k_x27_1511_; lean_object* v___x_1512_; 
v_c_1506_ = lean_ctor_get(v_head_1495_, 0);
v_e_1507_ = lean_ctor_get(v_head_1495_, 1);
v_u_1508_ = lean_ctor_get(v_head_1495_, 2);
v_v_1509_ = lean_ctor_get(v_head_1495_, 3);
v_k_1510_ = lean_ctor_get(v_head_1495_, 4);
v_k_x27_1511_ = lean_ctor_get(v_head_1495_, 5);
lean_inc_ref(v_e_1507_);
lean_inc_ref(v_c_1506_);
v___x_1512_ = l_Lean_Meta_Grind_Order_propagateEqFalse(v_c_1506_, v_e_1507_, v_u_1508_, v_v_1509_, v_k_1510_, v_k_x27_1511_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_);
if (lean_obj_tag(v___x_1512_) == 0)
{
lean_dec_ref_known(v___x_1512_, 1);
v_as_x27_1480_ = v_tail_1496_;
v_b_1481_ = v___x_1497_;
goto _start;
}
else
{
return v___x_1512_;
}
}
default: 
{
lean_object* v_u_1514_; lean_object* v_v_1515_; lean_object* v___x_1516_; 
v_u_1514_ = lean_ctor_get(v_head_1495_, 0);
v_v_1515_ = lean_ctor_get(v_head_1495_, 1);
v___x_1516_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_u_1514_, v___y_1482_, v___y_1483_, v___y_1491_);
if (lean_obj_tag(v___x_1516_) == 0)
{
lean_object* v_a_1517_; lean_object* v___x_1518_; 
v_a_1517_ = lean_ctor_get(v___x_1516_, 0);
lean_inc(v_a_1517_);
lean_dec_ref_known(v___x_1516_, 1);
v___x_1518_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_v_1515_, v___y_1482_, v___y_1483_, v___y_1491_);
if (lean_obj_tag(v___x_1518_) == 0)
{
lean_object* v_a_1519_; lean_object* v___y_1521_; lean_object* v___y_1522_; lean_object* v___y_1523_; lean_object* v___y_1524_; lean_object* v___y_1525_; lean_object* v___y_1526_; lean_object* v___y_1527_; lean_object* v___y_1528_; lean_object* v___y_1529_; lean_object* v___y_1530_; lean_object* v___y_1531_; lean_object* v___x_1644_; 
v_a_1519_ = lean_ctor_get(v___x_1518_, 0);
lean_inc(v_a_1519_);
lean_dec_ref_known(v___x_1518_, 1);
v___x_1644_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_a_1517_, v___y_1483_);
if (lean_obj_tag(v___x_1644_) == 0)
{
lean_object* v_a_1645_; uint8_t v___x_1646_; 
v_a_1645_ = lean_ctor_get(v___x_1644_, 0);
lean_inc(v_a_1645_);
lean_dec_ref_known(v___x_1644_, 1);
v___x_1646_ = lean_unbox(v_a_1645_);
lean_dec(v_a_1645_);
if (v___x_1646_ == 0)
{
v___y_1521_ = v___y_1482_;
v___y_1522_ = v___y_1483_;
v___y_1523_ = v___y_1484_;
v___y_1524_ = v___y_1485_;
v___y_1525_ = v___y_1486_;
v___y_1526_ = v___y_1487_;
v___y_1527_ = v___y_1488_;
v___y_1528_ = v___y_1489_;
v___y_1529_ = v___y_1490_;
v___y_1530_ = v___y_1491_;
v___y_1531_ = v___y_1492_;
goto v___jp_1520_;
}
else
{
lean_object* v___x_1647_; 
v___x_1647_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_a_1519_, v___y_1483_);
if (lean_obj_tag(v___x_1647_) == 0)
{
lean_object* v_a_1648_; uint8_t v___x_1649_; 
v_a_1648_ = lean_ctor_get(v___x_1647_, 0);
lean_inc(v_a_1648_);
lean_dec_ref_known(v___x_1647_, 1);
v___x_1649_ = lean_unbox(v_a_1648_);
lean_dec(v_a_1648_);
if (v___x_1649_ == 0)
{
v___y_1521_ = v___y_1482_;
v___y_1522_ = v___y_1483_;
v___y_1523_ = v___y_1484_;
v___y_1524_ = v___y_1485_;
v___y_1525_ = v___y_1486_;
v___y_1526_ = v___y_1487_;
v___y_1527_ = v___y_1488_;
v___y_1528_ = v___y_1489_;
v___y_1529_ = v___y_1490_;
v___y_1530_ = v___y_1491_;
v___y_1531_ = v___y_1492_;
goto v___jp_1520_;
}
else
{
lean_object* v___x_1650_; 
v___x_1650_ = l_Lean_Meta_Grind_isEqv___redArg(v_a_1517_, v_a_1519_, v___y_1483_);
if (lean_obj_tag(v___x_1650_) == 0)
{
lean_object* v_a_1651_; uint8_t v___x_1652_; 
v_a_1651_ = lean_ctor_get(v___x_1650_, 0);
lean_inc(v_a_1651_);
lean_dec_ref_known(v___x_1650_, 1);
v___x_1652_ = lean_unbox(v_a_1651_);
if (v___x_1652_ == 0)
{
lean_object* v___x_1653_; 
v___x_1653_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath(v_u_1514_, v_v_1515_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_);
if (lean_obj_tag(v___x_1653_) == 0)
{
lean_object* v_a_1654_; lean_object* v___x_1655_; 
v_a_1654_ = lean_ctor_get(v___x_1653_, 0);
lean_inc(v_a_1654_);
lean_dec_ref_known(v___x_1653_, 1);
v___x_1655_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath(v_v_1515_, v_u_1514_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_);
if (lean_obj_tag(v___x_1655_) == 0)
{
lean_object* v_a_1656_; lean_object* v___x_1657_; 
v_a_1656_ = lean_ctor_get(v___x_1655_, 0);
lean_inc(v_a_1656_);
lean_dec_ref_known(v___x_1655_, 1);
lean_inc(v_a_1519_);
lean_inc(v_a_1517_);
v___x_1657_ = l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLe(v_a_1517_, v_a_1519_, v_a_1654_, v_a_1656_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_);
if (lean_obj_tag(v___x_1657_) == 0)
{
lean_object* v_a_1658_; uint8_t v___x_1659_; lean_object* v___x_1660_; 
v_a_1658_ = lean_ctor_get(v___x_1657_, 0);
lean_inc(v_a_1658_);
lean_dec_ref_known(v___x_1657_, 1);
v___x_1659_ = lean_unbox(v_a_1651_);
lean_dec(v_a_1651_);
lean_inc(v_a_1519_);
lean_inc(v_a_1517_);
v___x_1660_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_a_1517_, v_a_1519_, v_a_1658_, v___x_1659_, v___y_1483_, v___y_1485_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_);
if (lean_obj_tag(v___x_1660_) == 0)
{
lean_dec_ref_known(v___x_1660_, 1);
v___y_1521_ = v___y_1482_;
v___y_1522_ = v___y_1483_;
v___y_1523_ = v___y_1484_;
v___y_1524_ = v___y_1485_;
v___y_1525_ = v___y_1486_;
v___y_1526_ = v___y_1487_;
v___y_1527_ = v___y_1488_;
v___y_1528_ = v___y_1489_;
v___y_1529_ = v___y_1490_;
v___y_1530_ = v___y_1491_;
v___y_1531_ = v___y_1492_;
goto v___jp_1520_;
}
else
{
lean_dec(v_a_1519_);
lean_dec(v_a_1517_);
return v___x_1660_;
}
}
else
{
lean_object* v_a_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1668_; 
lean_dec(v_a_1651_);
lean_dec(v_a_1519_);
lean_dec(v_a_1517_);
v_a_1661_ = lean_ctor_get(v___x_1657_, 0);
v_isSharedCheck_1668_ = !lean_is_exclusive(v___x_1657_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1663_ = v___x_1657_;
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_a_1661_);
lean_dec(v___x_1657_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1668_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1666_; 
if (v_isShared_1664_ == 0)
{
v___x_1666_ = v___x_1663_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v_a_1661_);
v___x_1666_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
return v___x_1666_;
}
}
}
}
else
{
lean_object* v_a_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1676_; 
lean_dec(v_a_1654_);
lean_dec(v_a_1651_);
lean_dec(v_a_1519_);
lean_dec(v_a_1517_);
v_a_1669_ = lean_ctor_get(v___x_1655_, 0);
v_isSharedCheck_1676_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1671_ = v___x_1655_;
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_a_1669_);
lean_dec(v___x_1655_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v___x_1674_; 
if (v_isShared_1672_ == 0)
{
v___x_1674_ = v___x_1671_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v_a_1669_);
v___x_1674_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
return v___x_1674_;
}
}
}
}
else
{
lean_object* v_a_1677_; lean_object* v___x_1679_; uint8_t v_isShared_1680_; uint8_t v_isSharedCheck_1684_; 
lean_dec(v_a_1651_);
lean_dec(v_a_1519_);
lean_dec(v_a_1517_);
v_a_1677_ = lean_ctor_get(v___x_1653_, 0);
v_isSharedCheck_1684_ = !lean_is_exclusive(v___x_1653_);
if (v_isSharedCheck_1684_ == 0)
{
v___x_1679_ = v___x_1653_;
v_isShared_1680_ = v_isSharedCheck_1684_;
goto v_resetjp_1678_;
}
else
{
lean_inc(v_a_1677_);
lean_dec(v___x_1653_);
v___x_1679_ = lean_box(0);
v_isShared_1680_ = v_isSharedCheck_1684_;
goto v_resetjp_1678_;
}
v_resetjp_1678_:
{
lean_object* v___x_1682_; 
if (v_isShared_1680_ == 0)
{
v___x_1682_ = v___x_1679_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v_a_1677_);
v___x_1682_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
return v___x_1682_;
}
}
}
}
else
{
lean_dec(v_a_1651_);
v___y_1521_ = v___y_1482_;
v___y_1522_ = v___y_1483_;
v___y_1523_ = v___y_1484_;
v___y_1524_ = v___y_1485_;
v___y_1525_ = v___y_1486_;
v___y_1526_ = v___y_1487_;
v___y_1527_ = v___y_1488_;
v___y_1528_ = v___y_1489_;
v___y_1529_ = v___y_1490_;
v___y_1530_ = v___y_1491_;
v___y_1531_ = v___y_1492_;
goto v___jp_1520_;
}
}
else
{
lean_object* v_a_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1692_; 
lean_dec(v_a_1519_);
lean_dec(v_a_1517_);
v_a_1685_ = lean_ctor_get(v___x_1650_, 0);
v_isSharedCheck_1692_ = !lean_is_exclusive(v___x_1650_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1687_ = v___x_1650_;
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_a_1685_);
lean_dec(v___x_1650_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v___x_1690_; 
if (v_isShared_1688_ == 0)
{
v___x_1690_ = v___x_1687_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v_a_1685_);
v___x_1690_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
return v___x_1690_;
}
}
}
}
}
else
{
lean_object* v_a_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1700_; 
lean_dec(v_a_1519_);
lean_dec(v_a_1517_);
v_a_1693_ = lean_ctor_get(v___x_1647_, 0);
v_isSharedCheck_1700_ = !lean_is_exclusive(v___x_1647_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1695_ = v___x_1647_;
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_a_1693_);
lean_dec(v___x_1647_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1700_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
lean_object* v___x_1698_; 
if (v_isShared_1696_ == 0)
{
v___x_1698_ = v___x_1695_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v_a_1693_);
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
else
{
lean_object* v_a_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1708_; 
lean_dec(v_a_1519_);
lean_dec(v_a_1517_);
v_a_1701_ = lean_ctor_get(v___x_1644_, 0);
v_isSharedCheck_1708_ = !lean_is_exclusive(v___x_1644_);
if (v_isSharedCheck_1708_ == 0)
{
v___x_1703_ = v___x_1644_;
v_isShared_1704_ = v_isSharedCheck_1708_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_a_1701_);
lean_dec(v___x_1644_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1708_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
lean_object* v___x_1706_; 
if (v_isShared_1704_ == 0)
{
v___x_1706_ = v___x_1703_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v_a_1701_);
v___x_1706_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
return v___x_1706_;
}
}
}
v___jp_1520_:
{
lean_object* v___x_1532_; 
v___x_1532_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f___redArg(v_a_1517_, v___y_1522_, v___y_1530_);
if (lean_obj_tag(v___x_1532_) == 0)
{
lean_object* v_a_1533_; 
v_a_1533_ = lean_ctor_get(v___x_1532_, 0);
lean_inc(v_a_1533_);
lean_dec_ref_known(v___x_1532_, 1);
if (lean_obj_tag(v_a_1533_) == 1)
{
lean_object* v_val_1534_; lean_object* v_fst_1535_; lean_object* v_snd_1536_; lean_object* v___x_1537_; 
v_val_1534_ = lean_ctor_get(v_a_1533_, 0);
lean_inc(v_val_1534_);
lean_dec_ref_known(v_a_1533_, 1);
v_fst_1535_ = lean_ctor_get(v_val_1534_, 0);
lean_inc(v_fst_1535_);
v_snd_1536_ = lean_ctor_get(v_val_1534_, 1);
lean_inc(v_snd_1536_);
lean_dec(v_val_1534_);
v___x_1537_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f___redArg(v_a_1519_, v___y_1522_, v___y_1530_);
if (lean_obj_tag(v___x_1537_) == 0)
{
lean_object* v_a_1538_; 
v_a_1538_ = lean_ctor_get(v___x_1537_, 0);
lean_inc(v_a_1538_);
lean_dec_ref_known(v___x_1537_, 1);
if (lean_obj_tag(v_a_1538_) == 1)
{
lean_object* v_val_1539_; lean_object* v_fst_1540_; lean_object* v_snd_1541_; lean_object* v___x_1542_; 
v_val_1539_ = lean_ctor_get(v_a_1538_, 0);
lean_inc(v_val_1539_);
lean_dec_ref_known(v_a_1538_, 1);
v_fst_1540_ = lean_ctor_get(v_val_1539_, 0);
lean_inc(v_fst_1540_);
v_snd_1541_ = lean_ctor_get(v_val_1539_, 1);
lean_inc(v_snd_1541_);
lean_dec(v_val_1539_);
v___x_1542_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_fst_1535_, v___y_1522_);
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_object* v_a_1543_; uint8_t v___x_1544_; 
v_a_1543_ = lean_ctor_get(v___x_1542_, 0);
lean_inc(v_a_1543_);
lean_dec_ref_known(v___x_1542_, 1);
v___x_1544_ = lean_unbox(v_a_1543_);
lean_dec(v_a_1543_);
if (v___x_1544_ == 0)
{
lean_dec(v_snd_1541_);
lean_dec(v_fst_1540_);
lean_dec(v_snd_1536_);
lean_dec(v_fst_1535_);
lean_dec(v_a_1519_);
lean_dec(v_a_1517_);
v_as_x27_1480_ = v_tail_1496_;
v_b_1481_ = v___x_1497_;
goto _start;
}
else
{
lean_object* v___x_1546_; 
v___x_1546_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_fst_1540_, v___y_1522_);
if (lean_obj_tag(v___x_1546_) == 0)
{
lean_object* v_a_1547_; uint8_t v___x_1548_; 
v_a_1547_ = lean_ctor_get(v___x_1546_, 0);
lean_inc(v_a_1547_);
lean_dec_ref_known(v___x_1546_, 1);
v___x_1548_ = lean_unbox(v_a_1547_);
lean_dec(v_a_1547_);
if (v___x_1548_ == 0)
{
lean_dec(v_snd_1541_);
lean_dec(v_fst_1540_);
lean_dec(v_snd_1536_);
lean_dec(v_fst_1535_);
lean_dec(v_a_1519_);
lean_dec(v_a_1517_);
v_as_x27_1480_ = v_tail_1496_;
v_b_1481_ = v___x_1497_;
goto _start;
}
else
{
lean_object* v___x_1550_; 
v___x_1550_ = l_Lean_Meta_Grind_isEqv___redArg(v_fst_1535_, v_fst_1540_, v___y_1522_);
if (lean_obj_tag(v___x_1550_) == 0)
{
lean_object* v_a_1551_; uint8_t v___x_1552_; 
v_a_1551_ = lean_ctor_get(v___x_1550_, 0);
lean_inc(v_a_1551_);
lean_dec_ref_known(v___x_1550_, 1);
v___x_1552_ = lean_unbox(v_a_1551_);
if (v___x_1552_ == 0)
{
lean_object* v___x_1553_; 
v___x_1553_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath(v_u_1514_, v_v_1515_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_);
if (lean_obj_tag(v___x_1553_) == 0)
{
lean_object* v_a_1554_; lean_object* v___x_1555_; 
v_a_1554_ = lean_ctor_get(v___x_1553_, 0);
lean_inc(v_a_1554_);
lean_dec_ref_known(v___x_1553_, 1);
v___x_1555_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath(v_v_1515_, v_u_1514_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_);
if (lean_obj_tag(v___x_1555_) == 0)
{
lean_object* v_a_1556_; lean_object* v___x_1557_; 
v_a_1556_ = lean_ctor_get(v___x_1555_, 0);
lean_inc(v_a_1556_);
lean_dec_ref_known(v___x_1555_, 1);
lean_inc(v_a_1519_);
lean_inc(v_a_1517_);
v___x_1557_ = l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLe(v_a_1517_, v_a_1519_, v_a_1554_, v_a_1556_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_);
if (lean_obj_tag(v___x_1557_) == 0)
{
lean_object* v_a_1558_; lean_object* v___x_1559_; 
v_a_1558_ = lean_ctor_get(v___x_1557_, 0);
lean_inc(v_a_1558_);
lean_dec_ref_known(v___x_1557_, 1);
lean_inc(v___y_1531_);
lean_inc_ref(v___y_1530_);
lean_inc(v___y_1529_);
lean_inc_ref(v___y_1528_);
lean_inc(v_a_1517_);
v___x_1559_ = lean_infer_type(v_a_1517_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_);
if (lean_obj_tag(v___x_1559_) == 0)
{
lean_object* v_a_1560_; lean_object* v___x_1561_; uint8_t v___x_1562_; 
v_a_1560_ = lean_ctor_get(v___x_1559_, 0);
lean_inc(v_a_1560_);
lean_dec_ref_known(v___x_1559_, 1);
v___x_1561_ = l_Lean_Int_mkType;
v___x_1562_ = lean_expr_eqv(v_a_1560_, v___x_1561_);
lean_dec(v_a_1560_);
if (v___x_1562_ == 0)
{
lean_dec(v_a_1558_);
lean_dec(v_a_1551_);
lean_dec(v_snd_1541_);
lean_dec(v_fst_1540_);
lean_dec(v_snd_1536_);
lean_dec(v_fst_1535_);
lean_dec(v_a_1519_);
lean_dec(v_a_1517_);
v_as_x27_1480_ = v_tail_1496_;
v_b_1481_ = v___x_1497_;
goto _start;
}
else
{
lean_object* v___x_1564_; lean_object* v___x_1565_; uint8_t v___x_1566_; lean_object* v___x_1567_; 
v___x_1564_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg___closed__2, &l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg___closed__2_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg___closed__2);
lean_inc(v_fst_1540_);
lean_inc(v_fst_1535_);
v___x_1565_ = l_Lean_mkApp7(v___x_1564_, v_fst_1535_, v_fst_1540_, v_a_1517_, v_a_1519_, v_snd_1536_, v_snd_1541_, v_a_1558_);
v___x_1566_ = lean_unbox(v_a_1551_);
lean_dec(v_a_1551_);
v___x_1567_ = l_Lean_Meta_Grind_pushEqCore___redArg(v_fst_1535_, v_fst_1540_, v___x_1565_, v___x_1566_, v___y_1522_, v___y_1524_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_);
if (lean_obj_tag(v___x_1567_) == 0)
{
lean_dec_ref_known(v___x_1567_, 1);
v_as_x27_1480_ = v_tail_1496_;
v_b_1481_ = v___x_1497_;
goto _start;
}
else
{
return v___x_1567_;
}
}
}
else
{
lean_object* v_a_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1576_; 
lean_dec(v_a_1558_);
lean_dec(v_a_1551_);
lean_dec(v_snd_1541_);
lean_dec(v_fst_1540_);
lean_dec(v_snd_1536_);
lean_dec(v_fst_1535_);
lean_dec(v_a_1519_);
lean_dec(v_a_1517_);
v_a_1569_ = lean_ctor_get(v___x_1559_, 0);
v_isSharedCheck_1576_ = !lean_is_exclusive(v___x_1559_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1571_ = v___x_1559_;
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_a_1569_);
lean_dec(v___x_1559_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1574_; 
if (v_isShared_1572_ == 0)
{
v___x_1574_ = v___x_1571_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v_a_1569_);
v___x_1574_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
return v___x_1574_;
}
}
}
}
else
{
lean_object* v_a_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1584_; 
lean_dec(v_a_1551_);
lean_dec(v_snd_1541_);
lean_dec(v_fst_1540_);
lean_dec(v_snd_1536_);
lean_dec(v_fst_1535_);
lean_dec(v_a_1519_);
lean_dec(v_a_1517_);
v_a_1577_ = lean_ctor_get(v___x_1557_, 0);
v_isSharedCheck_1584_ = !lean_is_exclusive(v___x_1557_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1579_ = v___x_1557_;
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_a_1577_);
lean_dec(v___x_1557_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v___x_1582_; 
if (v_isShared_1580_ == 0)
{
v___x_1582_ = v___x_1579_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_a_1577_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
return v___x_1582_;
}
}
}
}
else
{
lean_object* v_a_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1592_; 
lean_dec(v_a_1554_);
lean_dec(v_a_1551_);
lean_dec(v_snd_1541_);
lean_dec(v_fst_1540_);
lean_dec(v_snd_1536_);
lean_dec(v_fst_1535_);
lean_dec(v_a_1519_);
lean_dec(v_a_1517_);
v_a_1585_ = lean_ctor_get(v___x_1555_, 0);
v_isSharedCheck_1592_ = !lean_is_exclusive(v___x_1555_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1587_ = v___x_1555_;
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_a_1585_);
lean_dec(v___x_1555_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v___x_1590_; 
if (v_isShared_1588_ == 0)
{
v___x_1590_ = v___x_1587_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v_a_1585_);
v___x_1590_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
return v___x_1590_;
}
}
}
}
else
{
lean_object* v_a_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1600_; 
lean_dec(v_a_1551_);
lean_dec(v_snd_1541_);
lean_dec(v_fst_1540_);
lean_dec(v_snd_1536_);
lean_dec(v_fst_1535_);
lean_dec(v_a_1519_);
lean_dec(v_a_1517_);
v_a_1593_ = lean_ctor_get(v___x_1553_, 0);
v_isSharedCheck_1600_ = !lean_is_exclusive(v___x_1553_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1595_ = v___x_1553_;
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_a_1593_);
lean_dec(v___x_1553_);
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
else
{
lean_dec(v_a_1551_);
lean_dec(v_snd_1541_);
lean_dec(v_fst_1540_);
lean_dec(v_snd_1536_);
lean_dec(v_fst_1535_);
lean_dec(v_a_1519_);
lean_dec(v_a_1517_);
v_as_x27_1480_ = v_tail_1496_;
v_b_1481_ = v___x_1497_;
goto _start;
}
}
else
{
lean_object* v_a_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1609_; 
lean_dec(v_snd_1541_);
lean_dec(v_fst_1540_);
lean_dec(v_snd_1536_);
lean_dec(v_fst_1535_);
lean_dec(v_a_1519_);
lean_dec(v_a_1517_);
v_a_1602_ = lean_ctor_get(v___x_1550_, 0);
v_isSharedCheck_1609_ = !lean_is_exclusive(v___x_1550_);
if (v_isSharedCheck_1609_ == 0)
{
v___x_1604_ = v___x_1550_;
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_a_1602_);
lean_dec(v___x_1550_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1609_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1607_; 
if (v_isShared_1605_ == 0)
{
v___x_1607_ = v___x_1604_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v_a_1602_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
}
}
}
else
{
lean_object* v_a_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1617_; 
lean_dec(v_snd_1541_);
lean_dec(v_fst_1540_);
lean_dec(v_snd_1536_);
lean_dec(v_fst_1535_);
lean_dec(v_a_1519_);
lean_dec(v_a_1517_);
v_a_1610_ = lean_ctor_get(v___x_1546_, 0);
v_isSharedCheck_1617_ = !lean_is_exclusive(v___x_1546_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1612_ = v___x_1546_;
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_a_1610_);
lean_dec(v___x_1546_);
v___x_1612_ = lean_box(0);
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
v_resetjp_1611_:
{
lean_object* v___x_1615_; 
if (v_isShared_1613_ == 0)
{
v___x_1615_ = v___x_1612_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v_a_1610_);
v___x_1615_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
return v___x_1615_;
}
}
}
}
}
else
{
lean_object* v_a_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1625_; 
lean_dec(v_snd_1541_);
lean_dec(v_fst_1540_);
lean_dec(v_snd_1536_);
lean_dec(v_fst_1535_);
lean_dec(v_a_1519_);
lean_dec(v_a_1517_);
v_a_1618_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1625_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1625_ == 0)
{
v___x_1620_ = v___x_1542_;
v_isShared_1621_ = v_isSharedCheck_1625_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_a_1618_);
lean_dec(v___x_1542_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1625_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
lean_object* v___x_1623_; 
if (v_isShared_1621_ == 0)
{
v___x_1623_ = v___x_1620_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v_a_1618_);
v___x_1623_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
return v___x_1623_;
}
}
}
}
else
{
lean_dec(v_a_1538_);
lean_dec(v_snd_1536_);
lean_dec(v_fst_1535_);
lean_dec(v_a_1519_);
lean_dec(v_a_1517_);
v_as_x27_1480_ = v_tail_1496_;
v_b_1481_ = v___x_1497_;
goto _start;
}
}
else
{
lean_object* v_a_1627_; lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1634_; 
lean_dec(v_snd_1536_);
lean_dec(v_fst_1535_);
lean_dec(v_a_1519_);
lean_dec(v_a_1517_);
v_a_1627_ = lean_ctor_get(v___x_1537_, 0);
v_isSharedCheck_1634_ = !lean_is_exclusive(v___x_1537_);
if (v_isSharedCheck_1634_ == 0)
{
v___x_1629_ = v___x_1537_;
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
else
{
lean_inc(v_a_1627_);
lean_dec(v___x_1537_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
lean_object* v___x_1632_; 
if (v_isShared_1630_ == 0)
{
v___x_1632_ = v___x_1629_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v_a_1627_);
v___x_1632_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
return v___x_1632_;
}
}
}
}
else
{
lean_dec(v_a_1533_);
lean_dec(v_a_1519_);
lean_dec(v_a_1517_);
v_as_x27_1480_ = v_tail_1496_;
v_b_1481_ = v___x_1497_;
goto _start;
}
}
else
{
lean_object* v_a_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1643_; 
lean_dec(v_a_1519_);
lean_dec(v_a_1517_);
v_a_1636_ = lean_ctor_get(v___x_1532_, 0);
v_isSharedCheck_1643_ = !lean_is_exclusive(v___x_1532_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1638_ = v___x_1532_;
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_a_1636_);
lean_dec(v___x_1532_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v___x_1641_; 
if (v_isShared_1639_ == 0)
{
v___x_1641_ = v___x_1638_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_a_1636_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
}
}
}
else
{
lean_object* v_a_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1716_; 
lean_dec(v_a_1517_);
v_a_1709_ = lean_ctor_get(v___x_1518_, 0);
v_isSharedCheck_1716_ = !lean_is_exclusive(v___x_1518_);
if (v_isSharedCheck_1716_ == 0)
{
v___x_1711_ = v___x_1518_;
v_isShared_1712_ = v_isSharedCheck_1716_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_a_1709_);
lean_dec(v___x_1518_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1716_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v___x_1714_; 
if (v_isShared_1712_ == 0)
{
v___x_1714_ = v___x_1711_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v_a_1709_);
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
else
{
lean_object* v_a_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1724_; 
v_a_1717_ = lean_ctor_get(v___x_1516_, 0);
v_isSharedCheck_1724_ = !lean_is_exclusive(v___x_1516_);
if (v_isSharedCheck_1724_ == 0)
{
v___x_1719_ = v___x_1516_;
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_a_1717_);
lean_dec(v___x_1516_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v___x_1722_; 
if (v_isShared_1720_ == 0)
{
v___x_1722_ = v___x_1719_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v_a_1717_);
v___x_1722_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
return v___x_1722_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg___boxed(lean_object* v_as_x27_1725_, lean_object* v_b_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_){
_start:
{
lean_object* v_res_1739_; 
v_res_1739_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg(v_as_x27_1725_, v_b_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_);
lean_dec(v___y_1737_);
lean_dec_ref(v___y_1736_);
lean_dec(v___y_1735_);
lean_dec_ref(v___y_1734_);
lean_dec(v___y_1733_);
lean_dec_ref(v___y_1732_);
lean_dec(v___y_1731_);
lean_dec_ref(v___y_1730_);
lean_dec(v___y_1729_);
lean_dec(v___y_1728_);
lean_dec(v___y_1727_);
lean_dec(v_as_x27_1725_);
return v_res_1739_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending(lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_){
_start:
{
lean_object* v___f_1753_; lean_object* v___x_1754_; 
v___f_1753_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending___closed__0));
v___x_1754_ = l_Lean_Meta_Grind_Order_getStruct___redArg(v_a_1741_, v_a_1742_, v_a_1750_);
if (lean_obj_tag(v___x_1754_) == 0)
{
lean_object* v_a_1755_; lean_object* v_propagate_1756_; lean_object* v___x_1757_; 
v_a_1755_ = lean_ctor_get(v___x_1754_, 0);
lean_inc(v_a_1755_);
lean_dec_ref_known(v___x_1754_, 1);
v_propagate_1756_ = lean_ctor_get(v_a_1755_, 8);
lean_inc(v_propagate_1756_);
lean_dec(v_a_1755_);
v___x_1757_ = l_Lean_Meta_Grind_Order_modifyStruct___redArg(v___f_1753_, v_a_1741_, v_a_1742_);
if (lean_obj_tag(v___x_1757_) == 0)
{
lean_object* v___x_1758_; lean_object* v___x_1759_; 
lean_dec_ref_known(v___x_1757_, 1);
v___x_1758_ = lean_box(0);
v___x_1759_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg(v_propagate_1756_, v___x_1758_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_);
lean_dec(v_propagate_1756_);
if (lean_obj_tag(v___x_1759_) == 0)
{
lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1766_; 
v_isSharedCheck_1766_ = !lean_is_exclusive(v___x_1759_);
if (v_isSharedCheck_1766_ == 0)
{
lean_object* v_unused_1767_; 
v_unused_1767_ = lean_ctor_get(v___x_1759_, 0);
lean_dec(v_unused_1767_);
v___x_1761_ = v___x_1759_;
v_isShared_1762_ = v_isSharedCheck_1766_;
goto v_resetjp_1760_;
}
else
{
lean_dec(v___x_1759_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1766_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v___x_1764_; 
if (v_isShared_1762_ == 0)
{
lean_ctor_set(v___x_1761_, 0, v___x_1758_);
v___x_1764_ = v___x_1761_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v___x_1758_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
return v___x_1764_;
}
}
}
else
{
return v___x_1759_;
}
}
else
{
lean_dec(v_propagate_1756_);
return v___x_1757_;
}
}
else
{
lean_object* v_a_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1775_; 
v_a_1768_ = lean_ctor_get(v___x_1754_, 0);
v_isSharedCheck_1775_ = !lean_is_exclusive(v___x_1754_);
if (v_isSharedCheck_1775_ == 0)
{
v___x_1770_ = v___x_1754_;
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_a_1768_);
lean_dec(v___x_1754_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v___x_1773_; 
if (v_isShared_1771_ == 0)
{
v___x_1773_ = v___x_1770_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v_a_1768_);
v___x_1773_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
return v___x_1773_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending___boxed(lean_object* v_a_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_){
_start:
{
lean_object* v_res_1788_; 
v_res_1788_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending(v_a_1776_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_);
lean_dec(v_a_1786_);
lean_dec_ref(v_a_1785_);
lean_dec(v_a_1784_);
lean_dec_ref(v_a_1783_);
lean_dec(v_a_1782_);
lean_dec_ref(v_a_1781_);
lean_dec(v_a_1780_);
lean_dec_ref(v_a_1779_);
lean_dec(v_a_1778_);
lean_dec(v_a_1777_);
lean_dec(v_a_1776_);
return v_res_1788_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0(lean_object* v_as_1789_, lean_object* v_as_x27_1790_, lean_object* v_b_1791_, lean_object* v_a_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_){
_start:
{
lean_object* v___x_1805_; 
v___x_1805_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg(v_as_x27_1790_, v_b_1791_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_);
return v___x_1805_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___boxed(lean_object* v_as_1806_, lean_object* v_as_x27_1807_, lean_object* v_b_1808_, lean_object* v_a_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_){
_start:
{
lean_object* v_res_1822_; 
v_res_1822_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0(v_as_1806_, v_as_x27_1807_, v_b_1808_, v_a_1809_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_);
lean_dec(v___y_1820_);
lean_dec_ref(v___y_1819_);
lean_dec(v___y_1818_);
lean_dec_ref(v___y_1817_);
lean_dec(v___y_1816_);
lean_dec_ref(v___y_1815_);
lean_dec(v___y_1814_);
lean_dec_ref(v___y_1813_);
lean_dec(v___y_1812_);
lean_dec(v___y_1811_);
lean_dec(v___y_1810_);
lean_dec(v_as_x27_1807_);
lean_dec(v_as_1806_);
return v_res_1822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue___redArg(lean_object* v_e_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_){
_start:
{
lean_object* v___x_1831_; 
v___x_1831_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_1824_, v_a_1828_);
if (lean_obj_tag(v___x_1831_) == 0)
{
lean_object* v_a_1832_; lean_object* v_termMapInv_1833_; lean_object* v___x_1834_; 
v_a_1832_ = lean_ctor_get(v___x_1831_, 0);
lean_inc(v_a_1832_);
lean_dec_ref_known(v___x_1831_, 1);
v_termMapInv_1833_ = lean_ctor_get(v_a_1832_, 4);
lean_inc_ref(v_termMapInv_1833_);
lean_dec(v_a_1832_);
v___x_1834_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMapInv_1833_, v_e_1823_);
lean_dec_ref(v_termMapInv_1833_);
if (lean_obj_tag(v___x_1834_) == 1)
{
lean_object* v_val_1835_; lean_object* v_fst_1836_; lean_object* v___x_1837_; 
lean_dec_ref(v_e_1823_);
v_val_1835_ = lean_ctor_get(v___x_1834_, 0);
lean_inc(v_val_1835_);
lean_dec_ref_known(v___x_1834_, 1);
v_fst_1836_ = lean_ctor_get(v_val_1835_, 0);
lean_inc(v_fst_1836_);
lean_dec(v_val_1835_);
v___x_1837_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_fst_1836_, v_a_1824_);
if (lean_obj_tag(v___x_1837_) == 0)
{
lean_object* v_a_1838_; uint8_t v___x_1839_; 
v_a_1838_ = lean_ctor_get(v___x_1837_, 0);
v___x_1839_ = lean_unbox(v_a_1838_);
if (v___x_1839_ == 0)
{
lean_dec(v_fst_1836_);
return v___x_1837_;
}
else
{
lean_object* v___x_1840_; 
lean_dec_ref_known(v___x_1837_, 1);
v___x_1840_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_fst_1836_, v_a_1824_, v_a_1825_, v_a_1826_, v_a_1827_, v_a_1828_, v_a_1829_);
return v___x_1840_;
}
}
else
{
lean_dec(v_fst_1836_);
return v___x_1837_;
}
}
else
{
lean_object* v___x_1841_; 
lean_dec(v___x_1834_);
v___x_1841_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_e_1823_, v_a_1824_);
if (lean_obj_tag(v___x_1841_) == 0)
{
lean_object* v_a_1842_; uint8_t v___x_1843_; 
v_a_1842_ = lean_ctor_get(v___x_1841_, 0);
v___x_1843_ = lean_unbox(v_a_1842_);
if (v___x_1843_ == 0)
{
lean_dec_ref(v_e_1823_);
return v___x_1841_;
}
else
{
lean_object* v___x_1844_; 
lean_dec_ref_known(v___x_1841_, 1);
v___x_1844_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_1823_, v_a_1824_, v_a_1825_, v_a_1826_, v_a_1827_, v_a_1828_, v_a_1829_);
return v___x_1844_;
}
}
else
{
lean_dec_ref(v_e_1823_);
return v___x_1841_;
}
}
}
else
{
lean_object* v_a_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1852_; 
lean_dec_ref(v_e_1823_);
v_a_1845_ = lean_ctor_get(v___x_1831_, 0);
v_isSharedCheck_1852_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1852_ == 0)
{
v___x_1847_ = v___x_1831_;
v_isShared_1848_ = v_isSharedCheck_1852_;
goto v_resetjp_1846_;
}
else
{
lean_inc(v_a_1845_);
lean_dec(v___x_1831_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue___redArg___boxed(lean_object* v_e_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_){
_start:
{
lean_object* v_res_1861_; 
v_res_1861_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue___redArg(v_e_1853_, v_a_1854_, v_a_1855_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_);
lean_dec(v_a_1859_);
lean_dec_ref(v_a_1858_);
lean_dec(v_a_1857_);
lean_dec_ref(v_a_1856_);
lean_dec_ref(v_a_1855_);
lean_dec(v_a_1854_);
return v_res_1861_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue(lean_object* v_e_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_){
_start:
{
lean_object* v___x_1875_; 
v___x_1875_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue___redArg(v_e_1862_, v_a_1864_, v_a_1868_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_);
return v___x_1875_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue___boxed(lean_object* v_e_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_){
_start:
{
lean_object* v_res_1889_; 
v_res_1889_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue(v_e_1876_, v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_);
lean_dec(v_a_1887_);
lean_dec_ref(v_a_1886_);
lean_dec(v_a_1885_);
lean_dec_ref(v_a_1884_);
lean_dec(v_a_1883_);
lean_dec_ref(v_a_1882_);
lean_dec(v_a_1881_);
lean_dec_ref(v_a_1880_);
lean_dec(v_a_1879_);
lean_dec(v_a_1878_);
lean_dec(v_a_1877_);
return v_res_1889_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__2(void){
_start:
{
lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; 
v___x_1896_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__1));
v___x_1897_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__6));
v___x_1898_ = l_Lean_Name_append(v___x_1897_, v___x_1896_);
return v___x_1898_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4(void){
_start:
{
lean_object* v___x_1900_; lean_object* v___x_1901_; 
v___x_1900_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__3));
v___x_1901_ = l_Lean_stringToMessageData(v___x_1900_);
return v___x_1901_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue(lean_object* v_u_1903_, lean_object* v_v_1904_, lean_object* v_k_1905_, lean_object* v_c_1906_, lean_object* v_e_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_){
_start:
{
lean_object* v___x_1920_; 
lean_inc_ref(v_e_1907_);
v___x_1920_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue___redArg(v_e_1907_, v_a_1909_, v_a_1913_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_);
if (lean_obj_tag(v___x_1920_) == 0)
{
lean_object* v_a_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_2020_; 
v_a_1921_ = lean_ctor_get(v___x_1920_, 0);
v_isSharedCheck_2020_ = !lean_is_exclusive(v___x_1920_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_1923_ = v___x_1920_;
v_isShared_1924_ = v_isSharedCheck_2020_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_a_1921_);
lean_dec(v___x_1920_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_2020_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
uint8_t v___x_1925_; 
v___x_1925_ = lean_unbox(v_a_1921_);
lean_dec(v_a_1921_);
if (v___x_1925_ == 0)
{
lean_object* v_toCold_1926_; lean_object* v_options_1927_; lean_object* v_inheritedTraceOptions_1928_; uint8_t v_hasTrace_1929_; lean_object* v___x_1930_; lean_object* v___y_1932_; lean_object* v___y_1933_; lean_object* v___y_1934_; lean_object* v___y_1935_; lean_object* v___y_1936_; lean_object* v___y_1937_; lean_object* v___y_1938_; lean_object* v___y_1939_; lean_object* v___y_1940_; lean_object* v___y_1941_; lean_object* v___y_1942_; 
v_toCold_1926_ = lean_ctor_get(v_a_1917_, 0);
v_options_1927_ = lean_ctor_get(v_toCold_1926_, 2);
v_inheritedTraceOptions_1928_ = lean_ctor_get(v_toCold_1926_, 11);
v_hasTrace_1929_ = lean_ctor_get_uint8(v_options_1927_, sizeof(void*)*1);
v___x_1930_ = l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(v_c_1906_);
if (v_hasTrace_1929_ == 0)
{
v___y_1932_ = v_a_1908_;
v___y_1933_ = v_a_1909_;
v___y_1934_ = v_a_1910_;
v___y_1935_ = v_a_1911_;
v___y_1936_ = v_a_1912_;
v___y_1937_ = v_a_1913_;
v___y_1938_ = v_a_1914_;
v___y_1939_ = v_a_1915_;
v___y_1940_ = v_a_1916_;
v___y_1941_ = v_a_1917_;
v___y_1942_ = v_a_1918_;
goto v___jp_1931_;
}
else
{
lean_object* v___x_1950_; lean_object* v___x_1951_; uint8_t v___x_1952_; 
v___x_1950_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__1));
v___x_1951_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__2, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__2);
v___x_1952_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1928_, v_options_1927_, v___x_1951_);
if (v___x_1952_ == 0)
{
v___y_1932_ = v_a_1908_;
v___y_1933_ = v_a_1909_;
v___y_1934_ = v_a_1910_;
v___y_1935_ = v_a_1911_;
v___y_1936_ = v_a_1912_;
v___y_1937_ = v_a_1913_;
v___y_1938_ = v_a_1914_;
v___y_1939_ = v_a_1915_;
v___y_1940_ = v_a_1916_;
v___y_1941_ = v_a_1917_;
v___y_1942_ = v_a_1918_;
goto v___jp_1931_;
}
else
{
lean_object* v___x_1953_; 
v___x_1953_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_u_1903_, v_a_1908_, v_a_1909_, v_a_1917_);
if (lean_obj_tag(v___x_1953_) == 0)
{
lean_object* v_a_1954_; lean_object* v___x_1955_; 
v_a_1954_ = lean_ctor_get(v___x_1953_, 0);
lean_inc(v_a_1954_);
lean_dec_ref_known(v___x_1953_, 1);
v___x_1955_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_v_1904_, v_a_1908_, v_a_1909_, v_a_1917_);
if (lean_obj_tag(v___x_1955_) == 0)
{
lean_object* v_a_1956_; lean_object* v___x_1957_; 
v_a_1956_ = lean_ctor_get(v___x_1955_, 0);
lean_inc(v_a_1956_);
lean_dec_ref_known(v___x_1955_, 1);
v___x_1957_ = l_Lean_Meta_Grind_Order_Cnstr_pp___redArg(v_c_1906_, v_a_1908_, v_a_1909_, v_a_1917_);
if (lean_obj_tag(v___x_1957_) == 0)
{
lean_object* v_a_1958_; lean_object* v_k_1959_; uint8_t v_strict_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___y_1964_; lean_object* v___y_1965_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___y_1977_; 
v_a_1958_ = lean_ctor_get(v___x_1957_, 0);
lean_inc(v_a_1958_);
lean_dec_ref_known(v___x_1957_, 1);
v_k_1959_ = lean_ctor_get(v_k_1905_, 0);
v_strict_1960_ = lean_ctor_get_uint8(v_k_1905_, sizeof(void*)*1);
v___x_1961_ = l_Lean_MessageData_ofExpr(v_a_1954_);
v___x_1962_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4);
v___x_1972_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1972_, 0, v___x_1961_);
lean_ctor_set(v___x_1972_, 1, v___x_1962_);
v___x_1973_ = l_Lean_MessageData_ofExpr(v_a_1956_);
v___x_1974_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1974_, 0, v___x_1972_);
lean_ctor_set(v___x_1974_, 1, v___x_1973_);
v___x_1975_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1975_, 0, v___x_1974_);
lean_ctor_set(v___x_1975_, 1, v___x_1962_);
if (v_strict_1960_ == 0)
{
lean_object* v___x_1988_; 
v___x_1988_ = l_Int_repr(v_k_1959_);
v___y_1977_ = v___x_1988_;
goto v___jp_1976_;
}
else
{
lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; 
v___x_1989_ = l_Int_repr(v_k_1959_);
v___x_1990_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5));
v___x_1991_ = lean_string_append(v___x_1989_, v___x_1990_);
v___y_1977_ = v___x_1991_;
goto v___jp_1976_;
}
v___jp_1963_:
{
lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; 
v___x_1966_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1966_, 0, v___y_1965_);
v___x_1967_ = l_Lean_MessageData_ofFormat(v___x_1966_);
v___x_1968_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1968_, 0, v___y_1964_);
lean_ctor_set(v___x_1968_, 1, v___x_1967_);
v___x_1969_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1969_, 0, v___x_1968_);
lean_ctor_set(v___x_1969_, 1, v___x_1962_);
v___x_1970_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1970_, 0, v___x_1969_);
lean_ctor_set(v___x_1970_, 1, v_a_1958_);
v___x_1971_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(v___x_1950_, v___x_1970_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_);
if (lean_obj_tag(v___x_1971_) == 0)
{
lean_dec_ref_known(v___x_1971_, 1);
v___y_1932_ = v_a_1908_;
v___y_1933_ = v_a_1909_;
v___y_1934_ = v_a_1910_;
v___y_1935_ = v_a_1911_;
v___y_1936_ = v_a_1912_;
v___y_1937_ = v_a_1913_;
v___y_1938_ = v_a_1914_;
v___y_1939_ = v_a_1915_;
v___y_1940_ = v_a_1916_;
v___y_1941_ = v_a_1917_;
v___y_1942_ = v_a_1918_;
goto v___jp_1931_;
}
else
{
lean_dec_ref(v___x_1930_);
lean_del_object(v___x_1923_);
lean_dec_ref(v_e_1907_);
lean_dec_ref(v_c_1906_);
lean_dec_ref(v_k_1905_);
lean_dec(v_v_1904_);
lean_dec(v_u_1903_);
return v___x_1971_;
}
}
v___jp_1976_:
{
lean_object* v_k_1978_; uint8_t v_strict_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; 
v_k_1978_ = lean_ctor_get(v___x_1930_, 0);
v_strict_1979_ = lean_ctor_get_uint8(v___x_1930_, sizeof(void*)*1);
v___x_1980_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1980_, 0, v___y_1977_);
v___x_1981_ = l_Lean_MessageData_ofFormat(v___x_1980_);
v___x_1982_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1982_, 0, v___x_1975_);
lean_ctor_set(v___x_1982_, 1, v___x_1981_);
v___x_1983_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1983_, 0, v___x_1982_);
lean_ctor_set(v___x_1983_, 1, v___x_1962_);
if (v_strict_1979_ == 0)
{
lean_object* v___x_1984_; 
v___x_1984_ = l_Int_repr(v_k_1978_);
v___y_1964_ = v___x_1983_;
v___y_1965_ = v___x_1984_;
goto v___jp_1963_;
}
else
{
lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; 
v___x_1985_ = l_Int_repr(v_k_1978_);
v___x_1986_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5));
v___x_1987_ = lean_string_append(v___x_1985_, v___x_1986_);
v___y_1964_ = v___x_1983_;
v___y_1965_ = v___x_1987_;
goto v___jp_1963_;
}
}
}
else
{
lean_object* v_a_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_1999_; 
lean_dec(v_a_1956_);
lean_dec(v_a_1954_);
lean_dec_ref(v___x_1930_);
lean_del_object(v___x_1923_);
lean_dec_ref(v_e_1907_);
lean_dec_ref(v_c_1906_);
lean_dec_ref(v_k_1905_);
lean_dec(v_v_1904_);
lean_dec(v_u_1903_);
v_a_1992_ = lean_ctor_get(v___x_1957_, 0);
v_isSharedCheck_1999_ = !lean_is_exclusive(v___x_1957_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1994_ = v___x_1957_;
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_a_1992_);
lean_dec(v___x_1957_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
lean_object* v___x_1997_; 
if (v_isShared_1995_ == 0)
{
v___x_1997_ = v___x_1994_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v_a_1992_);
v___x_1997_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
return v___x_1997_;
}
}
}
}
else
{
lean_object* v_a_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2007_; 
lean_dec(v_a_1954_);
lean_dec_ref(v___x_1930_);
lean_del_object(v___x_1923_);
lean_dec_ref(v_e_1907_);
lean_dec_ref(v_c_1906_);
lean_dec_ref(v_k_1905_);
lean_dec(v_v_1904_);
lean_dec(v_u_1903_);
v_a_2000_ = lean_ctor_get(v___x_1955_, 0);
v_isSharedCheck_2007_ = !lean_is_exclusive(v___x_1955_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_2002_ = v___x_1955_;
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_a_2000_);
lean_dec(v___x_1955_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v___x_2005_; 
if (v_isShared_2003_ == 0)
{
v___x_2005_ = v___x_2002_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v_a_2000_);
v___x_2005_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
return v___x_2005_;
}
}
}
}
else
{
lean_object* v_a_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2015_; 
lean_dec_ref(v___x_1930_);
lean_del_object(v___x_1923_);
lean_dec_ref(v_e_1907_);
lean_dec_ref(v_c_1906_);
lean_dec_ref(v_k_1905_);
lean_dec(v_v_1904_);
lean_dec(v_u_1903_);
v_a_2008_ = lean_ctor_get(v___x_1953_, 0);
v_isSharedCheck_2015_ = !lean_is_exclusive(v___x_1953_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_2010_ = v___x_1953_;
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_a_2008_);
lean_dec(v___x_1953_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v___x_2013_; 
if (v_isShared_2011_ == 0)
{
v___x_2013_ = v___x_2010_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v_a_2008_);
v___x_2013_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
return v___x_2013_;
}
}
}
}
}
v___jp_1931_:
{
uint8_t v___x_1943_; 
v___x_1943_ = l_Lean_Meta_Grind_Order_instDecidableLEWeight(v_k_1905_, v___x_1930_);
if (v___x_1943_ == 0)
{
lean_object* v___x_1944_; lean_object* v___x_1946_; 
lean_dec_ref(v___x_1930_);
lean_dec_ref(v_e_1907_);
lean_dec_ref(v_c_1906_);
lean_dec_ref(v_k_1905_);
lean_dec(v_v_1904_);
lean_dec(v_u_1903_);
v___x_1944_ = lean_box(0);
if (v_isShared_1924_ == 0)
{
lean_ctor_set(v___x_1923_, 0, v___x_1944_);
v___x_1946_ = v___x_1923_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v___x_1944_);
v___x_1946_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
return v___x_1946_;
}
}
else
{
lean_object* v___x_1948_; lean_object* v___x_1949_; 
lean_del_object(v___x_1923_);
v___x_1948_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1948_, 0, v_c_1906_);
lean_ctor_set(v___x_1948_, 1, v_e_1907_);
lean_ctor_set(v___x_1948_, 2, v_u_1903_);
lean_ctor_set(v___x_1948_, 3, v_v_1904_);
lean_ctor_set(v___x_1948_, 4, v_k_1905_);
lean_ctor_set(v___x_1948_, 5, v___x_1930_);
v___x_1949_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate(v___x_1948_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_);
return v___x_1949_;
}
}
}
else
{
lean_object* v___x_2016_; lean_object* v___x_2018_; 
lean_dec_ref(v_e_1907_);
lean_dec_ref(v_c_1906_);
lean_dec_ref(v_k_1905_);
lean_dec(v_v_1904_);
lean_dec(v_u_1903_);
v___x_2016_ = lean_box(0);
if (v_isShared_1924_ == 0)
{
lean_ctor_set(v___x_1923_, 0, v___x_2016_);
v___x_2018_ = v___x_1923_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v___x_2016_);
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
lean_dec_ref(v_e_1907_);
lean_dec_ref(v_c_1906_);
lean_dec_ref(v_k_1905_);
lean_dec(v_v_1904_);
lean_dec(v_u_1903_);
v_a_2021_ = lean_ctor_get(v___x_1920_, 0);
v_isSharedCheck_2028_ = !lean_is_exclusive(v___x_1920_);
if (v_isSharedCheck_2028_ == 0)
{
v___x_2023_ = v___x_1920_;
v_isShared_2024_ = v_isSharedCheck_2028_;
goto v_resetjp_2022_;
}
else
{
lean_inc(v_a_2021_);
lean_dec(v___x_1920_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___boxed(lean_object** _args){
lean_object* v_u_2029_ = _args[0];
lean_object* v_v_2030_ = _args[1];
lean_object* v_k_2031_ = _args[2];
lean_object* v_c_2032_ = _args[3];
lean_object* v_e_2033_ = _args[4];
lean_object* v_a_2034_ = _args[5];
lean_object* v_a_2035_ = _args[6];
lean_object* v_a_2036_ = _args[7];
lean_object* v_a_2037_ = _args[8];
lean_object* v_a_2038_ = _args[9];
lean_object* v_a_2039_ = _args[10];
lean_object* v_a_2040_ = _args[11];
lean_object* v_a_2041_ = _args[12];
lean_object* v_a_2042_ = _args[13];
lean_object* v_a_2043_ = _args[14];
lean_object* v_a_2044_ = _args[15];
lean_object* v_a_2045_ = _args[16];
_start:
{
lean_object* v_res_2046_; 
v_res_2046_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue(v_u_2029_, v_v_2030_, v_k_2031_, v_c_2032_, v_e_2033_, v_a_2034_, v_a_2035_, v_a_2036_, v_a_2037_, v_a_2038_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_, v_a_2043_, v_a_2044_);
lean_dec(v_a_2044_);
lean_dec_ref(v_a_2043_);
lean_dec(v_a_2042_);
lean_dec_ref(v_a_2041_);
lean_dec(v_a_2040_);
lean_dec_ref(v_a_2039_);
lean_dec(v_a_2038_);
lean_dec_ref(v_a_2037_);
lean_dec(v_a_2036_);
lean_dec(v_a_2035_);
lean_dec(v_a_2034_);
return v_res_2046_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse___redArg(lean_object* v_e_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_){
_start:
{
lean_object* v___x_2055_; 
v___x_2055_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_2048_, v_a_2052_);
if (lean_obj_tag(v___x_2055_) == 0)
{
lean_object* v_a_2056_; lean_object* v_termMapInv_2057_; lean_object* v___x_2058_; 
v_a_2056_ = lean_ctor_get(v___x_2055_, 0);
lean_inc(v_a_2056_);
lean_dec_ref_known(v___x_2055_, 1);
v_termMapInv_2057_ = lean_ctor_get(v_a_2056_, 4);
lean_inc_ref(v_termMapInv_2057_);
lean_dec(v_a_2056_);
v___x_2058_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMapInv_2057_, v_e_2047_);
lean_dec_ref(v_termMapInv_2057_);
if (lean_obj_tag(v___x_2058_) == 1)
{
lean_object* v_val_2059_; lean_object* v_fst_2060_; lean_object* v___x_2061_; 
lean_dec_ref(v_e_2047_);
v_val_2059_ = lean_ctor_get(v___x_2058_, 0);
lean_inc(v_val_2059_);
lean_dec_ref_known(v___x_2058_, 1);
v_fst_2060_ = lean_ctor_get(v_val_2059_, 0);
lean_inc(v_fst_2060_);
lean_dec(v_val_2059_);
v___x_2061_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_fst_2060_, v_a_2048_);
if (lean_obj_tag(v___x_2061_) == 0)
{
lean_object* v_a_2062_; uint8_t v___x_2063_; 
v_a_2062_ = lean_ctor_get(v___x_2061_, 0);
v___x_2063_ = lean_unbox(v_a_2062_);
if (v___x_2063_ == 0)
{
lean_dec(v_fst_2060_);
return v___x_2061_;
}
else
{
lean_object* v___x_2064_; 
lean_dec_ref_known(v___x_2061_, 1);
v___x_2064_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_fst_2060_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_, v_a_2052_, v_a_2053_);
return v___x_2064_;
}
}
else
{
lean_dec(v_fst_2060_);
return v___x_2061_;
}
}
else
{
lean_object* v___x_2065_; 
lean_dec(v___x_2058_);
v___x_2065_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_e_2047_, v_a_2048_);
if (lean_obj_tag(v___x_2065_) == 0)
{
lean_object* v_a_2066_; uint8_t v___x_2067_; 
v_a_2066_ = lean_ctor_get(v___x_2065_, 0);
v___x_2067_ = lean_unbox(v_a_2066_);
if (v___x_2067_ == 0)
{
lean_dec_ref(v_e_2047_);
return v___x_2065_;
}
else
{
lean_object* v___x_2068_; 
lean_dec_ref_known(v___x_2065_, 1);
v___x_2068_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_2047_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_, v_a_2052_, v_a_2053_);
return v___x_2068_;
}
}
else
{
lean_dec_ref(v_e_2047_);
return v___x_2065_;
}
}
}
else
{
lean_object* v_a_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2076_; 
lean_dec_ref(v_e_2047_);
v_a_2069_ = lean_ctor_get(v___x_2055_, 0);
v_isSharedCheck_2076_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2076_ == 0)
{
v___x_2071_ = v___x_2055_;
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_a_2069_);
lean_dec(v___x_2055_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
lean_object* v___x_2074_; 
if (v_isShared_2072_ == 0)
{
v___x_2074_ = v___x_2071_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v_a_2069_);
v___x_2074_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
return v___x_2074_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse___redArg___boxed(lean_object* v_e_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_){
_start:
{
lean_object* v_res_2085_; 
v_res_2085_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse___redArg(v_e_2077_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_, v_a_2083_);
lean_dec(v_a_2083_);
lean_dec_ref(v_a_2082_);
lean_dec(v_a_2081_);
lean_dec_ref(v_a_2080_);
lean_dec_ref(v_a_2079_);
lean_dec(v_a_2078_);
return v_res_2085_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse(lean_object* v_e_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_, lean_object* v_a_2089_, lean_object* v_a_2090_, lean_object* v_a_2091_, lean_object* v_a_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_){
_start:
{
lean_object* v___x_2099_; 
v___x_2099_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse___redArg(v_e_2086_, v_a_2088_, v_a_2092_, v_a_2094_, v_a_2095_, v_a_2096_, v_a_2097_);
return v___x_2099_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse___boxed(lean_object* v_e_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_){
_start:
{
lean_object* v_res_2113_; 
v_res_2113_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse(v_e_2100_, v_a_2101_, v_a_2102_, v_a_2103_, v_a_2104_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_, v_a_2109_, v_a_2110_, v_a_2111_);
lean_dec(v_a_2111_);
lean_dec_ref(v_a_2110_);
lean_dec(v_a_2109_);
lean_dec_ref(v_a_2108_);
lean_dec(v_a_2107_);
lean_dec_ref(v_a_2106_);
lean_dec(v_a_2105_);
lean_dec_ref(v_a_2104_);
lean_dec(v_a_2103_);
lean_dec(v_a_2102_);
lean_dec(v_a_2101_);
return v_res_2113_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__2(void){
_start:
{
lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; 
v___x_2120_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__1));
v___x_2121_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__6));
v___x_2122_ = l_Lean_Name_append(v___x_2121_, v___x_2120_);
return v___x_2122_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__4(void){
_start:
{
lean_object* v___x_2124_; lean_object* v___x_2125_; 
v___x_2124_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__3));
v___x_2125_ = l_Lean_stringToMessageData(v___x_2124_);
return v___x_2125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse(lean_object* v_u_2126_, lean_object* v_v_2127_, lean_object* v_k_2128_, lean_object* v_c_2129_, lean_object* v_e_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_){
_start:
{
lean_object* v___x_2143_; 
lean_inc_ref(v_e_2130_);
v___x_2143_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse___redArg(v_e_2130_, v_a_2132_, v_a_2136_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_);
if (lean_obj_tag(v___x_2143_) == 0)
{
lean_object* v_a_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2245_; 
v_a_2144_ = lean_ctor_get(v___x_2143_, 0);
v_isSharedCheck_2245_ = !lean_is_exclusive(v___x_2143_);
if (v_isSharedCheck_2245_ == 0)
{
v___x_2146_ = v___x_2143_;
v_isShared_2147_ = v_isSharedCheck_2245_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_a_2144_);
lean_dec(v___x_2143_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2245_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
uint8_t v___x_2148_; 
v___x_2148_ = lean_unbox(v_a_2144_);
lean_dec(v_a_2144_);
if (v___x_2148_ == 0)
{
lean_object* v_toCold_2149_; lean_object* v_options_2150_; lean_object* v_inheritedTraceOptions_2151_; uint8_t v_hasTrace_2152_; lean_object* v___x_2153_; lean_object* v___y_2155_; lean_object* v___y_2156_; lean_object* v___y_2157_; lean_object* v___y_2158_; lean_object* v___y_2159_; lean_object* v___y_2160_; lean_object* v___y_2161_; lean_object* v___y_2162_; lean_object* v___y_2163_; lean_object* v___y_2164_; lean_object* v___y_2165_; 
v_toCold_2149_ = lean_ctor_get(v_a_2140_, 0);
v_options_2150_ = lean_ctor_get(v_toCold_2149_, 2);
v_inheritedTraceOptions_2151_ = lean_ctor_get(v_toCold_2149_, 11);
v_hasTrace_2152_ = lean_ctor_get_uint8(v_options_2150_, sizeof(void*)*1);
v___x_2153_ = l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(v_c_2129_);
if (v_hasTrace_2152_ == 0)
{
v___y_2155_ = v_a_2131_;
v___y_2156_ = v_a_2132_;
v___y_2157_ = v_a_2133_;
v___y_2158_ = v_a_2134_;
v___y_2159_ = v_a_2135_;
v___y_2160_ = v_a_2136_;
v___y_2161_ = v_a_2137_;
v___y_2162_ = v_a_2138_;
v___y_2163_ = v_a_2139_;
v___y_2164_ = v_a_2140_;
v___y_2165_ = v_a_2141_;
goto v___jp_2154_;
}
else
{
lean_object* v___x_2174_; lean_object* v___x_2175_; uint8_t v___x_2176_; 
v___x_2174_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__1));
v___x_2175_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__2, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__2);
v___x_2176_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2151_, v_options_2150_, v___x_2175_);
if (v___x_2176_ == 0)
{
v___y_2155_ = v_a_2131_;
v___y_2156_ = v_a_2132_;
v___y_2157_ = v_a_2133_;
v___y_2158_ = v_a_2134_;
v___y_2159_ = v_a_2135_;
v___y_2160_ = v_a_2136_;
v___y_2161_ = v_a_2137_;
v___y_2162_ = v_a_2138_;
v___y_2163_ = v_a_2139_;
v___y_2164_ = v_a_2140_;
v___y_2165_ = v_a_2141_;
goto v___jp_2154_;
}
else
{
lean_object* v___x_2177_; 
v___x_2177_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_u_2126_, v_a_2131_, v_a_2132_, v_a_2140_);
if (lean_obj_tag(v___x_2177_) == 0)
{
lean_object* v_a_2178_; lean_object* v___x_2179_; 
v_a_2178_ = lean_ctor_get(v___x_2177_, 0);
lean_inc(v_a_2178_);
lean_dec_ref_known(v___x_2177_, 1);
v___x_2179_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_v_2127_, v_a_2131_, v_a_2132_, v_a_2140_);
if (lean_obj_tag(v___x_2179_) == 0)
{
lean_object* v_a_2180_; lean_object* v___x_2181_; 
v_a_2180_ = lean_ctor_get(v___x_2179_, 0);
lean_inc(v_a_2180_);
lean_dec_ref_known(v___x_2179_, 1);
v___x_2181_ = l_Lean_Meta_Grind_Order_Cnstr_pp___redArg(v_c_2129_, v_a_2131_, v_a_2132_, v_a_2140_);
if (lean_obj_tag(v___x_2181_) == 0)
{
lean_object* v_a_2182_; lean_object* v___y_2184_; lean_object* v___y_2185_; lean_object* v_k_2193_; uint8_t v_strict_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___y_2202_; 
v_a_2182_ = lean_ctor_get(v___x_2181_, 0);
lean_inc(v_a_2182_);
lean_dec_ref_known(v___x_2181_, 1);
v_k_2193_ = lean_ctor_get(v_k_2128_, 0);
v_strict_2194_ = lean_ctor_get_uint8(v_k_2128_, sizeof(void*)*1);
v___x_2195_ = l_Lean_MessageData_ofExpr(v_a_2178_);
v___x_2196_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4);
v___x_2197_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2197_, 0, v___x_2195_);
lean_ctor_set(v___x_2197_, 1, v___x_2196_);
v___x_2198_ = l_Lean_MessageData_ofExpr(v_a_2180_);
v___x_2199_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2199_, 0, v___x_2197_);
lean_ctor_set(v___x_2199_, 1, v___x_2198_);
v___x_2200_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2200_, 0, v___x_2199_);
lean_ctor_set(v___x_2200_, 1, v___x_2196_);
if (v_strict_2194_ == 0)
{
lean_object* v___x_2213_; 
v___x_2213_ = l_Int_repr(v_k_2193_);
v___y_2202_ = v___x_2213_;
goto v___jp_2201_;
}
else
{
lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; 
v___x_2214_ = l_Int_repr(v_k_2193_);
v___x_2215_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5));
v___x_2216_ = lean_string_append(v___x_2214_, v___x_2215_);
v___y_2202_ = v___x_2216_;
goto v___jp_2201_;
}
v___jp_2183_:
{
lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; 
v___x_2186_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2186_, 0, v___y_2185_);
v___x_2187_ = l_Lean_MessageData_ofFormat(v___x_2186_);
v___x_2188_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2188_, 0, v___y_2184_);
lean_ctor_set(v___x_2188_, 1, v___x_2187_);
v___x_2189_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__4);
v___x_2190_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2190_, 0, v___x_2188_);
lean_ctor_set(v___x_2190_, 1, v___x_2189_);
v___x_2191_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2191_, 0, v___x_2190_);
lean_ctor_set(v___x_2191_, 1, v_a_2182_);
v___x_2192_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(v___x_2174_, v___x_2191_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_);
if (lean_obj_tag(v___x_2192_) == 0)
{
lean_dec_ref_known(v___x_2192_, 1);
v___y_2155_ = v_a_2131_;
v___y_2156_ = v_a_2132_;
v___y_2157_ = v_a_2133_;
v___y_2158_ = v_a_2134_;
v___y_2159_ = v_a_2135_;
v___y_2160_ = v_a_2136_;
v___y_2161_ = v_a_2137_;
v___y_2162_ = v_a_2138_;
v___y_2163_ = v_a_2139_;
v___y_2164_ = v_a_2140_;
v___y_2165_ = v_a_2141_;
goto v___jp_2154_;
}
else
{
lean_dec_ref(v___x_2153_);
lean_del_object(v___x_2146_);
lean_dec_ref(v_e_2130_);
lean_dec_ref(v_c_2129_);
lean_dec_ref(v_k_2128_);
lean_dec(v_v_2127_);
lean_dec(v_u_2126_);
return v___x_2192_;
}
}
v___jp_2201_:
{
lean_object* v_k_2203_; uint8_t v_strict_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; 
v_k_2203_ = lean_ctor_get(v___x_2153_, 0);
v_strict_2204_ = lean_ctor_get_uint8(v___x_2153_, sizeof(void*)*1);
v___x_2205_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2205_, 0, v___y_2202_);
v___x_2206_ = l_Lean_MessageData_ofFormat(v___x_2205_);
v___x_2207_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2207_, 0, v___x_2200_);
lean_ctor_set(v___x_2207_, 1, v___x_2206_);
v___x_2208_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2208_, 0, v___x_2207_);
lean_ctor_set(v___x_2208_, 1, v___x_2196_);
if (v_strict_2204_ == 0)
{
lean_object* v___x_2209_; 
v___x_2209_ = l_Int_repr(v_k_2203_);
v___y_2184_ = v___x_2208_;
v___y_2185_ = v___x_2209_;
goto v___jp_2183_;
}
else
{
lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; 
v___x_2210_ = l_Int_repr(v_k_2203_);
v___x_2211_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5));
v___x_2212_ = lean_string_append(v___x_2210_, v___x_2211_);
v___y_2184_ = v___x_2208_;
v___y_2185_ = v___x_2212_;
goto v___jp_2183_;
}
}
}
else
{
lean_object* v_a_2217_; lean_object* v___x_2219_; uint8_t v_isShared_2220_; uint8_t v_isSharedCheck_2224_; 
lean_dec(v_a_2180_);
lean_dec(v_a_2178_);
lean_dec_ref(v___x_2153_);
lean_del_object(v___x_2146_);
lean_dec_ref(v_e_2130_);
lean_dec_ref(v_c_2129_);
lean_dec_ref(v_k_2128_);
lean_dec(v_v_2127_);
lean_dec(v_u_2126_);
v_a_2217_ = lean_ctor_get(v___x_2181_, 0);
v_isSharedCheck_2224_ = !lean_is_exclusive(v___x_2181_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2219_ = v___x_2181_;
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
else
{
lean_inc(v_a_2217_);
lean_dec(v___x_2181_);
v___x_2219_ = lean_box(0);
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
v_resetjp_2218_:
{
lean_object* v___x_2222_; 
if (v_isShared_2220_ == 0)
{
v___x_2222_ = v___x_2219_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v_a_2217_);
v___x_2222_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
return v___x_2222_;
}
}
}
}
else
{
lean_object* v_a_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2232_; 
lean_dec(v_a_2178_);
lean_dec_ref(v___x_2153_);
lean_del_object(v___x_2146_);
lean_dec_ref(v_e_2130_);
lean_dec_ref(v_c_2129_);
lean_dec_ref(v_k_2128_);
lean_dec(v_v_2127_);
lean_dec(v_u_2126_);
v_a_2225_ = lean_ctor_get(v___x_2179_, 0);
v_isSharedCheck_2232_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2232_ == 0)
{
v___x_2227_ = v___x_2179_;
v_isShared_2228_ = v_isSharedCheck_2232_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_a_2225_);
lean_dec(v___x_2179_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2232_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v___x_2230_; 
if (v_isShared_2228_ == 0)
{
v___x_2230_ = v___x_2227_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v_a_2225_);
v___x_2230_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
return v___x_2230_;
}
}
}
}
else
{
lean_object* v_a_2233_; lean_object* v___x_2235_; uint8_t v_isShared_2236_; uint8_t v_isSharedCheck_2240_; 
lean_dec_ref(v___x_2153_);
lean_del_object(v___x_2146_);
lean_dec_ref(v_e_2130_);
lean_dec_ref(v_c_2129_);
lean_dec_ref(v_k_2128_);
lean_dec(v_v_2127_);
lean_dec(v_u_2126_);
v_a_2233_ = lean_ctor_get(v___x_2177_, 0);
v_isSharedCheck_2240_ = !lean_is_exclusive(v___x_2177_);
if (v_isSharedCheck_2240_ == 0)
{
v___x_2235_ = v___x_2177_;
v_isShared_2236_ = v_isSharedCheck_2240_;
goto v_resetjp_2234_;
}
else
{
lean_inc(v_a_2233_);
lean_dec(v___x_2177_);
v___x_2235_ = lean_box(0);
v_isShared_2236_ = v_isSharedCheck_2240_;
goto v_resetjp_2234_;
}
v_resetjp_2234_:
{
lean_object* v___x_2238_; 
if (v_isShared_2236_ == 0)
{
v___x_2238_ = v___x_2235_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v_a_2233_);
v___x_2238_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
return v___x_2238_;
}
}
}
}
}
v___jp_2154_:
{
lean_object* v___x_2166_; uint8_t v___x_2167_; 
lean_inc_ref(v___x_2153_);
v___x_2166_ = l_Lean_Meta_Grind_Order_Weight_add(v_k_2128_, v___x_2153_);
v___x_2167_ = l_Lean_Meta_Grind_Order_Weight_isNeg(v___x_2166_);
lean_dec_ref(v___x_2166_);
if (v___x_2167_ == 0)
{
lean_object* v___x_2168_; lean_object* v___x_2170_; 
lean_dec_ref(v___x_2153_);
lean_dec_ref(v_e_2130_);
lean_dec_ref(v_c_2129_);
lean_dec_ref(v_k_2128_);
lean_dec(v_v_2127_);
lean_dec(v_u_2126_);
v___x_2168_ = lean_box(0);
if (v_isShared_2147_ == 0)
{
lean_ctor_set(v___x_2146_, 0, v___x_2168_);
v___x_2170_ = v___x_2146_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v___x_2168_);
v___x_2170_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
return v___x_2170_;
}
}
else
{
lean_object* v___x_2172_; lean_object* v___x_2173_; 
lean_del_object(v___x_2146_);
v___x_2172_ = lean_alloc_ctor(1, 6, 0);
lean_ctor_set(v___x_2172_, 0, v_c_2129_);
lean_ctor_set(v___x_2172_, 1, v_e_2130_);
lean_ctor_set(v___x_2172_, 2, v_u_2126_);
lean_ctor_set(v___x_2172_, 3, v_v_2127_);
lean_ctor_set(v___x_2172_, 4, v_k_2128_);
lean_ctor_set(v___x_2172_, 5, v___x_2153_);
v___x_2173_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate(v___x_2172_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_);
return v___x_2173_;
}
}
}
else
{
lean_object* v___x_2241_; lean_object* v___x_2243_; 
lean_dec_ref(v_e_2130_);
lean_dec_ref(v_c_2129_);
lean_dec_ref(v_k_2128_);
lean_dec(v_v_2127_);
lean_dec(v_u_2126_);
v___x_2241_ = lean_box(0);
if (v_isShared_2147_ == 0)
{
lean_ctor_set(v___x_2146_, 0, v___x_2241_);
v___x_2243_ = v___x_2146_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v___x_2241_);
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
lean_dec_ref(v_e_2130_);
lean_dec_ref(v_c_2129_);
lean_dec_ref(v_k_2128_);
lean_dec(v_v_2127_);
lean_dec(v_u_2126_);
v_a_2246_ = lean_ctor_get(v___x_2143_, 0);
v_isSharedCheck_2253_ = !lean_is_exclusive(v___x_2143_);
if (v_isSharedCheck_2253_ == 0)
{
v___x_2248_ = v___x_2143_;
v_isShared_2249_ = v_isSharedCheck_2253_;
goto v_resetjp_2247_;
}
else
{
lean_inc(v_a_2246_);
lean_dec(v___x_2143_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___boxed(lean_object** _args){
lean_object* v_u_2254_ = _args[0];
lean_object* v_v_2255_ = _args[1];
lean_object* v_k_2256_ = _args[2];
lean_object* v_c_2257_ = _args[3];
lean_object* v_e_2258_ = _args[4];
lean_object* v_a_2259_ = _args[5];
lean_object* v_a_2260_ = _args[6];
lean_object* v_a_2261_ = _args[7];
lean_object* v_a_2262_ = _args[8];
lean_object* v_a_2263_ = _args[9];
lean_object* v_a_2264_ = _args[10];
lean_object* v_a_2265_ = _args[11];
lean_object* v_a_2266_ = _args[12];
lean_object* v_a_2267_ = _args[13];
lean_object* v_a_2268_ = _args[14];
lean_object* v_a_2269_ = _args[15];
lean_object* v_a_2270_ = _args[16];
_start:
{
lean_object* v_res_2271_; 
v_res_2271_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse(v_u_2254_, v_v_2255_, v_k_2256_, v_c_2257_, v_e_2258_, v_a_2259_, v_a_2260_, v_a_2261_, v_a_2262_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_, v_a_2269_);
lean_dec(v_a_2269_);
lean_dec_ref(v_a_2268_);
lean_dec(v_a_2267_);
lean_dec_ref(v_a_2266_);
lean_dec(v_a_2265_);
lean_dec_ref(v_a_2264_);
lean_dec(v_a_2263_);
lean_dec_ref(v_a_2262_);
lean_dec(v_a_2261_);
lean_dec(v_a_2260_);
lean_dec(v_a_2259_);
return v_res_2271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___lam__0(lean_object* v_f_2272_, lean_object* v_x_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_){
_start:
{
lean_object* v_fst_2286_; lean_object* v_snd_2287_; lean_object* v___x_2288_; 
v_fst_2286_ = lean_ctor_get(v_x_2273_, 0);
lean_inc(v_fst_2286_);
v_snd_2287_ = lean_ctor_get(v_x_2273_, 1);
lean_inc(v_snd_2287_);
lean_dec_ref(v_x_2273_);
lean_inc(v___y_2284_);
lean_inc_ref(v___y_2283_);
lean_inc(v___y_2282_);
lean_inc_ref(v___y_2281_);
lean_inc(v___y_2280_);
lean_inc_ref(v___y_2279_);
lean_inc(v___y_2278_);
lean_inc_ref(v___y_2277_);
lean_inc(v___y_2276_);
lean_inc(v___y_2275_);
lean_inc(v___y_2274_);
v___x_2288_ = lean_apply_14(v_f_2272_, v_fst_2286_, v_snd_2287_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, lean_box(0));
return v___x_2288_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___lam__0___boxed(lean_object* v_f_2289_, lean_object* v_x_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_){
_start:
{
lean_object* v_res_2303_; 
v_res_2303_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___lam__0(v_f_2289_, v_x_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_);
lean_dec(v___y_2301_);
lean_dec_ref(v___y_2300_);
lean_dec(v___y_2299_);
lean_dec_ref(v___y_2298_);
lean_dec(v___y_2297_);
lean_dec_ref(v___y_2296_);
lean_dec(v___y_2295_);
lean_dec_ref(v___y_2294_);
lean_dec(v___y_2293_);
lean_dec(v___y_2292_);
lean_dec(v___y_2291_);
return v_res_2303_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__0(void){
_start:
{
lean_object* v___x_2304_; 
v___x_2304_ = l_instMonadEIO___redArg();
return v___x_2304_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__1(void){
_start:
{
lean_object* v___x_2305_; lean_object* v___x_2306_; 
v___x_2305_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__0, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__0);
v___x_2306_ = l_StateRefT_x27_instMonad___redArg(v___x_2305_);
return v___x_2306_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__8(void){
_start:
{
lean_object* v___x_2314_; lean_object* v___f_2315_; 
v___x_2314_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
v___f_2315_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2315_, 0, v___x_2314_);
return v___f_2315_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__9(void){
_start:
{
lean_object* v___f_2316_; lean_object* v___f_2317_; 
v___f_2316_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__8, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__8);
v___f_2317_ = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(v___f_2317_, 0, v___f_2316_);
lean_closure_set(v___f_2317_, 1, v___f_2316_);
return v___f_2317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf(lean_object* v_u_2318_, lean_object* v_v_2319_, lean_object* v_f_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_){
_start:
{
lean_object* v___x_2333_; lean_object* v_toApplicative_2334_; lean_object* v_toFunctor_2335_; lean_object* v_toSeq_2336_; lean_object* v_toSeqLeft_2337_; lean_object* v_toSeqRight_2338_; lean_object* v___f_2339_; lean_object* v___f_2340_; lean_object* v___f_2341_; lean_object* v___f_2342_; lean_object* v___x_2343_; lean_object* v___f_2344_; lean_object* v___f_2345_; lean_object* v___f_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v_toApplicative_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2411_; 
v___x_2333_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__1, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__1);
v_toApplicative_2334_ = lean_ctor_get(v___x_2333_, 0);
v_toFunctor_2335_ = lean_ctor_get(v_toApplicative_2334_, 0);
v_toSeq_2336_ = lean_ctor_get(v_toApplicative_2334_, 2);
v_toSeqLeft_2337_ = lean_ctor_get(v_toApplicative_2334_, 3);
v_toSeqRight_2338_ = lean_ctor_get(v_toApplicative_2334_, 4);
v___f_2339_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__2));
v___f_2340_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__3));
lean_inc_ref_n(v_toFunctor_2335_, 2);
v___f_2341_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2341_, 0, v_toFunctor_2335_);
v___f_2342_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2342_, 0, v_toFunctor_2335_);
v___x_2343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2343_, 0, v___f_2341_);
lean_ctor_set(v___x_2343_, 1, v___f_2342_);
lean_inc(v_toSeqRight_2338_);
v___f_2344_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2344_, 0, v_toSeqRight_2338_);
lean_inc(v_toSeqLeft_2337_);
v___f_2345_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2345_, 0, v_toSeqLeft_2337_);
lean_inc(v_toSeq_2336_);
v___f_2346_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2346_, 0, v_toSeq_2336_);
v___x_2347_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2347_, 0, v___x_2343_);
lean_ctor_set(v___x_2347_, 1, v___f_2339_);
lean_ctor_set(v___x_2347_, 2, v___f_2346_);
lean_ctor_set(v___x_2347_, 3, v___f_2345_);
lean_ctor_set(v___x_2347_, 4, v___f_2344_);
v___x_2348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2348_, 0, v___x_2347_);
lean_ctor_set(v___x_2348_, 1, v___f_2340_);
v___x_2349_ = l_StateRefT_x27_instMonad___redArg(v___x_2348_);
v_toApplicative_2350_ = lean_ctor_get(v___x_2349_, 0);
v_isSharedCheck_2411_ = !lean_is_exclusive(v___x_2349_);
if (v_isSharedCheck_2411_ == 0)
{
lean_object* v_unused_2412_; 
v_unused_2412_ = lean_ctor_get(v___x_2349_, 1);
lean_dec(v_unused_2412_);
v___x_2352_ = v___x_2349_;
v_isShared_2353_ = v_isSharedCheck_2411_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_toApplicative_2350_);
lean_dec(v___x_2349_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2411_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v_toFunctor_2354_; lean_object* v_toSeq_2355_; lean_object* v_toSeqLeft_2356_; lean_object* v_toSeqRight_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2409_; 
v_toFunctor_2354_ = lean_ctor_get(v_toApplicative_2350_, 0);
v_toSeq_2355_ = lean_ctor_get(v_toApplicative_2350_, 2);
v_toSeqLeft_2356_ = lean_ctor_get(v_toApplicative_2350_, 3);
v_toSeqRight_2357_ = lean_ctor_get(v_toApplicative_2350_, 4);
v_isSharedCheck_2409_ = !lean_is_exclusive(v_toApplicative_2350_);
if (v_isSharedCheck_2409_ == 0)
{
lean_object* v_unused_2410_; 
v_unused_2410_ = lean_ctor_get(v_toApplicative_2350_, 1);
lean_dec(v_unused_2410_);
v___x_2359_ = v_toApplicative_2350_;
v_isShared_2360_ = v_isSharedCheck_2409_;
goto v_resetjp_2358_;
}
else
{
lean_inc(v_toSeqRight_2357_);
lean_inc(v_toSeqLeft_2356_);
lean_inc(v_toSeq_2355_);
lean_inc(v_toFunctor_2354_);
lean_dec(v_toApplicative_2350_);
v___x_2359_ = lean_box(0);
v_isShared_2360_ = v_isSharedCheck_2409_;
goto v_resetjp_2358_;
}
v_resetjp_2358_:
{
lean_object* v___f_2361_; lean_object* v___f_2362_; lean_object* v___f_2363_; lean_object* v___f_2364_; lean_object* v___f_2365_; lean_object* v___x_2366_; lean_object* v___f_2367_; lean_object* v___f_2368_; lean_object* v___f_2369_; lean_object* v___x_2371_; 
v___f_2361_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___lam__0___boxed), 14, 1);
lean_closure_set(v___f_2361_, 0, v_f_2320_);
v___f_2362_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__4));
v___f_2363_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__5));
lean_inc_ref(v_toFunctor_2354_);
v___f_2364_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2364_, 0, v_toFunctor_2354_);
v___f_2365_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2365_, 0, v_toFunctor_2354_);
v___x_2366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2366_, 0, v___f_2364_);
lean_ctor_set(v___x_2366_, 1, v___f_2365_);
v___f_2367_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2367_, 0, v_toSeqRight_2357_);
v___f_2368_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2368_, 0, v_toSeqLeft_2356_);
v___f_2369_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2369_, 0, v_toSeq_2355_);
if (v_isShared_2360_ == 0)
{
lean_ctor_set(v___x_2359_, 4, v___f_2367_);
lean_ctor_set(v___x_2359_, 3, v___f_2368_);
lean_ctor_set(v___x_2359_, 2, v___f_2369_);
lean_ctor_set(v___x_2359_, 1, v___f_2362_);
lean_ctor_set(v___x_2359_, 0, v___x_2366_);
v___x_2371_ = v___x_2359_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2408_; 
v_reuseFailAlloc_2408_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2408_, 0, v___x_2366_);
lean_ctor_set(v_reuseFailAlloc_2408_, 1, v___f_2362_);
lean_ctor_set(v_reuseFailAlloc_2408_, 2, v___f_2369_);
lean_ctor_set(v_reuseFailAlloc_2408_, 3, v___f_2368_);
lean_ctor_set(v_reuseFailAlloc_2408_, 4, v___f_2367_);
v___x_2371_ = v_reuseFailAlloc_2408_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
lean_object* v___x_2373_; 
if (v_isShared_2353_ == 0)
{
lean_ctor_set(v___x_2352_, 1, v___f_2363_);
lean_ctor_set(v___x_2352_, 0, v___x_2371_);
v___x_2373_ = v___x_2352_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v___x_2371_);
lean_ctor_set(v_reuseFailAlloc_2407_, 1, v___f_2363_);
v___x_2373_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___f_2381_; lean_object* v___x_2382_; 
v___x_2374_ = l_StateRefT_x27_instMonad___redArg(v___x_2373_);
v___x_2375_ = l_ReaderT_instMonad___redArg(v___x_2374_);
v___x_2376_ = l_StateRefT_x27_instMonad___redArg(v___x_2375_);
v___x_2377_ = l_ReaderT_instMonad___redArg(v___x_2376_);
v___x_2378_ = l_ReaderT_instMonad___redArg(v___x_2377_);
v___x_2379_ = l_StateRefT_x27_instMonad___redArg(v___x_2378_);
v___x_2380_ = l_ReaderT_instMonad___redArg(v___x_2379_);
v___f_2381_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__7));
v___x_2382_ = l_Lean_Meta_Grind_Order_getStruct___redArg(v_a_2321_, v_a_2322_, v_a_2330_);
if (lean_obj_tag(v___x_2382_) == 0)
{
lean_object* v_a_2383_; lean_object* v___x_2385_; uint8_t v_isShared_2386_; uint8_t v_isSharedCheck_2398_; 
v_a_2383_ = lean_ctor_get(v___x_2382_, 0);
v_isSharedCheck_2398_ = !lean_is_exclusive(v___x_2382_);
if (v_isSharedCheck_2398_ == 0)
{
v___x_2385_ = v___x_2382_;
v_isShared_2386_ = v_isSharedCheck_2398_;
goto v_resetjp_2384_;
}
else
{
lean_inc(v_a_2383_);
lean_dec(v___x_2382_);
v___x_2385_ = lean_box(0);
v_isShared_2386_ = v_isSharedCheck_2398_;
goto v_resetjp_2384_;
}
v_resetjp_2384_:
{
lean_object* v___f_2387_; lean_object* v_cnstrsOf_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; 
v___f_2387_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__9, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__9);
v_cnstrsOf_2388_ = lean_ctor_get(v_a_2383_, 4);
lean_inc_ref(v_cnstrsOf_2388_);
lean_dec(v_a_2383_);
v___x_2389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2389_, 0, v_u_2318_);
lean_ctor_set(v___x_2389_, 1, v_v_2319_);
v___x_2390_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_2387_, v___f_2381_, v_cnstrsOf_2388_, v___x_2389_);
lean_dec_ref(v_cnstrsOf_2388_);
if (lean_obj_tag(v___x_2390_) == 1)
{
lean_object* v_val_2391_; lean_object* v___x_1500__overap_2392_; lean_object* v___x_2393_; 
lean_del_object(v___x_2385_);
v_val_2391_ = lean_ctor_get(v___x_2390_, 0);
lean_inc(v_val_2391_);
lean_dec_ref_known(v___x_2390_, 1);
v___x_1500__overap_2392_ = l_List_forM___redArg(v___x_2380_, v_val_2391_, v___f_2361_);
lean_inc(v_a_2331_);
lean_inc_ref(v_a_2330_);
lean_inc(v_a_2329_);
lean_inc_ref(v_a_2328_);
lean_inc(v_a_2327_);
lean_inc_ref(v_a_2326_);
lean_inc(v_a_2325_);
lean_inc_ref(v_a_2324_);
lean_inc(v_a_2323_);
lean_inc(v_a_2322_);
lean_inc(v_a_2321_);
v___x_2393_ = lean_apply_12(v___x_1500__overap_2392_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_, v_a_2331_, lean_box(0));
return v___x_2393_;
}
else
{
lean_object* v___x_2394_; lean_object* v___x_2396_; 
lean_dec(v___x_2390_);
lean_dec_ref(v___x_2380_);
lean_dec_ref(v___f_2361_);
v___x_2394_ = lean_box(0);
if (v_isShared_2386_ == 0)
{
lean_ctor_set(v___x_2385_, 0, v___x_2394_);
v___x_2396_ = v___x_2385_;
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
}
else
{
lean_object* v_a_2399_; lean_object* v___x_2401_; uint8_t v_isShared_2402_; uint8_t v_isSharedCheck_2406_; 
lean_dec_ref(v___x_2380_);
lean_dec_ref(v___f_2361_);
lean_dec(v_v_2319_);
lean_dec(v_u_2318_);
v_a_2399_ = lean_ctor_get(v___x_2382_, 0);
v_isSharedCheck_2406_ = !lean_is_exclusive(v___x_2382_);
if (v_isSharedCheck_2406_ == 0)
{
v___x_2401_ = v___x_2382_;
v_isShared_2402_ = v_isSharedCheck_2406_;
goto v_resetjp_2400_;
}
else
{
lean_inc(v_a_2399_);
lean_dec(v___x_2382_);
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
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___boxed(lean_object* v_u_2413_, lean_object* v_v_2414_, lean_object* v_f_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_){
_start:
{
lean_object* v_res_2428_; 
v_res_2428_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf(v_u_2413_, v_v_2414_, v_f_2415_, v_a_2416_, v_a_2417_, v_a_2418_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_);
lean_dec(v_a_2426_);
lean_dec_ref(v_a_2425_);
lean_dec(v_a_2424_);
lean_dec_ref(v_a_2423_);
lean_dec(v_a_2422_);
lean_dec_ref(v_a_2421_);
lean_dec(v_a_2420_);
lean_dec_ref(v_a_2419_);
lean_dec(v_a_2418_);
lean_dec(v_a_2417_);
lean_dec(v_a_2416_);
return v_res_2428_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___redArg(lean_object* v_e_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_){
_start:
{
lean_object* v___x_2433_; 
v___x_2433_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_2430_, v_a_2431_);
if (lean_obj_tag(v___x_2433_) == 0)
{
lean_object* v_a_2434_; lean_object* v___x_2436_; uint8_t v_isShared_2437_; uint8_t v_isSharedCheck_2456_; 
v_a_2434_ = lean_ctor_get(v___x_2433_, 0);
v_isSharedCheck_2456_ = !lean_is_exclusive(v___x_2433_);
if (v_isSharedCheck_2456_ == 0)
{
v___x_2436_ = v___x_2433_;
v_isShared_2437_ = v_isSharedCheck_2456_;
goto v_resetjp_2435_;
}
else
{
lean_inc(v_a_2434_);
lean_dec(v___x_2433_);
v___x_2436_ = lean_box(0);
v_isShared_2437_ = v_isSharedCheck_2456_;
goto v_resetjp_2435_;
}
v_resetjp_2435_:
{
lean_object* v_termMapInv_2438_; lean_object* v___x_2439_; 
v_termMapInv_2438_ = lean_ctor_get(v_a_2434_, 4);
lean_inc_ref(v_termMapInv_2438_);
lean_dec(v_a_2434_);
v___x_2439_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMapInv_2438_, v_e_2429_);
lean_dec_ref(v_termMapInv_2438_);
if (lean_obj_tag(v___x_2439_) == 1)
{
lean_object* v_val_2440_; lean_object* v___x_2442_; uint8_t v_isShared_2443_; uint8_t v_isSharedCheck_2451_; 
v_val_2440_ = lean_ctor_get(v___x_2439_, 0);
v_isSharedCheck_2451_ = !lean_is_exclusive(v___x_2439_);
if (v_isSharedCheck_2451_ == 0)
{
v___x_2442_ = v___x_2439_;
v_isShared_2443_ = v_isSharedCheck_2451_;
goto v_resetjp_2441_;
}
else
{
lean_inc(v_val_2440_);
lean_dec(v___x_2439_);
v___x_2442_ = lean_box(0);
v_isShared_2443_ = v_isSharedCheck_2451_;
goto v_resetjp_2441_;
}
v_resetjp_2441_:
{
lean_object* v_fst_2444_; lean_object* v___x_2446_; 
v_fst_2444_ = lean_ctor_get(v_val_2440_, 0);
lean_inc(v_fst_2444_);
lean_dec(v_val_2440_);
if (v_isShared_2443_ == 0)
{
lean_ctor_set(v___x_2442_, 0, v_fst_2444_);
v___x_2446_ = v___x_2442_;
goto v_reusejp_2445_;
}
else
{
lean_object* v_reuseFailAlloc_2450_; 
v_reuseFailAlloc_2450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2450_, 0, v_fst_2444_);
v___x_2446_ = v_reuseFailAlloc_2450_;
goto v_reusejp_2445_;
}
v_reusejp_2445_:
{
lean_object* v___x_2448_; 
if (v_isShared_2437_ == 0)
{
lean_ctor_set(v___x_2436_, 0, v___x_2446_);
v___x_2448_ = v___x_2436_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v___x_2446_);
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
lean_object* v___x_2452_; lean_object* v___x_2454_; 
lean_dec(v___x_2439_);
v___x_2452_ = lean_box(0);
if (v_isShared_2437_ == 0)
{
lean_ctor_set(v___x_2436_, 0, v___x_2452_);
v___x_2454_ = v___x_2436_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2455_; 
v_reuseFailAlloc_2455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2455_, 0, v___x_2452_);
v___x_2454_ = v_reuseFailAlloc_2455_;
goto v_reusejp_2453_;
}
v_reusejp_2453_:
{
return v___x_2454_;
}
}
}
}
else
{
lean_object* v_a_2457_; lean_object* v___x_2459_; uint8_t v_isShared_2460_; uint8_t v_isSharedCheck_2464_; 
v_a_2457_ = lean_ctor_get(v___x_2433_, 0);
v_isSharedCheck_2464_ = !lean_is_exclusive(v___x_2433_);
if (v_isSharedCheck_2464_ == 0)
{
v___x_2459_ = v___x_2433_;
v_isShared_2460_ = v_isSharedCheck_2464_;
goto v_resetjp_2458_;
}
else
{
lean_inc(v_a_2457_);
lean_dec(v___x_2433_);
v___x_2459_ = lean_box(0);
v_isShared_2460_ = v_isSharedCheck_2464_;
goto v_resetjp_2458_;
}
v_resetjp_2458_:
{
lean_object* v___x_2462_; 
if (v_isShared_2460_ == 0)
{
v___x_2462_ = v___x_2459_;
goto v_reusejp_2461_;
}
else
{
lean_object* v_reuseFailAlloc_2463_; 
v_reuseFailAlloc_2463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2463_, 0, v_a_2457_);
v___x_2462_ = v_reuseFailAlloc_2463_;
goto v_reusejp_2461_;
}
v_reusejp_2461_:
{
return v___x_2462_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___redArg___boxed(lean_object* v_e_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_){
_start:
{
lean_object* v_res_2469_; 
v_res_2469_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___redArg(v_e_2465_, v_a_2466_, v_a_2467_);
lean_dec_ref(v_a_2467_);
lean_dec(v_a_2466_);
lean_dec_ref(v_e_2465_);
return v_res_2469_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f(lean_object* v_e_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_, lean_object* v_a_2480_){
_start:
{
lean_object* v___x_2482_; 
v___x_2482_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___redArg(v_e_2470_, v_a_2471_, v_a_2479_);
return v___x_2482_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___boxed(lean_object* v_e_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_){
_start:
{
lean_object* v_res_2495_; 
v_res_2495_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f(v_e_2483_, v_a_2484_, v_a_2485_, v_a_2486_, v_a_2487_, v_a_2488_, v_a_2489_, v_a_2490_, v_a_2491_, v_a_2492_, v_a_2493_);
lean_dec(v_a_2493_);
lean_dec_ref(v_a_2492_);
lean_dec(v_a_2491_);
lean_dec_ref(v_a_2490_);
lean_dec(v_a_2489_);
lean_dec_ref(v_a_2488_);
lean_dec(v_a_2487_);
lean_dec_ref(v_a_2486_);
lean_dec(v_a_2485_);
lean_dec(v_a_2484_);
lean_dec_ref(v_e_2483_);
return v_res_2495_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq(lean_object* v_u_2496_, lean_object* v_v_2497_, lean_object* v_k_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_){
_start:
{
uint8_t v___x_2514_; 
v___x_2514_ = lean_nat_dec_eq(v_u_2496_, v_v_2497_);
if (v___x_2514_ == 0)
{
lean_object* v___x_2515_; 
v___x_2515_ = l_Lean_Meta_Grind_Order_isPartialOrder(v_a_2499_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_, v_a_2504_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_);
if (lean_obj_tag(v___x_2515_) == 0)
{
lean_object* v_a_2516_; lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2699_; 
v_a_2516_ = lean_ctor_get(v___x_2515_, 0);
v_isSharedCheck_2699_ = !lean_is_exclusive(v___x_2515_);
if (v_isSharedCheck_2699_ == 0)
{
v___x_2518_ = v___x_2515_;
v_isShared_2519_ = v_isSharedCheck_2699_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_a_2516_);
lean_dec(v___x_2515_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2699_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
uint8_t v___x_2520_; 
v___x_2520_ = lean_unbox(v_a_2516_);
lean_dec(v_a_2516_);
if (v___x_2520_ == 0)
{
lean_object* v___x_2521_; lean_object* v___x_2523_; 
lean_dec(v_v_2497_);
lean_dec(v_u_2496_);
v___x_2521_ = lean_box(0);
if (v_isShared_2519_ == 0)
{
lean_ctor_set(v___x_2518_, 0, v___x_2521_);
v___x_2523_ = v___x_2518_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v___x_2521_);
v___x_2523_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
return v___x_2523_;
}
}
else
{
uint8_t v___x_2525_; 
v___x_2525_ = l_Lean_Meta_Grind_Order_Weight_isZero(v_k_2498_);
if (v___x_2525_ == 0)
{
lean_object* v___x_2526_; lean_object* v___x_2528_; 
lean_dec(v_v_2497_);
lean_dec(v_u_2496_);
v___x_2526_ = lean_box(0);
if (v_isShared_2519_ == 0)
{
lean_ctor_set(v___x_2518_, 0, v___x_2526_);
v___x_2528_ = v___x_2518_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2529_; 
v_reuseFailAlloc_2529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2529_, 0, v___x_2526_);
v___x_2528_ = v_reuseFailAlloc_2529_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
return v___x_2528_;
}
}
else
{
lean_object* v___x_2530_; 
lean_del_object(v___x_2518_);
v___x_2530_ = l_Lean_Meta_Grind_Order_getDist_x3f___redArg(v_v_2497_, v_u_2496_, v_a_2499_, v_a_2500_, v_a_2508_);
if (lean_obj_tag(v___x_2530_) == 0)
{
lean_object* v_a_2531_; lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2690_; 
v_a_2531_ = lean_ctor_get(v___x_2530_, 0);
v_isSharedCheck_2690_ = !lean_is_exclusive(v___x_2530_);
if (v_isSharedCheck_2690_ == 0)
{
v___x_2533_ = v___x_2530_;
v_isShared_2534_ = v_isSharedCheck_2690_;
goto v_resetjp_2532_;
}
else
{
lean_inc(v_a_2531_);
lean_dec(v___x_2530_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2690_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
if (lean_obj_tag(v_a_2531_) == 1)
{
lean_object* v_val_2535_; uint8_t v___x_2536_; 
v_val_2535_ = lean_ctor_get(v_a_2531_, 0);
lean_inc(v_val_2535_);
lean_dec_ref_known(v_a_2531_, 1);
v___x_2536_ = l_Lean_Meta_Grind_Order_Weight_isZero(v_val_2535_);
lean_dec(v_val_2535_);
if (v___x_2536_ == 0)
{
lean_object* v___x_2537_; lean_object* v___x_2539_; 
lean_dec(v_v_2497_);
lean_dec(v_u_2496_);
v___x_2537_ = lean_box(0);
if (v_isShared_2534_ == 0)
{
lean_ctor_set(v___x_2533_, 0, v___x_2537_);
v___x_2539_ = v___x_2533_;
goto v_reusejp_2538_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v___x_2537_);
v___x_2539_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2538_;
}
v_reusejp_2538_:
{
return v___x_2539_;
}
}
else
{
lean_object* v___x_2541_; 
lean_del_object(v___x_2533_);
v___x_2541_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_u_2496_, v_a_2499_, v_a_2500_, v_a_2508_);
if (lean_obj_tag(v___x_2541_) == 0)
{
lean_object* v_a_2542_; lean_object* v___x_2543_; 
v_a_2542_ = lean_ctor_get(v___x_2541_, 0);
lean_inc(v_a_2542_);
lean_dec_ref_known(v___x_2541_, 1);
v___x_2543_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_v_2497_, v_a_2499_, v_a_2500_, v_a_2508_);
if (lean_obj_tag(v___x_2543_) == 0)
{
lean_object* v_a_2544_; lean_object* v___x_2627_; 
v_a_2544_ = lean_ctor_get(v___x_2543_, 0);
lean_inc(v_a_2544_);
lean_dec_ref_known(v___x_2543_, 1);
v___x_2627_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_a_2542_, v_a_2500_);
if (lean_obj_tag(v___x_2627_) == 0)
{
lean_object* v_a_2628_; uint8_t v___x_2629_; 
v_a_2628_ = lean_ctor_get(v___x_2627_, 0);
lean_inc(v_a_2628_);
lean_dec_ref_known(v___x_2627_, 1);
v___x_2629_ = lean_unbox(v_a_2628_);
lean_dec(v_a_2628_);
if (v___x_2629_ == 0)
{
goto v___jp_2545_;
}
else
{
lean_object* v___x_2630_; 
v___x_2630_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_a_2544_, v_a_2500_);
if (lean_obj_tag(v___x_2630_) == 0)
{
lean_object* v_a_2631_; uint8_t v___x_2632_; 
v_a_2631_ = lean_ctor_get(v___x_2630_, 0);
lean_inc(v_a_2631_);
lean_dec_ref_known(v___x_2630_, 1);
v___x_2632_ = lean_unbox(v_a_2631_);
lean_dec(v_a_2631_);
if (v___x_2632_ == 0)
{
goto v___jp_2545_;
}
else
{
lean_object* v___x_2633_; 
v___x_2633_ = l_Lean_Meta_Grind_isEqv___redArg(v_a_2542_, v_a_2544_, v_a_2500_);
lean_dec(v_a_2544_);
lean_dec(v_a_2542_);
if (lean_obj_tag(v___x_2633_) == 0)
{
lean_object* v_a_2634_; lean_object* v___x_2636_; uint8_t v_isShared_2637_; uint8_t v_isSharedCheck_2645_; 
v_a_2634_ = lean_ctor_get(v___x_2633_, 0);
v_isSharedCheck_2645_ = !lean_is_exclusive(v___x_2633_);
if (v_isSharedCheck_2645_ == 0)
{
v___x_2636_ = v___x_2633_;
v_isShared_2637_ = v_isSharedCheck_2645_;
goto v_resetjp_2635_;
}
else
{
lean_inc(v_a_2634_);
lean_dec(v___x_2633_);
v___x_2636_ = lean_box(0);
v_isShared_2637_ = v_isSharedCheck_2645_;
goto v_resetjp_2635_;
}
v_resetjp_2635_:
{
uint8_t v___x_2638_; 
v___x_2638_ = lean_unbox(v_a_2634_);
lean_dec(v_a_2634_);
if (v___x_2638_ == 0)
{
lean_object* v___x_2639_; lean_object* v___x_2640_; 
lean_del_object(v___x_2636_);
v___x_2639_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2639_, 0, v_u_2496_);
lean_ctor_set(v___x_2639_, 1, v_v_2497_);
v___x_2640_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate(v___x_2639_, v_a_2499_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_, v_a_2504_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_);
return v___x_2640_;
}
else
{
lean_object* v___x_2641_; lean_object* v___x_2643_; 
lean_dec(v_v_2497_);
lean_dec(v_u_2496_);
v___x_2641_ = lean_box(0);
if (v_isShared_2637_ == 0)
{
lean_ctor_set(v___x_2636_, 0, v___x_2641_);
v___x_2643_ = v___x_2636_;
goto v_reusejp_2642_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v___x_2641_);
v___x_2643_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2642_;
}
v_reusejp_2642_:
{
return v___x_2643_;
}
}
}
}
else
{
lean_object* v_a_2646_; lean_object* v___x_2648_; uint8_t v_isShared_2649_; uint8_t v_isSharedCheck_2653_; 
lean_dec(v_v_2497_);
lean_dec(v_u_2496_);
v_a_2646_ = lean_ctor_get(v___x_2633_, 0);
v_isSharedCheck_2653_ = !lean_is_exclusive(v___x_2633_);
if (v_isSharedCheck_2653_ == 0)
{
v___x_2648_ = v___x_2633_;
v_isShared_2649_ = v_isSharedCheck_2653_;
goto v_resetjp_2647_;
}
else
{
lean_inc(v_a_2646_);
lean_dec(v___x_2633_);
v___x_2648_ = lean_box(0);
v_isShared_2649_ = v_isSharedCheck_2653_;
goto v_resetjp_2647_;
}
v_resetjp_2647_:
{
lean_object* v___x_2651_; 
if (v_isShared_2649_ == 0)
{
v___x_2651_ = v___x_2648_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v_a_2646_);
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
lean_object* v_a_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2661_; 
lean_dec(v_a_2544_);
lean_dec(v_a_2542_);
lean_dec(v_v_2497_);
lean_dec(v_u_2496_);
v_a_2654_ = lean_ctor_get(v___x_2630_, 0);
v_isSharedCheck_2661_ = !lean_is_exclusive(v___x_2630_);
if (v_isSharedCheck_2661_ == 0)
{
v___x_2656_ = v___x_2630_;
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
else
{
lean_inc(v_a_2654_);
lean_dec(v___x_2630_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v___x_2659_; 
if (v_isShared_2657_ == 0)
{
v___x_2659_ = v___x_2656_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v_a_2654_);
v___x_2659_ = v_reuseFailAlloc_2660_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
return v___x_2659_;
}
}
}
}
}
else
{
lean_object* v_a_2662_; lean_object* v___x_2664_; uint8_t v_isShared_2665_; uint8_t v_isSharedCheck_2669_; 
lean_dec(v_a_2544_);
lean_dec(v_a_2542_);
lean_dec(v_v_2497_);
lean_dec(v_u_2496_);
v_a_2662_ = lean_ctor_get(v___x_2627_, 0);
v_isSharedCheck_2669_ = !lean_is_exclusive(v___x_2627_);
if (v_isSharedCheck_2669_ == 0)
{
v___x_2664_ = v___x_2627_;
v_isShared_2665_ = v_isSharedCheck_2669_;
goto v_resetjp_2663_;
}
else
{
lean_inc(v_a_2662_);
lean_dec(v___x_2627_);
v___x_2664_ = lean_box(0);
v_isShared_2665_ = v_isSharedCheck_2669_;
goto v_resetjp_2663_;
}
v_resetjp_2663_:
{
lean_object* v___x_2667_; 
if (v_isShared_2665_ == 0)
{
v___x_2667_ = v___x_2664_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2668_; 
v_reuseFailAlloc_2668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2668_, 0, v_a_2662_);
v___x_2667_ = v_reuseFailAlloc_2668_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
return v___x_2667_;
}
}
}
v___jp_2545_:
{
lean_object* v___x_2546_; 
v___x_2546_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___redArg(v_a_2542_, v_a_2500_, v_a_2508_);
lean_dec(v_a_2542_);
if (lean_obj_tag(v___x_2546_) == 0)
{
lean_object* v_a_2547_; lean_object* v___x_2549_; uint8_t v_isShared_2550_; uint8_t v_isSharedCheck_2618_; 
v_a_2547_ = lean_ctor_get(v___x_2546_, 0);
v_isSharedCheck_2618_ = !lean_is_exclusive(v___x_2546_);
if (v_isSharedCheck_2618_ == 0)
{
v___x_2549_ = v___x_2546_;
v_isShared_2550_ = v_isSharedCheck_2618_;
goto v_resetjp_2548_;
}
else
{
lean_inc(v_a_2547_);
lean_dec(v___x_2546_);
v___x_2549_ = lean_box(0);
v_isShared_2550_ = v_isSharedCheck_2618_;
goto v_resetjp_2548_;
}
v_resetjp_2548_:
{
if (lean_obj_tag(v_a_2547_) == 1)
{
lean_object* v_val_2551_; lean_object* v___x_2552_; 
lean_del_object(v___x_2549_);
v_val_2551_ = lean_ctor_get(v_a_2547_, 0);
lean_inc(v_val_2551_);
lean_dec_ref_known(v_a_2547_, 1);
v___x_2552_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___redArg(v_a_2544_, v_a_2500_, v_a_2508_);
lean_dec(v_a_2544_);
if (lean_obj_tag(v___x_2552_) == 0)
{
lean_object* v_a_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2605_; 
v_a_2553_ = lean_ctor_get(v___x_2552_, 0);
v_isSharedCheck_2605_ = !lean_is_exclusive(v___x_2552_);
if (v_isSharedCheck_2605_ == 0)
{
v___x_2555_ = v___x_2552_;
v_isShared_2556_ = v_isSharedCheck_2605_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_a_2553_);
lean_dec(v___x_2552_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2605_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
if (lean_obj_tag(v_a_2553_) == 1)
{
lean_object* v_val_2557_; lean_object* v___x_2558_; 
lean_del_object(v___x_2555_);
v_val_2557_ = lean_ctor_get(v_a_2553_, 0);
lean_inc(v_val_2557_);
lean_dec_ref_known(v_a_2553_, 1);
v___x_2558_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_val_2551_, v_a_2500_);
if (lean_obj_tag(v___x_2558_) == 0)
{
lean_object* v_a_2559_; uint8_t v___x_2560_; 
v_a_2559_ = lean_ctor_get(v___x_2558_, 0);
lean_inc(v_a_2559_);
lean_dec_ref_known(v___x_2558_, 1);
v___x_2560_ = lean_unbox(v_a_2559_);
lean_dec(v_a_2559_);
if (v___x_2560_ == 0)
{
lean_dec(v_val_2557_);
lean_dec(v_val_2551_);
lean_dec(v_v_2497_);
lean_dec(v_u_2496_);
goto v___jp_2511_;
}
else
{
lean_object* v___x_2561_; 
v___x_2561_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_val_2557_, v_a_2500_);
if (lean_obj_tag(v___x_2561_) == 0)
{
lean_object* v_a_2562_; uint8_t v___x_2563_; 
v_a_2562_ = lean_ctor_get(v___x_2561_, 0);
lean_inc(v_a_2562_);
lean_dec_ref_known(v___x_2561_, 1);
v___x_2563_ = lean_unbox(v_a_2562_);
lean_dec(v_a_2562_);
if (v___x_2563_ == 0)
{
lean_dec(v_val_2557_);
lean_dec(v_val_2551_);
lean_dec(v_v_2497_);
lean_dec(v_u_2496_);
goto v___jp_2511_;
}
else
{
lean_object* v___x_2564_; 
v___x_2564_ = l_Lean_Meta_Grind_isEqv___redArg(v_val_2551_, v_val_2557_, v_a_2500_);
lean_dec(v_val_2557_);
lean_dec(v_val_2551_);
if (lean_obj_tag(v___x_2564_) == 0)
{
lean_object* v_a_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2576_; 
v_a_2565_ = lean_ctor_get(v___x_2564_, 0);
v_isSharedCheck_2576_ = !lean_is_exclusive(v___x_2564_);
if (v_isSharedCheck_2576_ == 0)
{
v___x_2567_ = v___x_2564_;
v_isShared_2568_ = v_isSharedCheck_2576_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_a_2565_);
lean_dec(v___x_2564_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2576_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
uint8_t v___x_2569_; 
v___x_2569_ = lean_unbox(v_a_2565_);
lean_dec(v_a_2565_);
if (v___x_2569_ == 0)
{
lean_object* v___x_2570_; lean_object* v___x_2571_; 
lean_del_object(v___x_2567_);
v___x_2570_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2570_, 0, v_u_2496_);
lean_ctor_set(v___x_2570_, 1, v_v_2497_);
v___x_2571_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate(v___x_2570_, v_a_2499_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_, v_a_2504_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_);
return v___x_2571_;
}
else
{
lean_object* v___x_2572_; lean_object* v___x_2574_; 
lean_dec(v_v_2497_);
lean_dec(v_u_2496_);
v___x_2572_ = lean_box(0);
if (v_isShared_2568_ == 0)
{
lean_ctor_set(v___x_2567_, 0, v___x_2572_);
v___x_2574_ = v___x_2567_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v___x_2572_);
v___x_2574_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
return v___x_2574_;
}
}
}
}
else
{
lean_object* v_a_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2584_; 
lean_dec(v_v_2497_);
lean_dec(v_u_2496_);
v_a_2577_ = lean_ctor_get(v___x_2564_, 0);
v_isSharedCheck_2584_ = !lean_is_exclusive(v___x_2564_);
if (v_isSharedCheck_2584_ == 0)
{
v___x_2579_ = v___x_2564_;
v_isShared_2580_ = v_isSharedCheck_2584_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_a_2577_);
lean_dec(v___x_2564_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2584_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
lean_object* v___x_2582_; 
if (v_isShared_2580_ == 0)
{
v___x_2582_ = v___x_2579_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v_a_2577_);
v___x_2582_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
return v___x_2582_;
}
}
}
}
}
else
{
lean_object* v_a_2585_; lean_object* v___x_2587_; uint8_t v_isShared_2588_; uint8_t v_isSharedCheck_2592_; 
lean_dec(v_val_2557_);
lean_dec(v_val_2551_);
lean_dec(v_v_2497_);
lean_dec(v_u_2496_);
v_a_2585_ = lean_ctor_get(v___x_2561_, 0);
v_isSharedCheck_2592_ = !lean_is_exclusive(v___x_2561_);
if (v_isSharedCheck_2592_ == 0)
{
v___x_2587_ = v___x_2561_;
v_isShared_2588_ = v_isSharedCheck_2592_;
goto v_resetjp_2586_;
}
else
{
lean_inc(v_a_2585_);
lean_dec(v___x_2561_);
v___x_2587_ = lean_box(0);
v_isShared_2588_ = v_isSharedCheck_2592_;
goto v_resetjp_2586_;
}
v_resetjp_2586_:
{
lean_object* v___x_2590_; 
if (v_isShared_2588_ == 0)
{
v___x_2590_ = v___x_2587_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v_a_2585_);
v___x_2590_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2589_;
}
v_reusejp_2589_:
{
return v___x_2590_;
}
}
}
}
}
else
{
lean_object* v_a_2593_; lean_object* v___x_2595_; uint8_t v_isShared_2596_; uint8_t v_isSharedCheck_2600_; 
lean_dec(v_val_2557_);
lean_dec(v_val_2551_);
lean_dec(v_v_2497_);
lean_dec(v_u_2496_);
v_a_2593_ = lean_ctor_get(v___x_2558_, 0);
v_isSharedCheck_2600_ = !lean_is_exclusive(v___x_2558_);
if (v_isSharedCheck_2600_ == 0)
{
v___x_2595_ = v___x_2558_;
v_isShared_2596_ = v_isSharedCheck_2600_;
goto v_resetjp_2594_;
}
else
{
lean_inc(v_a_2593_);
lean_dec(v___x_2558_);
v___x_2595_ = lean_box(0);
v_isShared_2596_ = v_isSharedCheck_2600_;
goto v_resetjp_2594_;
}
v_resetjp_2594_:
{
lean_object* v___x_2598_; 
if (v_isShared_2596_ == 0)
{
v___x_2598_ = v___x_2595_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v_a_2593_);
v___x_2598_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
return v___x_2598_;
}
}
}
}
else
{
lean_object* v___x_2601_; lean_object* v___x_2603_; 
lean_dec(v_a_2553_);
lean_dec(v_val_2551_);
lean_dec(v_v_2497_);
lean_dec(v_u_2496_);
v___x_2601_ = lean_box(0);
if (v_isShared_2556_ == 0)
{
lean_ctor_set(v___x_2555_, 0, v___x_2601_);
v___x_2603_ = v___x_2555_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v___x_2601_);
v___x_2603_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
return v___x_2603_;
}
}
}
}
else
{
lean_object* v_a_2606_; lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2613_; 
lean_dec(v_val_2551_);
lean_dec(v_v_2497_);
lean_dec(v_u_2496_);
v_a_2606_ = lean_ctor_get(v___x_2552_, 0);
v_isSharedCheck_2613_ = !lean_is_exclusive(v___x_2552_);
if (v_isSharedCheck_2613_ == 0)
{
v___x_2608_ = v___x_2552_;
v_isShared_2609_ = v_isSharedCheck_2613_;
goto v_resetjp_2607_;
}
else
{
lean_inc(v_a_2606_);
lean_dec(v___x_2552_);
v___x_2608_ = lean_box(0);
v_isShared_2609_ = v_isSharedCheck_2613_;
goto v_resetjp_2607_;
}
v_resetjp_2607_:
{
lean_object* v___x_2611_; 
if (v_isShared_2609_ == 0)
{
v___x_2611_ = v___x_2608_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v_a_2606_);
v___x_2611_ = v_reuseFailAlloc_2612_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
return v___x_2611_;
}
}
}
}
else
{
lean_object* v___x_2614_; lean_object* v___x_2616_; 
lean_dec(v_a_2547_);
lean_dec(v_a_2544_);
lean_dec(v_v_2497_);
lean_dec(v_u_2496_);
v___x_2614_ = lean_box(0);
if (v_isShared_2550_ == 0)
{
lean_ctor_set(v___x_2549_, 0, v___x_2614_);
v___x_2616_ = v___x_2549_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v___x_2614_);
v___x_2616_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
return v___x_2616_;
}
}
}
}
else
{
lean_object* v_a_2619_; lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2626_; 
lean_dec(v_a_2544_);
lean_dec(v_v_2497_);
lean_dec(v_u_2496_);
v_a_2619_ = lean_ctor_get(v___x_2546_, 0);
v_isSharedCheck_2626_ = !lean_is_exclusive(v___x_2546_);
if (v_isSharedCheck_2626_ == 0)
{
v___x_2621_ = v___x_2546_;
v_isShared_2622_ = v_isSharedCheck_2626_;
goto v_resetjp_2620_;
}
else
{
lean_inc(v_a_2619_);
lean_dec(v___x_2546_);
v___x_2621_ = lean_box(0);
v_isShared_2622_ = v_isSharedCheck_2626_;
goto v_resetjp_2620_;
}
v_resetjp_2620_:
{
lean_object* v___x_2624_; 
if (v_isShared_2622_ == 0)
{
v___x_2624_ = v___x_2621_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v_a_2619_);
v___x_2624_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
return v___x_2624_;
}
}
}
}
}
else
{
lean_object* v_a_2670_; lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2677_; 
lean_dec(v_a_2542_);
lean_dec(v_v_2497_);
lean_dec(v_u_2496_);
v_a_2670_ = lean_ctor_get(v___x_2543_, 0);
v_isSharedCheck_2677_ = !lean_is_exclusive(v___x_2543_);
if (v_isSharedCheck_2677_ == 0)
{
v___x_2672_ = v___x_2543_;
v_isShared_2673_ = v_isSharedCheck_2677_;
goto v_resetjp_2671_;
}
else
{
lean_inc(v_a_2670_);
lean_dec(v___x_2543_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2677_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
lean_object* v___x_2675_; 
if (v_isShared_2673_ == 0)
{
v___x_2675_ = v___x_2672_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v_a_2670_);
v___x_2675_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
return v___x_2675_;
}
}
}
}
else
{
lean_object* v_a_2678_; lean_object* v___x_2680_; uint8_t v_isShared_2681_; uint8_t v_isSharedCheck_2685_; 
lean_dec(v_v_2497_);
lean_dec(v_u_2496_);
v_a_2678_ = lean_ctor_get(v___x_2541_, 0);
v_isSharedCheck_2685_ = !lean_is_exclusive(v___x_2541_);
if (v_isSharedCheck_2685_ == 0)
{
v___x_2680_ = v___x_2541_;
v_isShared_2681_ = v_isSharedCheck_2685_;
goto v_resetjp_2679_;
}
else
{
lean_inc(v_a_2678_);
lean_dec(v___x_2541_);
v___x_2680_ = lean_box(0);
v_isShared_2681_ = v_isSharedCheck_2685_;
goto v_resetjp_2679_;
}
v_resetjp_2679_:
{
lean_object* v___x_2683_; 
if (v_isShared_2681_ == 0)
{
v___x_2683_ = v___x_2680_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v_a_2678_);
v___x_2683_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
return v___x_2683_;
}
}
}
}
}
else
{
lean_object* v___x_2686_; lean_object* v___x_2688_; 
lean_dec(v_a_2531_);
lean_dec(v_v_2497_);
lean_dec(v_u_2496_);
v___x_2686_ = lean_box(0);
if (v_isShared_2534_ == 0)
{
lean_ctor_set(v___x_2533_, 0, v___x_2686_);
v___x_2688_ = v___x_2533_;
goto v_reusejp_2687_;
}
else
{
lean_object* v_reuseFailAlloc_2689_; 
v_reuseFailAlloc_2689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2689_, 0, v___x_2686_);
v___x_2688_ = v_reuseFailAlloc_2689_;
goto v_reusejp_2687_;
}
v_reusejp_2687_:
{
return v___x_2688_;
}
}
}
}
else
{
lean_object* v_a_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2698_; 
lean_dec(v_v_2497_);
lean_dec(v_u_2496_);
v_a_2691_ = lean_ctor_get(v___x_2530_, 0);
v_isSharedCheck_2698_ = !lean_is_exclusive(v___x_2530_);
if (v_isSharedCheck_2698_ == 0)
{
v___x_2693_ = v___x_2530_;
v_isShared_2694_ = v_isSharedCheck_2698_;
goto v_resetjp_2692_;
}
else
{
lean_inc(v_a_2691_);
lean_dec(v___x_2530_);
v___x_2693_ = lean_box(0);
v_isShared_2694_ = v_isSharedCheck_2698_;
goto v_resetjp_2692_;
}
v_resetjp_2692_:
{
lean_object* v___x_2696_; 
if (v_isShared_2694_ == 0)
{
v___x_2696_ = v___x_2693_;
goto v_reusejp_2695_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v_a_2691_);
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
}
}
}
else
{
lean_object* v_a_2700_; lean_object* v___x_2702_; uint8_t v_isShared_2703_; uint8_t v_isSharedCheck_2707_; 
lean_dec(v_v_2497_);
lean_dec(v_u_2496_);
v_a_2700_ = lean_ctor_get(v___x_2515_, 0);
v_isSharedCheck_2707_ = !lean_is_exclusive(v___x_2515_);
if (v_isSharedCheck_2707_ == 0)
{
v___x_2702_ = v___x_2515_;
v_isShared_2703_ = v_isSharedCheck_2707_;
goto v_resetjp_2701_;
}
else
{
lean_inc(v_a_2700_);
lean_dec(v___x_2515_);
v___x_2702_ = lean_box(0);
v_isShared_2703_ = v_isSharedCheck_2707_;
goto v_resetjp_2701_;
}
v_resetjp_2701_:
{
lean_object* v___x_2705_; 
if (v_isShared_2703_ == 0)
{
v___x_2705_ = v___x_2702_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v_a_2700_);
v___x_2705_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2704_;
}
v_reusejp_2704_:
{
return v___x_2705_;
}
}
}
}
else
{
lean_object* v___x_2708_; lean_object* v___x_2709_; 
lean_dec(v_v_2497_);
lean_dec(v_u_2496_);
v___x_2708_ = lean_box(0);
v___x_2709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2709_, 0, v___x_2708_);
return v___x_2709_;
}
v___jp_2511_:
{
lean_object* v___x_2512_; lean_object* v___x_2513_; 
v___x_2512_ = lean_box(0);
v___x_2513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2513_, 0, v___x_2512_);
return v___x_2513_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq___boxed(lean_object* v_u_2710_, lean_object* v_v_2711_, lean_object* v_k_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_){
_start:
{
lean_object* v_res_2725_; 
v_res_2725_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq(v_u_2710_, v_v_2711_, v_k_2712_, v_a_2713_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_, v_a_2720_, v_a_2721_, v_a_2722_, v_a_2723_);
lean_dec(v_a_2723_);
lean_dec_ref(v_a_2722_);
lean_dec(v_a_2721_);
lean_dec_ref(v_a_2720_);
lean_dec(v_a_2719_);
lean_dec_ref(v_a_2718_);
lean_dec(v_a_2717_);
lean_dec_ref(v_a_2716_);
lean_dec(v_a_2715_);
lean_dec(v_a_2714_);
lean_dec(v_a_2713_);
lean_dec_ref(v_k_2712_);
return v_res_2725_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_2726_, lean_object* v_vals_2727_, lean_object* v_i_2728_, lean_object* v_k_2729_){
_start:
{
lean_object* v___x_2734_; uint8_t v___x_2735_; 
v___x_2734_ = lean_array_get_size(v_keys_2726_);
v___x_2735_ = lean_nat_dec_lt(v_i_2728_, v___x_2734_);
if (v___x_2735_ == 0)
{
lean_object* v___x_2736_; 
lean_dec(v_i_2728_);
v___x_2736_ = lean_box(0);
return v___x_2736_;
}
else
{
lean_object* v_fst_2737_; lean_object* v_snd_2738_; lean_object* v_k_x27_2739_; lean_object* v_fst_2740_; lean_object* v_snd_2741_; uint8_t v___x_2742_; 
v_fst_2737_ = lean_ctor_get(v_k_2729_, 0);
v_snd_2738_ = lean_ctor_get(v_k_2729_, 1);
v_k_x27_2739_ = lean_array_fget_borrowed(v_keys_2726_, v_i_2728_);
v_fst_2740_ = lean_ctor_get(v_k_x27_2739_, 0);
v_snd_2741_ = lean_ctor_get(v_k_x27_2739_, 1);
v___x_2742_ = lean_nat_dec_eq(v_fst_2737_, v_fst_2740_);
if (v___x_2742_ == 0)
{
goto v___jp_2730_;
}
else
{
uint8_t v___x_2743_; 
v___x_2743_ = lean_nat_dec_eq(v_snd_2738_, v_snd_2741_);
if (v___x_2743_ == 0)
{
goto v___jp_2730_;
}
else
{
lean_object* v___x_2744_; lean_object* v___x_2745_; 
v___x_2744_ = lean_array_fget_borrowed(v_vals_2727_, v_i_2728_);
lean_dec(v_i_2728_);
lean_inc(v___x_2744_);
v___x_2745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2745_, 0, v___x_2744_);
return v___x_2745_;
}
}
}
v___jp_2730_:
{
lean_object* v___x_2731_; lean_object* v___x_2732_; 
v___x_2731_ = lean_unsigned_to_nat(1u);
v___x_2732_ = lean_nat_add(v_i_2728_, v___x_2731_);
lean_dec(v_i_2728_);
v_i_2728_ = v___x_2732_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_2746_, lean_object* v_vals_2747_, lean_object* v_i_2748_, lean_object* v_k_2749_){
_start:
{
lean_object* v_res_2750_; 
v_res_2750_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1___redArg(v_keys_2746_, v_vals_2747_, v_i_2748_, v_k_2749_);
lean_dec_ref(v_k_2749_);
lean_dec_ref(v_vals_2747_);
lean_dec_ref(v_keys_2746_);
return v_res_2750_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0___redArg(lean_object* v_x_2751_, size_t v_x_2752_, lean_object* v_x_2753_){
_start:
{
if (lean_obj_tag(v_x_2751_) == 0)
{
lean_object* v_es_2754_; lean_object* v___x_2755_; size_t v___x_2756_; size_t v___x_2757_; lean_object* v_j_2758_; lean_object* v___x_2759_; 
v_es_2754_ = lean_ctor_get(v_x_2751_, 0);
v___x_2755_ = lean_box(2);
v___x_2756_ = ((size_t)31ULL);
v___x_2757_ = lean_usize_land(v_x_2752_, v___x_2756_);
v_j_2758_ = lean_usize_to_nat(v___x_2757_);
v___x_2759_ = lean_array_get_borrowed(v___x_2755_, v_es_2754_, v_j_2758_);
lean_dec(v_j_2758_);
switch(lean_obj_tag(v___x_2759_))
{
case 0:
{
lean_object* v_key_2760_; lean_object* v_val_2761_; lean_object* v_fst_2762_; lean_object* v_snd_2763_; lean_object* v_fst_2764_; lean_object* v_snd_2765_; uint8_t v___x_2766_; 
v_key_2760_ = lean_ctor_get(v___x_2759_, 0);
v_val_2761_ = lean_ctor_get(v___x_2759_, 1);
v_fst_2762_ = lean_ctor_get(v_x_2753_, 0);
v_snd_2763_ = lean_ctor_get(v_x_2753_, 1);
v_fst_2764_ = lean_ctor_get(v_key_2760_, 0);
v_snd_2765_ = lean_ctor_get(v_key_2760_, 1);
v___x_2766_ = lean_nat_dec_eq(v_fst_2762_, v_fst_2764_);
if (v___x_2766_ == 0)
{
lean_object* v___x_2767_; 
v___x_2767_ = lean_box(0);
return v___x_2767_;
}
else
{
uint8_t v___x_2768_; 
v___x_2768_ = lean_nat_dec_eq(v_snd_2763_, v_snd_2765_);
if (v___x_2768_ == 0)
{
lean_object* v___x_2769_; 
v___x_2769_ = lean_box(0);
return v___x_2769_;
}
else
{
lean_object* v___x_2770_; 
lean_inc(v_val_2761_);
v___x_2770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2770_, 0, v_val_2761_);
return v___x_2770_;
}
}
}
case 1:
{
lean_object* v_node_2771_; size_t v___x_2772_; size_t v___x_2773_; 
v_node_2771_ = lean_ctor_get(v___x_2759_, 0);
v___x_2772_ = ((size_t)5ULL);
v___x_2773_ = lean_usize_shift_right(v_x_2752_, v___x_2772_);
v_x_2751_ = v_node_2771_;
v_x_2752_ = v___x_2773_;
goto _start;
}
default: 
{
lean_object* v___x_2775_; 
v___x_2775_ = lean_box(0);
return v___x_2775_;
}
}
}
else
{
lean_object* v_ks_2776_; lean_object* v_vs_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; 
v_ks_2776_ = lean_ctor_get(v_x_2751_, 0);
v_vs_2777_ = lean_ctor_get(v_x_2751_, 1);
v___x_2778_ = lean_unsigned_to_nat(0u);
v___x_2779_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1___redArg(v_ks_2776_, v_vs_2777_, v___x_2778_, v_x_2753_);
return v___x_2779_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0___redArg___boxed(lean_object* v_x_2780_, lean_object* v_x_2781_, lean_object* v_x_2782_){
_start:
{
size_t v_x_3989__boxed_2783_; lean_object* v_res_2784_; 
v_x_3989__boxed_2783_ = lean_unbox_usize(v_x_2781_);
lean_dec(v_x_2781_);
v_res_2784_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0___redArg(v_x_2780_, v_x_3989__boxed_2783_, v_x_2782_);
lean_dec_ref(v_x_2782_);
lean_dec_ref(v_x_2780_);
return v_res_2784_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0___redArg(lean_object* v_x_2785_, lean_object* v_x_2786_){
_start:
{
lean_object* v_fst_2787_; lean_object* v_snd_2788_; uint64_t v___x_2789_; uint64_t v___x_2790_; uint64_t v___x_2791_; size_t v___x_2792_; lean_object* v___x_2793_; 
v_fst_2787_ = lean_ctor_get(v_x_2786_, 0);
v_snd_2788_ = lean_ctor_get(v_x_2786_, 1);
v___x_2789_ = lean_uint64_of_nat(v_fst_2787_);
v___x_2790_ = lean_uint64_of_nat(v_snd_2788_);
v___x_2791_ = lean_uint64_mix_hash(v___x_2789_, v___x_2790_);
v___x_2792_ = lean_uint64_to_usize(v___x_2791_);
v___x_2793_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0___redArg(v_x_2785_, v___x_2792_, v_x_2786_);
return v___x_2793_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0___redArg___boxed(lean_object* v_x_2794_, lean_object* v_x_2795_){
_start:
{
lean_object* v_res_2796_; 
v_res_2796_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0___redArg(v_x_2794_, v_x_2795_);
lean_dec_ref(v_x_2795_);
lean_dec_ref(v_x_2794_);
return v_res_2796_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__1(lean_object* v_u_2797_, lean_object* v_v_2798_, lean_object* v_k_2799_, lean_object* v_as_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_){
_start:
{
if (lean_obj_tag(v_as_2800_) == 0)
{
lean_object* v___x_2813_; lean_object* v___x_2814_; 
lean_dec_ref(v_k_2799_);
lean_dec(v_v_2798_);
lean_dec(v_u_2797_);
v___x_2813_ = lean_box(0);
v___x_2814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2814_, 0, v___x_2813_);
return v___x_2814_;
}
else
{
lean_object* v_head_2815_; lean_object* v_tail_2816_; lean_object* v_fst_2817_; lean_object* v_snd_2818_; lean_object* v___x_2819_; 
v_head_2815_ = lean_ctor_get(v_as_2800_, 0);
lean_inc(v_head_2815_);
v_tail_2816_ = lean_ctor_get(v_as_2800_, 1);
lean_inc(v_tail_2816_);
lean_dec_ref_known(v_as_2800_, 2);
v_fst_2817_ = lean_ctor_get(v_head_2815_, 0);
lean_inc(v_fst_2817_);
v_snd_2818_ = lean_ctor_get(v_head_2815_, 1);
lean_inc(v_snd_2818_);
lean_dec(v_head_2815_);
lean_inc_ref(v_k_2799_);
lean_inc(v_v_2798_);
lean_inc(v_u_2797_);
v___x_2819_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse(v_u_2797_, v_v_2798_, v_k_2799_, v_fst_2817_, v_snd_2818_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_);
if (lean_obj_tag(v___x_2819_) == 0)
{
lean_dec_ref_known(v___x_2819_, 1);
v_as_2800_ = v_tail_2816_;
goto _start;
}
else
{
lean_dec(v_tail_2816_);
lean_dec_ref(v_k_2799_);
lean_dec(v_v_2798_);
lean_dec(v_u_2797_);
return v___x_2819_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__1___boxed(lean_object* v_u_2821_, lean_object* v_v_2822_, lean_object* v_k_2823_, lean_object* v_as_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_){
_start:
{
lean_object* v_res_2837_; 
v_res_2837_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__1(v_u_2821_, v_v_2822_, v_k_2823_, v_as_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_);
lean_dec(v___y_2835_);
lean_dec_ref(v___y_2834_);
lean_dec(v___y_2833_);
lean_dec_ref(v___y_2832_);
lean_dec(v___y_2831_);
lean_dec_ref(v___y_2830_);
lean_dec(v___y_2829_);
lean_dec_ref(v___y_2828_);
lean_dec(v___y_2827_);
lean_dec(v___y_2826_);
lean_dec(v___y_2825_);
return v_res_2837_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__2(lean_object* v_u_2838_, lean_object* v_v_2839_, lean_object* v_k_2840_, lean_object* v_as_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_){
_start:
{
if (lean_obj_tag(v_as_2841_) == 0)
{
lean_object* v___x_2854_; lean_object* v___x_2855_; 
lean_dec_ref(v_k_2840_);
lean_dec(v_v_2839_);
lean_dec(v_u_2838_);
v___x_2854_ = lean_box(0);
v___x_2855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2855_, 0, v___x_2854_);
return v___x_2855_;
}
else
{
lean_object* v_head_2856_; lean_object* v_tail_2857_; lean_object* v_fst_2858_; lean_object* v_snd_2859_; lean_object* v___x_2860_; 
v_head_2856_ = lean_ctor_get(v_as_2841_, 0);
lean_inc(v_head_2856_);
v_tail_2857_ = lean_ctor_get(v_as_2841_, 1);
lean_inc(v_tail_2857_);
lean_dec_ref_known(v_as_2841_, 2);
v_fst_2858_ = lean_ctor_get(v_head_2856_, 0);
lean_inc(v_fst_2858_);
v_snd_2859_ = lean_ctor_get(v_head_2856_, 1);
lean_inc(v_snd_2859_);
lean_dec(v_head_2856_);
lean_inc_ref(v_k_2840_);
lean_inc(v_v_2839_);
lean_inc(v_u_2838_);
v___x_2860_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue(v_u_2838_, v_v_2839_, v_k_2840_, v_fst_2858_, v_snd_2859_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_);
if (lean_obj_tag(v___x_2860_) == 0)
{
lean_dec_ref_known(v___x_2860_, 1);
v_as_2841_ = v_tail_2857_;
goto _start;
}
else
{
lean_dec(v_tail_2857_);
lean_dec_ref(v_k_2840_);
lean_dec(v_v_2839_);
lean_dec(v_u_2838_);
return v___x_2860_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__2___boxed(lean_object* v_u_2862_, lean_object* v_v_2863_, lean_object* v_k_2864_, lean_object* v_as_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_){
_start:
{
lean_object* v_res_2878_; 
v_res_2878_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__2(v_u_2862_, v_v_2863_, v_k_2864_, v_as_2865_, v___y_2866_, v___y_2867_, v___y_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_);
lean_dec(v___y_2876_);
lean_dec_ref(v___y_2875_);
lean_dec(v___y_2874_);
lean_dec_ref(v___y_2873_);
lean_dec(v___y_2872_);
lean_dec_ref(v___y_2871_);
lean_dec(v___y_2870_);
lean_dec_ref(v___y_2869_);
lean_dec(v___y_2868_);
lean_dec(v___y_2867_);
lean_dec(v___y_2866_);
return v_res_2878_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate(lean_object* v_u_2879_, lean_object* v_v_2880_, lean_object* v_k_2881_, lean_object* v_a_2882_, lean_object* v_a_2883_, lean_object* v_a_2884_, lean_object* v_a_2885_, lean_object* v_a_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_){
_start:
{
lean_object* v___x_2912_; 
v___x_2912_ = l_Lean_Meta_Grind_Order_getStruct___redArg(v_a_2882_, v_a_2883_, v_a_2891_);
if (lean_obj_tag(v___x_2912_) == 0)
{
lean_object* v_a_2913_; lean_object* v_cnstrsOf_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; 
v_a_2913_ = lean_ctor_get(v___x_2912_, 0);
lean_inc(v_a_2913_);
lean_dec_ref_known(v___x_2912_, 1);
v_cnstrsOf_2914_ = lean_ctor_get(v_a_2913_, 4);
lean_inc_ref(v_cnstrsOf_2914_);
lean_dec(v_a_2913_);
lean_inc(v_v_2880_);
lean_inc(v_u_2879_);
v___x_2915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2915_, 0, v_u_2879_);
lean_ctor_set(v___x_2915_, 1, v_v_2880_);
v___x_2916_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0___redArg(v_cnstrsOf_2914_, v___x_2915_);
lean_dec_ref_known(v___x_2915_, 2);
lean_dec_ref(v_cnstrsOf_2914_);
if (lean_obj_tag(v___x_2916_) == 1)
{
lean_object* v_val_2917_; lean_object* v___x_2918_; 
v_val_2917_ = lean_ctor_get(v___x_2916_, 0);
lean_inc(v_val_2917_);
lean_dec_ref_known(v___x_2916_, 1);
lean_inc_ref(v_k_2881_);
lean_inc(v_v_2880_);
lean_inc(v_u_2879_);
v___x_2918_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__2(v_u_2879_, v_v_2880_, v_k_2881_, v_val_2917_, v_a_2882_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_);
if (lean_obj_tag(v___x_2918_) == 0)
{
lean_dec_ref_known(v___x_2918_, 1);
goto v___jp_2894_;
}
else
{
lean_dec_ref(v_k_2881_);
lean_dec(v_v_2880_);
lean_dec(v_u_2879_);
return v___x_2918_;
}
}
else
{
lean_dec(v___x_2916_);
goto v___jp_2894_;
}
}
else
{
lean_object* v_a_2919_; lean_object* v___x_2921_; uint8_t v_isShared_2922_; uint8_t v_isSharedCheck_2926_; 
lean_dec_ref(v_k_2881_);
lean_dec(v_v_2880_);
lean_dec(v_u_2879_);
v_a_2919_ = lean_ctor_get(v___x_2912_, 0);
v_isSharedCheck_2926_ = !lean_is_exclusive(v___x_2912_);
if (v_isSharedCheck_2926_ == 0)
{
v___x_2921_ = v___x_2912_;
v_isShared_2922_ = v_isSharedCheck_2926_;
goto v_resetjp_2920_;
}
else
{
lean_inc(v_a_2919_);
lean_dec(v___x_2912_);
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
v___jp_2894_:
{
lean_object* v___x_2895_; 
v___x_2895_ = l_Lean_Meta_Grind_Order_getStruct___redArg(v_a_2882_, v_a_2883_, v_a_2891_);
if (lean_obj_tag(v___x_2895_) == 0)
{
lean_object* v_a_2896_; lean_object* v_cnstrsOf_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; 
v_a_2896_ = lean_ctor_get(v___x_2895_, 0);
lean_inc(v_a_2896_);
lean_dec_ref_known(v___x_2895_, 1);
v_cnstrsOf_2897_ = lean_ctor_get(v_a_2896_, 4);
lean_inc_ref(v_cnstrsOf_2897_);
lean_dec(v_a_2896_);
lean_inc(v_u_2879_);
lean_inc(v_v_2880_);
v___x_2898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2898_, 0, v_v_2880_);
lean_ctor_set(v___x_2898_, 1, v_u_2879_);
v___x_2899_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0___redArg(v_cnstrsOf_2897_, v___x_2898_);
lean_dec_ref_known(v___x_2898_, 2);
lean_dec_ref(v_cnstrsOf_2897_);
if (lean_obj_tag(v___x_2899_) == 1)
{
lean_object* v_val_2900_; lean_object* v___x_2901_; 
v_val_2900_ = lean_ctor_get(v___x_2899_, 0);
lean_inc(v_val_2900_);
lean_dec_ref_known(v___x_2899_, 1);
lean_inc_ref(v_k_2881_);
lean_inc(v_v_2880_);
lean_inc(v_u_2879_);
v___x_2901_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__1(v_u_2879_, v_v_2880_, v_k_2881_, v_val_2900_, v_a_2882_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_);
if (lean_obj_tag(v___x_2901_) == 0)
{
lean_object* v___x_2902_; 
lean_dec_ref_known(v___x_2901_, 1);
v___x_2902_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq(v_u_2879_, v_v_2880_, v_k_2881_, v_a_2882_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_);
lean_dec_ref(v_k_2881_);
return v___x_2902_;
}
else
{
lean_dec_ref(v_k_2881_);
lean_dec(v_v_2880_);
lean_dec(v_u_2879_);
return v___x_2901_;
}
}
else
{
lean_object* v___x_2903_; 
lean_dec(v___x_2899_);
v___x_2903_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq(v_u_2879_, v_v_2880_, v_k_2881_, v_a_2882_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_);
lean_dec_ref(v_k_2881_);
return v___x_2903_;
}
}
else
{
lean_object* v_a_2904_; lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2911_; 
lean_dec_ref(v_k_2881_);
lean_dec(v_v_2880_);
lean_dec(v_u_2879_);
v_a_2904_ = lean_ctor_get(v___x_2895_, 0);
v_isSharedCheck_2911_ = !lean_is_exclusive(v___x_2895_);
if (v_isSharedCheck_2911_ == 0)
{
v___x_2906_ = v___x_2895_;
v_isShared_2907_ = v_isSharedCheck_2911_;
goto v_resetjp_2905_;
}
else
{
lean_inc(v_a_2904_);
lean_dec(v___x_2895_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate___boxed(lean_object* v_u_2927_, lean_object* v_v_2928_, lean_object* v_k_2929_, lean_object* v_a_2930_, lean_object* v_a_2931_, lean_object* v_a_2932_, lean_object* v_a_2933_, lean_object* v_a_2934_, lean_object* v_a_2935_, lean_object* v_a_2936_, lean_object* v_a_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_){
_start:
{
lean_object* v_res_2942_; 
v_res_2942_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate(v_u_2927_, v_v_2928_, v_k_2929_, v_a_2930_, v_a_2931_, v_a_2932_, v_a_2933_, v_a_2934_, v_a_2935_, v_a_2936_, v_a_2937_, v_a_2938_, v_a_2939_, v_a_2940_);
lean_dec(v_a_2940_);
lean_dec_ref(v_a_2939_);
lean_dec(v_a_2938_);
lean_dec_ref(v_a_2937_);
lean_dec(v_a_2936_);
lean_dec_ref(v_a_2935_);
lean_dec(v_a_2934_);
lean_dec_ref(v_a_2933_);
lean_dec(v_a_2932_);
lean_dec(v_a_2931_);
lean_dec(v_a_2930_);
return v_res_2942_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0(lean_object* v_00_u03b2_2943_, lean_object* v_x_2944_, lean_object* v_x_2945_){
_start:
{
lean_object* v___x_2946_; 
v___x_2946_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0___redArg(v_x_2944_, v_x_2945_);
return v___x_2946_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0___boxed(lean_object* v_00_u03b2_2947_, lean_object* v_x_2948_, lean_object* v_x_2949_){
_start:
{
lean_object* v_res_2950_; 
v_res_2950_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0(v_00_u03b2_2947_, v_x_2948_, v_x_2949_);
lean_dec_ref(v_x_2949_);
lean_dec_ref(v_x_2948_);
return v_res_2950_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0(lean_object* v_00_u03b2_2951_, lean_object* v_x_2952_, size_t v_x_2953_, lean_object* v_x_2954_){
_start:
{
lean_object* v___x_2955_; 
v___x_2955_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0___redArg(v_x_2952_, v_x_2953_, v_x_2954_);
return v___x_2955_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2956_, lean_object* v_x_2957_, lean_object* v_x_2958_, lean_object* v_x_2959_){
_start:
{
size_t v_x_4253__boxed_2960_; lean_object* v_res_2961_; 
v_x_4253__boxed_2960_ = lean_unbox_usize(v_x_2958_);
lean_dec(v_x_2958_);
v_res_2961_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0(v_00_u03b2_2956_, v_x_2957_, v_x_4253__boxed_2960_, v_x_2959_);
lean_dec_ref(v_x_2959_);
lean_dec_ref(v_x_2957_);
return v_res_2961_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2962_, lean_object* v_keys_2963_, lean_object* v_vals_2964_, lean_object* v_heq_2965_, lean_object* v_i_2966_, lean_object* v_k_2967_){
_start:
{
lean_object* v___x_2968_; 
v___x_2968_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1___redArg(v_keys_2963_, v_vals_2964_, v_i_2966_, v_k_2967_);
return v___x_2968_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2969_, lean_object* v_keys_2970_, lean_object* v_vals_2971_, lean_object* v_heq_2972_, lean_object* v_i_2973_, lean_object* v_k_2974_){
_start:
{
lean_object* v_res_2975_; 
v_res_2975_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1(v_00_u03b2_2969_, v_keys_2970_, v_vals_2971_, v_heq_2972_, v_i_2973_, v_k_2974_);
lean_dec_ref(v_k_2974_);
lean_dec_ref(v_vals_2971_);
lean_dec_ref(v_keys_2970_);
return v_res_2975_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_updateIfShorter(lean_object* v_u_2976_, lean_object* v_v_2977_, lean_object* v_k_2978_, lean_object* v_w_2979_, lean_object* v_a_2980_, lean_object* v_a_2981_, lean_object* v_a_2982_, lean_object* v_a_2983_, lean_object* v_a_2984_, lean_object* v_a_2985_, lean_object* v_a_2986_, lean_object* v_a_2987_, lean_object* v_a_2988_, lean_object* v_a_2989_, lean_object* v_a_2990_){
_start:
{
lean_object* v___x_2992_; 
v___x_2992_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isShorter___redArg(v_u_2976_, v_v_2977_, v_k_2978_, v_a_2980_, v_a_2981_, v_a_2989_);
if (lean_obj_tag(v___x_2992_) == 0)
{
lean_object* v_a_2993_; lean_object* v___x_2995_; uint8_t v_isShared_2996_; uint8_t v_isSharedCheck_3015_; 
v_a_2993_ = lean_ctor_get(v___x_2992_, 0);
v_isSharedCheck_3015_ = !lean_is_exclusive(v___x_2992_);
if (v_isSharedCheck_3015_ == 0)
{
v___x_2995_ = v___x_2992_;
v_isShared_2996_ = v_isSharedCheck_3015_;
goto v_resetjp_2994_;
}
else
{
lean_inc(v_a_2993_);
lean_dec(v___x_2992_);
v___x_2995_ = lean_box(0);
v_isShared_2996_ = v_isSharedCheck_3015_;
goto v_resetjp_2994_;
}
v_resetjp_2994_:
{
uint8_t v___x_2997_; 
v___x_2997_ = lean_unbox(v_a_2993_);
lean_dec(v_a_2993_);
if (v___x_2997_ == 0)
{
lean_object* v___x_2998_; lean_object* v___x_3000_; 
lean_dec_ref(v_k_2978_);
lean_dec(v_v_2977_);
lean_dec(v_u_2976_);
v___x_2998_ = lean_box(0);
if (v_isShared_2996_ == 0)
{
lean_ctor_set(v___x_2995_, 0, v___x_2998_);
v___x_3000_ = v___x_2995_;
goto v_reusejp_2999_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v___x_2998_);
v___x_3000_ = v_reuseFailAlloc_3001_;
goto v_reusejp_2999_;
}
v_reusejp_2999_:
{
return v___x_3000_;
}
}
else
{
lean_object* v___x_3002_; 
lean_del_object(v___x_2995_);
lean_inc_ref(v_k_2978_);
lean_inc(v_v_2977_);
lean_inc(v_u_2976_);
v___x_3002_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist___redArg(v_u_2976_, v_v_2977_, v_k_2978_, v_a_2980_, v_a_2981_);
if (lean_obj_tag(v___x_3002_) == 0)
{
lean_object* v___x_3003_; 
lean_dec_ref_known(v___x_3002_, 1);
v___x_3003_ = l_Lean_Meta_Grind_Order_getProof___redArg(v_w_2979_, v_v_2977_, v_a_2980_, v_a_2981_, v_a_2987_, v_a_2988_, v_a_2989_, v_a_2990_);
if (lean_obj_tag(v___x_3003_) == 0)
{
lean_object* v_a_3004_; lean_object* v___x_3005_; 
v_a_3004_ = lean_ctor_get(v___x_3003_, 0);
lean_inc(v_a_3004_);
lean_dec_ref_known(v___x_3003_, 1);
lean_inc(v_v_2977_);
lean_inc(v_u_2976_);
v___x_3005_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___redArg(v_u_2976_, v_v_2977_, v_a_3004_, v_a_2980_, v_a_2981_);
if (lean_obj_tag(v___x_3005_) == 0)
{
lean_object* v___x_3006_; 
lean_dec_ref_known(v___x_3005_, 1);
v___x_3006_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate(v_u_2976_, v_v_2977_, v_k_2978_, v_a_2980_, v_a_2981_, v_a_2982_, v_a_2983_, v_a_2984_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_, v_a_2989_, v_a_2990_);
return v___x_3006_;
}
else
{
lean_dec_ref(v_k_2978_);
lean_dec(v_v_2977_);
lean_dec(v_u_2976_);
return v___x_3005_;
}
}
else
{
lean_object* v_a_3007_; lean_object* v___x_3009_; uint8_t v_isShared_3010_; uint8_t v_isSharedCheck_3014_; 
lean_dec_ref(v_k_2978_);
lean_dec(v_v_2977_);
lean_dec(v_u_2976_);
v_a_3007_ = lean_ctor_get(v___x_3003_, 0);
v_isSharedCheck_3014_ = !lean_is_exclusive(v___x_3003_);
if (v_isSharedCheck_3014_ == 0)
{
v___x_3009_ = v___x_3003_;
v_isShared_3010_ = v_isSharedCheck_3014_;
goto v_resetjp_3008_;
}
else
{
lean_inc(v_a_3007_);
lean_dec(v___x_3003_);
v___x_3009_ = lean_box(0);
v_isShared_3010_ = v_isSharedCheck_3014_;
goto v_resetjp_3008_;
}
v_resetjp_3008_:
{
lean_object* v___x_3012_; 
if (v_isShared_3010_ == 0)
{
v___x_3012_ = v___x_3009_;
goto v_reusejp_3011_;
}
else
{
lean_object* v_reuseFailAlloc_3013_; 
v_reuseFailAlloc_3013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3013_, 0, v_a_3007_);
v___x_3012_ = v_reuseFailAlloc_3013_;
goto v_reusejp_3011_;
}
v_reusejp_3011_:
{
return v___x_3012_;
}
}
}
}
else
{
lean_dec_ref(v_k_2978_);
lean_dec(v_v_2977_);
lean_dec(v_u_2976_);
return v___x_3002_;
}
}
}
}
else
{
lean_object* v_a_3016_; lean_object* v___x_3018_; uint8_t v_isShared_3019_; uint8_t v_isSharedCheck_3023_; 
lean_dec_ref(v_k_2978_);
lean_dec(v_v_2977_);
lean_dec(v_u_2976_);
v_a_3016_ = lean_ctor_get(v___x_2992_, 0);
v_isSharedCheck_3023_ = !lean_is_exclusive(v___x_2992_);
if (v_isSharedCheck_3023_ == 0)
{
v___x_3018_ = v___x_2992_;
v_isShared_3019_ = v_isSharedCheck_3023_;
goto v_resetjp_3017_;
}
else
{
lean_inc(v_a_3016_);
lean_dec(v___x_2992_);
v___x_3018_ = lean_box(0);
v_isShared_3019_ = v_isSharedCheck_3023_;
goto v_resetjp_3017_;
}
v_resetjp_3017_:
{
lean_object* v___x_3021_; 
if (v_isShared_3019_ == 0)
{
v___x_3021_ = v___x_3018_;
goto v_reusejp_3020_;
}
else
{
lean_object* v_reuseFailAlloc_3022_; 
v_reuseFailAlloc_3022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3022_, 0, v_a_3016_);
v___x_3021_ = v_reuseFailAlloc_3022_;
goto v_reusejp_3020_;
}
v_reusejp_3020_:
{
return v___x_3021_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_updateIfShorter___boxed(lean_object* v_u_3024_, lean_object* v_v_3025_, lean_object* v_k_3026_, lean_object* v_w_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_, lean_object* v_a_3038_, lean_object* v_a_3039_){
_start:
{
lean_object* v_res_3040_; 
v_res_3040_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_updateIfShorter(v_u_3024_, v_v_3025_, v_k_3026_, v_w_3027_, v_a_3028_, v_a_3029_, v_a_3030_, v_a_3031_, v_a_3032_, v_a_3033_, v_a_3034_, v_a_3035_, v_a_3036_, v_a_3037_, v_a_3038_);
lean_dec(v_a_3038_);
lean_dec_ref(v_a_3037_);
lean_dec(v_a_3036_);
lean_dec_ref(v_a_3035_);
lean_dec(v_a_3034_);
lean_dec_ref(v_a_3033_);
lean_dec(v_a_3032_);
lean_dec_ref(v_a_3031_);
lean_dec(v_a_3030_);
lean_dec(v_a_3029_);
lean_dec(v_a_3028_);
lean_dec(v_w_3027_);
return v_res_3040_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update___lam__0(lean_object* v_xs_3041_, lean_object* v_i_3042_){
_start:
{
lean_object* v_size_3043_; uint8_t v___x_3044_; 
v_size_3043_ = lean_ctor_get(v_xs_3041_, 2);
v___x_3044_ = lean_nat_dec_lt(v_i_3042_, v_size_3043_);
return v___x_3044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update___lam__0___boxed(lean_object* v_xs_3045_, lean_object* v_i_3046_){
_start:
{
uint8_t v_res_3047_; lean_object* v_r_3048_; 
v_res_3047_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update___lam__0(v_xs_3045_, v_i_3046_);
lean_dec(v_i_3046_);
lean_dec_ref(v_xs_3045_);
v_r_3048_ = lean_box(v_res_3047_);
return v_r_3048_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__2(lean_object* v___x_3049_, lean_object* v_fst_3050_, lean_object* v_v_3051_, lean_object* v_as_3052_, size_t v_sz_3053_, size_t v_i_3054_, lean_object* v_b_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_){
_start:
{
uint8_t v___x_3068_; 
v___x_3068_ = lean_usize_dec_lt(v_i_3054_, v_sz_3053_);
if (v___x_3068_ == 0)
{
lean_object* v___x_3069_; 
lean_dec(v_fst_3050_);
v___x_3069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3069_, 0, v_b_3055_);
return v___x_3069_;
}
else
{
lean_object* v_a_3070_; lean_object* v_fst_3071_; lean_object* v_snd_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; 
v_a_3070_ = lean_array_uget_borrowed(v_as_3052_, v_i_3054_);
v_fst_3071_ = lean_ctor_get(v_a_3070_, 0);
v_snd_3072_ = lean_ctor_get(v_a_3070_, 1);
v___x_3073_ = lean_box(0);
lean_inc(v_snd_3072_);
v___x_3074_ = l_Lean_Meta_Grind_Order_Weight_add(v___x_3049_, v_snd_3072_);
lean_inc(v_fst_3071_);
lean_inc(v_fst_3050_);
v___x_3075_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_updateIfShorter(v_fst_3050_, v_fst_3071_, v___x_3074_, v_v_3051_, v___y_3056_, v___y_3057_, v___y_3058_, v___y_3059_, v___y_3060_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_);
if (lean_obj_tag(v___x_3075_) == 0)
{
size_t v___x_3076_; size_t v___x_3077_; 
lean_dec_ref_known(v___x_3075_, 1);
v___x_3076_ = ((size_t)1ULL);
v___x_3077_ = lean_usize_add(v_i_3054_, v___x_3076_);
v_i_3054_ = v___x_3077_;
v_b_3055_ = v___x_3073_;
goto _start;
}
else
{
lean_dec(v_fst_3050_);
return v___x_3075_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__2___boxed(lean_object** _args){
lean_object* v___x_3079_ = _args[0];
lean_object* v_fst_3080_ = _args[1];
lean_object* v_v_3081_ = _args[2];
lean_object* v_as_3082_ = _args[3];
lean_object* v_sz_3083_ = _args[4];
lean_object* v_i_3084_ = _args[5];
lean_object* v_b_3085_ = _args[6];
lean_object* v___y_3086_ = _args[7];
lean_object* v___y_3087_ = _args[8];
lean_object* v___y_3088_ = _args[9];
lean_object* v___y_3089_ = _args[10];
lean_object* v___y_3090_ = _args[11];
lean_object* v___y_3091_ = _args[12];
lean_object* v___y_3092_ = _args[13];
lean_object* v___y_3093_ = _args[14];
lean_object* v___y_3094_ = _args[15];
lean_object* v___y_3095_ = _args[16];
lean_object* v___y_3096_ = _args[17];
lean_object* v___y_3097_ = _args[18];
_start:
{
size_t v_sz_boxed_3098_; size_t v_i_boxed_3099_; lean_object* v_res_3100_; 
v_sz_boxed_3098_ = lean_unbox_usize(v_sz_3083_);
lean_dec(v_sz_3083_);
v_i_boxed_3099_ = lean_unbox_usize(v_i_3084_);
lean_dec(v_i_3084_);
v_res_3100_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__2(v___x_3079_, v_fst_3080_, v_v_3081_, v_as_3082_, v_sz_boxed_3098_, v_i_boxed_3099_, v_b_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_);
lean_dec(v___y_3096_);
lean_dec_ref(v___y_3095_);
lean_dec(v___y_3094_);
lean_dec_ref(v___y_3093_);
lean_dec(v___y_3092_);
lean_dec_ref(v___y_3091_);
lean_dec(v___y_3090_);
lean_dec_ref(v___y_3089_);
lean_dec(v___y_3088_);
lean_dec(v___y_3087_);
lean_dec(v___y_3086_);
lean_dec_ref(v_as_3082_);
lean_dec(v_v_3081_);
lean_dec_ref(v___x_3079_);
return v_res_3100_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__3(lean_object* v_k_3101_, lean_object* v_v_3102_, lean_object* v_u_3103_, lean_object* v_a_3104_, lean_object* v_as_3105_, size_t v_sz_3106_, size_t v_i_3107_, lean_object* v_b_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_){
_start:
{
uint8_t v___x_3121_; 
v___x_3121_ = lean_usize_dec_lt(v_i_3107_, v_sz_3106_);
if (v___x_3121_ == 0)
{
lean_object* v___x_3122_; 
lean_dec(v_v_3102_);
lean_dec_ref(v_k_3101_);
v___x_3122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3122_, 0, v_b_3108_);
return v___x_3122_;
}
else
{
lean_object* v_a_3123_; lean_object* v_fst_3124_; lean_object* v_snd_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; 
v_a_3123_ = lean_array_uget_borrowed(v_as_3105_, v_i_3107_);
v_fst_3124_ = lean_ctor_get(v_a_3123_, 0);
v_snd_3125_ = lean_ctor_get(v_a_3123_, 1);
v___x_3126_ = lean_box(0);
lean_inc_ref(v_k_3101_);
v___x_3127_ = l_Lean_Meta_Grind_Order_Weight_add(v_snd_3125_, v_k_3101_);
lean_inc_ref(v___x_3127_);
lean_inc(v_v_3102_);
lean_inc(v_fst_3124_);
v___x_3128_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_updateIfShorter(v_fst_3124_, v_v_3102_, v___x_3127_, v_u_3103_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_);
if (lean_obj_tag(v___x_3128_) == 0)
{
size_t v_sz_3129_; size_t v___x_3130_; lean_object* v___x_3131_; 
lean_dec_ref_known(v___x_3128_, 1);
v_sz_3129_ = lean_array_size(v_a_3104_);
v___x_3130_ = ((size_t)0ULL);
lean_inc(v_fst_3124_);
v___x_3131_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__2(v___x_3127_, v_fst_3124_, v_v_3102_, v_a_3104_, v_sz_3129_, v___x_3130_, v___x_3126_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_);
lean_dec_ref(v___x_3127_);
if (lean_obj_tag(v___x_3131_) == 0)
{
size_t v___x_3132_; size_t v___x_3133_; 
lean_dec_ref_known(v___x_3131_, 1);
v___x_3132_ = ((size_t)1ULL);
v___x_3133_ = lean_usize_add(v_i_3107_, v___x_3132_);
v_i_3107_ = v___x_3133_;
v_b_3108_ = v___x_3126_;
goto _start;
}
else
{
lean_dec(v_v_3102_);
lean_dec_ref(v_k_3101_);
return v___x_3131_;
}
}
else
{
lean_dec_ref(v___x_3127_);
lean_dec(v_v_3102_);
lean_dec_ref(v_k_3101_);
return v___x_3128_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__3___boxed(lean_object** _args){
lean_object* v_k_3135_ = _args[0];
lean_object* v_v_3136_ = _args[1];
lean_object* v_u_3137_ = _args[2];
lean_object* v_a_3138_ = _args[3];
lean_object* v_as_3139_ = _args[4];
lean_object* v_sz_3140_ = _args[5];
lean_object* v_i_3141_ = _args[6];
lean_object* v_b_3142_ = _args[7];
lean_object* v___y_3143_ = _args[8];
lean_object* v___y_3144_ = _args[9];
lean_object* v___y_3145_ = _args[10];
lean_object* v___y_3146_ = _args[11];
lean_object* v___y_3147_ = _args[12];
lean_object* v___y_3148_ = _args[13];
lean_object* v___y_3149_ = _args[14];
lean_object* v___y_3150_ = _args[15];
lean_object* v___y_3151_ = _args[16];
lean_object* v___y_3152_ = _args[17];
lean_object* v___y_3153_ = _args[18];
lean_object* v___y_3154_ = _args[19];
_start:
{
size_t v_sz_boxed_3155_; size_t v_i_boxed_3156_; lean_object* v_res_3157_; 
v_sz_boxed_3155_ = lean_unbox_usize(v_sz_3140_);
lean_dec(v_sz_3140_);
v_i_boxed_3156_ = lean_unbox_usize(v_i_3141_);
lean_dec(v_i_3141_);
v_res_3157_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__3(v_k_3135_, v_v_3136_, v_u_3137_, v_a_3138_, v_as_3139_, v_sz_boxed_3155_, v_i_boxed_3156_, v_b_3142_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_);
lean_dec(v___y_3153_);
lean_dec_ref(v___y_3152_);
lean_dec(v___y_3151_);
lean_dec_ref(v___y_3150_);
lean_dec(v___y_3149_);
lean_dec_ref(v___y_3148_);
lean_dec(v___y_3147_);
lean_dec_ref(v___y_3146_);
lean_dec(v___y_3145_);
lean_dec(v___y_3144_);
lean_dec(v___y_3143_);
lean_dec_ref(v_as_3139_);
lean_dec_ref(v_a_3138_);
lean_dec(v_u_3137_);
return v_res_3157_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0___redArg(lean_object* v_k_3158_, lean_object* v_u_3159_, lean_object* v_x_3160_, lean_object* v_x_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_){
_start:
{
if (lean_obj_tag(v_x_3161_) == 0)
{
lean_object* v___x_3166_; 
v___x_3166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3166_, 0, v_x_3160_);
return v___x_3166_;
}
else
{
lean_object* v_key_3167_; lean_object* v_value_3168_; lean_object* v_tail_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; 
v_key_3167_ = lean_ctor_get(v_x_3161_, 0);
lean_inc_n(v_key_3167_, 2);
v_value_3168_ = lean_ctor_get(v_x_3161_, 1);
lean_inc_n(v_value_3168_, 2);
v_tail_3169_ = lean_ctor_get(v_x_3161_, 2);
lean_inc(v_tail_3169_);
lean_dec_ref_known(v_x_3161_, 3);
v___x_3170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3170_, 0, v_key_3167_);
lean_ctor_set(v___x_3170_, 1, v_value_3168_);
v___x_3171_ = l_Lean_Meta_Grind_Order_Weight_add(v_k_3158_, v_value_3168_);
v___x_3172_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isShorter___redArg(v_u_3159_, v_key_3167_, v___x_3171_, v___y_3162_, v___y_3163_, v___y_3164_);
lean_dec_ref(v___x_3171_);
lean_dec(v_key_3167_);
if (lean_obj_tag(v___x_3172_) == 0)
{
lean_object* v_a_3173_; uint8_t v___x_3174_; 
v_a_3173_ = lean_ctor_get(v___x_3172_, 0);
lean_inc(v_a_3173_);
lean_dec_ref_known(v___x_3172_, 1);
v___x_3174_ = lean_unbox(v_a_3173_);
lean_dec(v_a_3173_);
if (v___x_3174_ == 0)
{
lean_dec_ref_known(v___x_3170_, 2);
v_x_3161_ = v_tail_3169_;
goto _start;
}
else
{
lean_object* v___x_3176_; 
v___x_3176_ = lean_array_push(v_x_3160_, v___x_3170_);
v_x_3160_ = v___x_3176_;
v_x_3161_ = v_tail_3169_;
goto _start;
}
}
else
{
lean_object* v_a_3178_; lean_object* v___x_3180_; uint8_t v_isShared_3181_; uint8_t v_isSharedCheck_3185_; 
lean_dec_ref_known(v___x_3170_, 2);
lean_dec(v_tail_3169_);
lean_dec_ref(v_x_3160_);
v_a_3178_ = lean_ctor_get(v___x_3172_, 0);
v_isSharedCheck_3185_ = !lean_is_exclusive(v___x_3172_);
if (v_isSharedCheck_3185_ == 0)
{
v___x_3180_ = v___x_3172_;
v_isShared_3181_ = v_isSharedCheck_3185_;
goto v_resetjp_3179_;
}
else
{
lean_inc(v_a_3178_);
lean_dec(v___x_3172_);
v___x_3180_ = lean_box(0);
v_isShared_3181_ = v_isSharedCheck_3185_;
goto v_resetjp_3179_;
}
v_resetjp_3179_:
{
lean_object* v___x_3183_; 
if (v_isShared_3181_ == 0)
{
v___x_3183_ = v___x_3180_;
goto v_reusejp_3182_;
}
else
{
lean_object* v_reuseFailAlloc_3184_; 
v_reuseFailAlloc_3184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3184_, 0, v_a_3178_);
v___x_3183_ = v_reuseFailAlloc_3184_;
goto v_reusejp_3182_;
}
v_reusejp_3182_:
{
return v___x_3183_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0___redArg___boxed(lean_object* v_k_3186_, lean_object* v_u_3187_, lean_object* v_x_3188_, lean_object* v_x_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_){
_start:
{
lean_object* v_res_3194_; 
v_res_3194_ = l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0___redArg(v_k_3186_, v_u_3187_, v_x_3188_, v_x_3189_, v___y_3190_, v___y_3191_, v___y_3192_);
lean_dec_ref(v___y_3192_);
lean_dec(v___y_3191_);
lean_dec(v___y_3190_);
lean_dec(v_u_3187_);
lean_dec_ref(v_k_3186_);
return v_res_3194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__1___redArg(lean_object* v_k_3195_, lean_object* v_v_3196_, lean_object* v_x_3197_, lean_object* v_x_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_){
_start:
{
if (lean_obj_tag(v_x_3198_) == 0)
{
lean_object* v___x_3203_; 
lean_dec_ref(v_k_3195_);
v___x_3203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3203_, 0, v_x_3197_);
return v___x_3203_;
}
else
{
lean_object* v_key_3204_; lean_object* v_value_3205_; lean_object* v_tail_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; 
v_key_3204_ = lean_ctor_get(v_x_3198_, 0);
v_value_3205_ = lean_ctor_get(v_x_3198_, 1);
v_tail_3206_ = lean_ctor_get(v_x_3198_, 2);
lean_inc(v_value_3205_);
lean_inc(v_key_3204_);
v___x_3207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3207_, 0, v_key_3204_);
lean_ctor_set(v___x_3207_, 1, v_value_3205_);
lean_inc_ref(v_k_3195_);
v___x_3208_ = l_Lean_Meta_Grind_Order_Weight_add(v_value_3205_, v_k_3195_);
v___x_3209_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isShorter___redArg(v_key_3204_, v_v_3196_, v___x_3208_, v___y_3199_, v___y_3200_, v___y_3201_);
lean_dec_ref(v___x_3208_);
if (lean_obj_tag(v___x_3209_) == 0)
{
lean_object* v_a_3210_; uint8_t v___x_3211_; 
v_a_3210_ = lean_ctor_get(v___x_3209_, 0);
lean_inc(v_a_3210_);
lean_dec_ref_known(v___x_3209_, 1);
v___x_3211_ = lean_unbox(v_a_3210_);
lean_dec(v_a_3210_);
if (v___x_3211_ == 0)
{
lean_dec_ref_known(v___x_3207_, 2);
v_x_3198_ = v_tail_3206_;
goto _start;
}
else
{
lean_object* v___x_3213_; 
v___x_3213_ = lean_array_push(v_x_3197_, v___x_3207_);
v_x_3197_ = v___x_3213_;
v_x_3198_ = v_tail_3206_;
goto _start;
}
}
else
{
lean_object* v_a_3215_; lean_object* v___x_3217_; uint8_t v_isShared_3218_; uint8_t v_isSharedCheck_3222_; 
lean_dec_ref_known(v___x_3207_, 2);
lean_dec_ref(v_x_3197_);
lean_dec_ref(v_k_3195_);
v_a_3215_ = lean_ctor_get(v___x_3209_, 0);
v_isSharedCheck_3222_ = !lean_is_exclusive(v___x_3209_);
if (v_isSharedCheck_3222_ == 0)
{
v___x_3217_ = v___x_3209_;
v_isShared_3218_ = v_isSharedCheck_3222_;
goto v_resetjp_3216_;
}
else
{
lean_inc(v_a_3215_);
lean_dec(v___x_3209_);
v___x_3217_ = lean_box(0);
v_isShared_3218_ = v_isSharedCheck_3222_;
goto v_resetjp_3216_;
}
v_resetjp_3216_:
{
lean_object* v___x_3220_; 
if (v_isShared_3218_ == 0)
{
v___x_3220_ = v___x_3217_;
goto v_reusejp_3219_;
}
else
{
lean_object* v_reuseFailAlloc_3221_; 
v_reuseFailAlloc_3221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3221_, 0, v_a_3215_);
v___x_3220_ = v_reuseFailAlloc_3221_;
goto v_reusejp_3219_;
}
v_reusejp_3219_:
{
return v___x_3220_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__1___redArg___boxed(lean_object* v_k_3223_, lean_object* v_v_3224_, lean_object* v_x_3225_, lean_object* v_x_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_){
_start:
{
lean_object* v_res_3231_; 
v_res_3231_ = l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__1___redArg(v_k_3223_, v_v_3224_, v_x_3225_, v_x_3226_, v___y_3227_, v___y_3228_, v___y_3229_);
lean_dec_ref(v___y_3229_);
lean_dec(v___y_3228_);
lean_dec(v___y_3227_);
lean_dec(v_x_3226_);
lean_dec(v_v_3224_);
return v_res_3231_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update(lean_object* v_u_3234_, lean_object* v_v_3235_, lean_object* v_k_3236_, lean_object* v_a_3237_, lean_object* v_a_3238_, lean_object* v_a_3239_, lean_object* v_a_3240_, lean_object* v_a_3241_, lean_object* v_a_3242_, lean_object* v_a_3243_, lean_object* v_a_3244_, lean_object* v_a_3245_, lean_object* v_a_3246_, lean_object* v_a_3247_){
_start:
{
lean_object* v___x_3249_; lean_object* v_ts_3250_; lean_object* v___y_3252_; lean_object* v___y_3253_; lean_object* v___x_3278_; 
v___x_3249_ = lean_box(0);
v_ts_3250_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update___closed__0));
v___x_3278_ = l_Lean_Meta_Grind_Order_getStruct___redArg(v_a_3237_, v_a_3238_, v_a_3246_);
if (lean_obj_tag(v___x_3278_) == 0)
{
lean_object* v_a_3279_; lean_object* v___y_3281_; lean_object* v_targets_3306_; uint8_t v___x_3307_; 
v_a_3279_ = lean_ctor_get(v___x_3278_, 0);
lean_inc(v_a_3279_);
lean_dec_ref_known(v___x_3278_, 1);
v_targets_3306_ = lean_ctor_get(v_a_3279_, 6);
lean_inc_ref(v_targets_3306_);
lean_dec(v_a_3279_);
v___x_3307_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update___lam__0(v_targets_3306_, v_v_3235_);
if (v___x_3307_ == 0)
{
lean_object* v___x_3308_; 
lean_dec_ref(v_targets_3306_);
v___x_3308_ = l_outOfBounds___redArg(v___x_3249_);
v___y_3281_ = v___x_3308_;
goto v___jp_3280_;
}
else
{
lean_object* v___x_3309_; 
v___x_3309_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3249_, v_targets_3306_, v_v_3235_);
lean_dec_ref(v_targets_3306_);
v___y_3281_ = v___x_3309_;
goto v___jp_3280_;
}
v___jp_3280_:
{
lean_object* v___x_3282_; 
v___x_3282_ = l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0___redArg(v_k_3236_, v_u_3234_, v_ts_3250_, v___y_3281_, v_a_3237_, v_a_3238_, v_a_3246_);
if (lean_obj_tag(v___x_3282_) == 0)
{
lean_object* v_a_3283_; lean_object* v___x_3284_; 
v_a_3283_ = lean_ctor_get(v___x_3282_, 0);
lean_inc(v_a_3283_);
lean_dec_ref_known(v___x_3282_, 1);
v___x_3284_ = l_Lean_Meta_Grind_Order_getStruct___redArg(v_a_3237_, v_a_3238_, v_a_3246_);
if (lean_obj_tag(v___x_3284_) == 0)
{
lean_object* v_a_3285_; lean_object* v_sources_3286_; uint8_t v___x_3287_; 
v_a_3285_ = lean_ctor_get(v___x_3284_, 0);
lean_inc(v_a_3285_);
lean_dec_ref_known(v___x_3284_, 1);
v_sources_3286_ = lean_ctor_get(v_a_3285_, 5);
lean_inc_ref(v_sources_3286_);
lean_dec(v_a_3285_);
v___x_3287_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update___lam__0(v_sources_3286_, v_u_3234_);
if (v___x_3287_ == 0)
{
lean_object* v___x_3288_; 
lean_dec_ref(v_sources_3286_);
v___x_3288_ = l_outOfBounds___redArg(v___x_3249_);
v___y_3252_ = v_a_3283_;
v___y_3253_ = v___x_3288_;
goto v___jp_3251_;
}
else
{
lean_object* v___x_3289_; 
v___x_3289_ = l_Lean_PersistentArray_get_x21___redArg(v___x_3249_, v_sources_3286_, v_u_3234_);
lean_dec_ref(v_sources_3286_);
v___y_3252_ = v_a_3283_;
v___y_3253_ = v___x_3289_;
goto v___jp_3251_;
}
}
else
{
lean_object* v_a_3290_; lean_object* v___x_3292_; uint8_t v_isShared_3293_; uint8_t v_isSharedCheck_3297_; 
lean_dec(v_a_3283_);
lean_dec_ref(v_k_3236_);
lean_dec(v_v_3235_);
lean_dec(v_u_3234_);
v_a_3290_ = lean_ctor_get(v___x_3284_, 0);
v_isSharedCheck_3297_ = !lean_is_exclusive(v___x_3284_);
if (v_isSharedCheck_3297_ == 0)
{
v___x_3292_ = v___x_3284_;
v_isShared_3293_ = v_isSharedCheck_3297_;
goto v_resetjp_3291_;
}
else
{
lean_inc(v_a_3290_);
lean_dec(v___x_3284_);
v___x_3292_ = lean_box(0);
v_isShared_3293_ = v_isSharedCheck_3297_;
goto v_resetjp_3291_;
}
v_resetjp_3291_:
{
lean_object* v___x_3295_; 
if (v_isShared_3293_ == 0)
{
v___x_3295_ = v___x_3292_;
goto v_reusejp_3294_;
}
else
{
lean_object* v_reuseFailAlloc_3296_; 
v_reuseFailAlloc_3296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3296_, 0, v_a_3290_);
v___x_3295_ = v_reuseFailAlloc_3296_;
goto v_reusejp_3294_;
}
v_reusejp_3294_:
{
return v___x_3295_;
}
}
}
}
else
{
lean_object* v_a_3298_; lean_object* v___x_3300_; uint8_t v_isShared_3301_; uint8_t v_isSharedCheck_3305_; 
lean_dec_ref(v_k_3236_);
lean_dec(v_v_3235_);
lean_dec(v_u_3234_);
v_a_3298_ = lean_ctor_get(v___x_3282_, 0);
v_isSharedCheck_3305_ = !lean_is_exclusive(v___x_3282_);
if (v_isSharedCheck_3305_ == 0)
{
v___x_3300_ = v___x_3282_;
v_isShared_3301_ = v_isSharedCheck_3305_;
goto v_resetjp_3299_;
}
else
{
lean_inc(v_a_3298_);
lean_dec(v___x_3282_);
v___x_3300_ = lean_box(0);
v_isShared_3301_ = v_isSharedCheck_3305_;
goto v_resetjp_3299_;
}
v_resetjp_3299_:
{
lean_object* v___x_3303_; 
if (v_isShared_3301_ == 0)
{
v___x_3303_ = v___x_3300_;
goto v_reusejp_3302_;
}
else
{
lean_object* v_reuseFailAlloc_3304_; 
v_reuseFailAlloc_3304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3304_, 0, v_a_3298_);
v___x_3303_ = v_reuseFailAlloc_3304_;
goto v_reusejp_3302_;
}
v_reusejp_3302_:
{
return v___x_3303_;
}
}
}
}
}
else
{
lean_object* v_a_3310_; lean_object* v___x_3312_; uint8_t v_isShared_3313_; uint8_t v_isSharedCheck_3317_; 
lean_dec_ref(v_k_3236_);
lean_dec(v_v_3235_);
lean_dec(v_u_3234_);
v_a_3310_ = lean_ctor_get(v___x_3278_, 0);
v_isSharedCheck_3317_ = !lean_is_exclusive(v___x_3278_);
if (v_isSharedCheck_3317_ == 0)
{
v___x_3312_ = v___x_3278_;
v_isShared_3313_ = v_isSharedCheck_3317_;
goto v_resetjp_3311_;
}
else
{
lean_inc(v_a_3310_);
lean_dec(v___x_3278_);
v___x_3312_ = lean_box(0);
v_isShared_3313_ = v_isSharedCheck_3317_;
goto v_resetjp_3311_;
}
v_resetjp_3311_:
{
lean_object* v___x_3315_; 
if (v_isShared_3313_ == 0)
{
v___x_3315_ = v___x_3312_;
goto v_reusejp_3314_;
}
else
{
lean_object* v_reuseFailAlloc_3316_; 
v_reuseFailAlloc_3316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3316_, 0, v_a_3310_);
v___x_3315_ = v_reuseFailAlloc_3316_;
goto v_reusejp_3314_;
}
v_reusejp_3314_:
{
return v___x_3315_;
}
}
}
v___jp_3251_:
{
lean_object* v___x_3254_; 
lean_inc_ref(v_k_3236_);
v___x_3254_ = l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__1___redArg(v_k_3236_, v_v_3235_, v_ts_3250_, v___y_3253_, v_a_3237_, v_a_3238_, v_a_3246_);
lean_dec(v___y_3253_);
if (lean_obj_tag(v___x_3254_) == 0)
{
lean_object* v_a_3255_; lean_object* v___x_3256_; size_t v_sz_3257_; size_t v___x_3258_; lean_object* v___x_3259_; 
v_a_3255_ = lean_ctor_get(v___x_3254_, 0);
lean_inc(v_a_3255_);
lean_dec_ref_known(v___x_3254_, 1);
v___x_3256_ = lean_box(0);
v_sz_3257_ = lean_array_size(v___y_3252_);
v___x_3258_ = ((size_t)0ULL);
lean_inc(v_u_3234_);
v___x_3259_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__2(v_k_3236_, v_u_3234_, v_v_3235_, v___y_3252_, v_sz_3257_, v___x_3258_, v___x_3256_, v_a_3237_, v_a_3238_, v_a_3239_, v_a_3240_, v_a_3241_, v_a_3242_, v_a_3243_, v_a_3244_, v_a_3245_, v_a_3246_, v_a_3247_);
if (lean_obj_tag(v___x_3259_) == 0)
{
size_t v_sz_3260_; lean_object* v___x_3261_; 
lean_dec_ref_known(v___x_3259_, 1);
v_sz_3260_ = lean_array_size(v_a_3255_);
v___x_3261_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__3(v_k_3236_, v_v_3235_, v_u_3234_, v___y_3252_, v_a_3255_, v_sz_3260_, v___x_3258_, v___x_3256_, v_a_3237_, v_a_3238_, v_a_3239_, v_a_3240_, v_a_3241_, v_a_3242_, v_a_3243_, v_a_3244_, v_a_3245_, v_a_3246_, v_a_3247_);
lean_dec(v_a_3255_);
lean_dec_ref(v___y_3252_);
lean_dec(v_u_3234_);
if (lean_obj_tag(v___x_3261_) == 0)
{
lean_object* v___x_3263_; uint8_t v_isShared_3264_; uint8_t v_isSharedCheck_3268_; 
v_isSharedCheck_3268_ = !lean_is_exclusive(v___x_3261_);
if (v_isSharedCheck_3268_ == 0)
{
lean_object* v_unused_3269_; 
v_unused_3269_ = lean_ctor_get(v___x_3261_, 0);
lean_dec(v_unused_3269_);
v___x_3263_ = v___x_3261_;
v_isShared_3264_ = v_isSharedCheck_3268_;
goto v_resetjp_3262_;
}
else
{
lean_dec(v___x_3261_);
v___x_3263_ = lean_box(0);
v_isShared_3264_ = v_isSharedCheck_3268_;
goto v_resetjp_3262_;
}
v_resetjp_3262_:
{
lean_object* v___x_3266_; 
if (v_isShared_3264_ == 0)
{
lean_ctor_set(v___x_3263_, 0, v___x_3256_);
v___x_3266_ = v___x_3263_;
goto v_reusejp_3265_;
}
else
{
lean_object* v_reuseFailAlloc_3267_; 
v_reuseFailAlloc_3267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3267_, 0, v___x_3256_);
v___x_3266_ = v_reuseFailAlloc_3267_;
goto v_reusejp_3265_;
}
v_reusejp_3265_:
{
return v___x_3266_;
}
}
}
else
{
return v___x_3261_;
}
}
else
{
lean_dec(v_a_3255_);
lean_dec_ref(v___y_3252_);
lean_dec_ref(v_k_3236_);
lean_dec(v_v_3235_);
lean_dec(v_u_3234_);
return v___x_3259_;
}
}
else
{
lean_object* v_a_3270_; lean_object* v___x_3272_; uint8_t v_isShared_3273_; uint8_t v_isSharedCheck_3277_; 
lean_dec_ref(v___y_3252_);
lean_dec_ref(v_k_3236_);
lean_dec(v_v_3235_);
lean_dec(v_u_3234_);
v_a_3270_ = lean_ctor_get(v___x_3254_, 0);
v_isSharedCheck_3277_ = !lean_is_exclusive(v___x_3254_);
if (v_isSharedCheck_3277_ == 0)
{
v___x_3272_ = v___x_3254_;
v_isShared_3273_ = v_isSharedCheck_3277_;
goto v_resetjp_3271_;
}
else
{
lean_inc(v_a_3270_);
lean_dec(v___x_3254_);
v___x_3272_ = lean_box(0);
v_isShared_3273_ = v_isSharedCheck_3277_;
goto v_resetjp_3271_;
}
v_resetjp_3271_:
{
lean_object* v___x_3275_; 
if (v_isShared_3273_ == 0)
{
v___x_3275_ = v___x_3272_;
goto v_reusejp_3274_;
}
else
{
lean_object* v_reuseFailAlloc_3276_; 
v_reuseFailAlloc_3276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3276_, 0, v_a_3270_);
v___x_3275_ = v_reuseFailAlloc_3276_;
goto v_reusejp_3274_;
}
v_reusejp_3274_:
{
return v___x_3275_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update___boxed(lean_object* v_u_3318_, lean_object* v_v_3319_, lean_object* v_k_3320_, lean_object* v_a_3321_, lean_object* v_a_3322_, lean_object* v_a_3323_, lean_object* v_a_3324_, lean_object* v_a_3325_, lean_object* v_a_3326_, lean_object* v_a_3327_, lean_object* v_a_3328_, lean_object* v_a_3329_, lean_object* v_a_3330_, lean_object* v_a_3331_, lean_object* v_a_3332_){
_start:
{
lean_object* v_res_3333_; 
v_res_3333_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update(v_u_3318_, v_v_3319_, v_k_3320_, v_a_3321_, v_a_3322_, v_a_3323_, v_a_3324_, v_a_3325_, v_a_3326_, v_a_3327_, v_a_3328_, v_a_3329_, v_a_3330_, v_a_3331_);
lean_dec(v_a_3331_);
lean_dec_ref(v_a_3330_);
lean_dec(v_a_3329_);
lean_dec_ref(v_a_3328_);
lean_dec(v_a_3327_);
lean_dec_ref(v_a_3326_);
lean_dec(v_a_3325_);
lean_dec_ref(v_a_3324_);
lean_dec(v_a_3323_);
lean_dec(v_a_3322_);
lean_dec(v_a_3321_);
return v_res_3333_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0(lean_object* v_k_3334_, lean_object* v_u_3335_, lean_object* v_x_3336_, lean_object* v_x_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_){
_start:
{
lean_object* v___x_3350_; 
v___x_3350_ = l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0___redArg(v_k_3334_, v_u_3335_, v_x_3336_, v_x_3337_, v___y_3338_, v___y_3339_, v___y_3347_);
return v___x_3350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0___boxed(lean_object* v_k_3351_, lean_object* v_u_3352_, lean_object* v_x_3353_, lean_object* v_x_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_){
_start:
{
lean_object* v_res_3367_; 
v_res_3367_ = l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0(v_k_3351_, v_u_3352_, v_x_3353_, v_x_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_);
lean_dec(v___y_3365_);
lean_dec_ref(v___y_3364_);
lean_dec(v___y_3363_);
lean_dec_ref(v___y_3362_);
lean_dec(v___y_3361_);
lean_dec_ref(v___y_3360_);
lean_dec(v___y_3359_);
lean_dec_ref(v___y_3358_);
lean_dec(v___y_3357_);
lean_dec(v___y_3356_);
lean_dec(v___y_3355_);
lean_dec(v_u_3352_);
lean_dec_ref(v_k_3351_);
return v_res_3367_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__1(lean_object* v_k_3368_, lean_object* v_v_3369_, lean_object* v_x_3370_, lean_object* v_x_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_){
_start:
{
lean_object* v___x_3384_; 
v___x_3384_ = l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__1___redArg(v_k_3368_, v_v_3369_, v_x_3370_, v_x_3371_, v___y_3372_, v___y_3373_, v___y_3381_);
return v___x_3384_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__1___boxed(lean_object* v_k_3385_, lean_object* v_v_3386_, lean_object* v_x_3387_, lean_object* v_x_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_){
_start:
{
lean_object* v_res_3401_; 
v_res_3401_ = l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__1(v_k_3385_, v_v_3386_, v_x_3387_, v_x_3388_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_);
lean_dec(v___y_3399_);
lean_dec_ref(v___y_3398_);
lean_dec(v___y_3397_);
lean_dec_ref(v___y_3396_);
lean_dec(v___y_3395_);
lean_dec_ref(v___y_3394_);
lean_dec(v___y_3393_);
lean_dec_ref(v___y_3392_);
lean_dec(v___y_3391_);
lean_dec(v___y_3390_);
lean_dec(v___y_3389_);
lean_dec(v_x_3388_);
lean_dec(v_v_3386_);
return v_res_3401_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_addEdge___closed__2(void){
_start:
{
lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; 
v___x_3408_ = ((lean_object*)(l_Lean_Meta_Grind_Order_addEdge___closed__1));
v___x_3409_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__6));
v___x_3410_ = l_Lean_Name_append(v___x_3409_, v___x_3408_);
return v___x_3410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_addEdge(lean_object* v_u_3411_, lean_object* v_v_3412_, lean_object* v_k_3413_, lean_object* v_h_3414_, lean_object* v_a_3415_, lean_object* v_a_3416_, lean_object* v_a_3417_, lean_object* v_a_3418_, lean_object* v_a_3419_, lean_object* v_a_3420_, lean_object* v_a_3421_, lean_object* v_a_3422_, lean_object* v_a_3423_, lean_object* v_a_3424_, lean_object* v_a_3425_){
_start:
{
lean_object* v___y_3428_; lean_object* v___y_3429_; lean_object* v___y_3430_; lean_object* v___y_3431_; lean_object* v___y_3432_; lean_object* v___y_3433_; lean_object* v___y_3434_; lean_object* v___y_3435_; lean_object* v___y_3436_; lean_object* v___y_3437_; lean_object* v___y_3438_; lean_object* v___y_3465_; lean_object* v___y_3466_; lean_object* v___y_3467_; lean_object* v___y_3468_; lean_object* v___y_3469_; lean_object* v___y_3470_; lean_object* v___y_3471_; lean_object* v___y_3472_; lean_object* v___y_3473_; lean_object* v___y_3474_; lean_object* v___y_3475_; lean_object* v___x_3502_; 
v___x_3502_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_3416_);
if (lean_obj_tag(v___x_3502_) == 0)
{
lean_object* v_a_3503_; lean_object* v___x_3505_; uint8_t v_isShared_3506_; uint8_t v_isSharedCheck_3580_; 
v_a_3503_ = lean_ctor_get(v___x_3502_, 0);
v_isSharedCheck_3580_ = !lean_is_exclusive(v___x_3502_);
if (v_isSharedCheck_3580_ == 0)
{
v___x_3505_ = v___x_3502_;
v_isShared_3506_ = v_isSharedCheck_3580_;
goto v_resetjp_3504_;
}
else
{
lean_inc(v_a_3503_);
lean_dec(v___x_3502_);
v___x_3505_ = lean_box(0);
v_isShared_3506_ = v_isSharedCheck_3580_;
goto v_resetjp_3504_;
}
v_resetjp_3504_:
{
uint8_t v___x_3507_; 
v___x_3507_ = lean_unbox(v_a_3503_);
lean_dec(v_a_3503_);
if (v___x_3507_ == 0)
{
uint8_t v___x_3508_; 
lean_del_object(v___x_3505_);
v___x_3508_ = lean_nat_dec_eq(v_u_3411_, v_v_3412_);
if (v___x_3508_ == 0)
{
lean_object* v_toCold_3509_; lean_object* v_options_3510_; uint8_t v_hasTrace_3511_; 
v_toCold_3509_ = lean_ctor_get(v_a_3424_, 0);
v_options_3510_ = lean_ctor_get(v_toCold_3509_, 2);
v_hasTrace_3511_ = lean_ctor_get_uint8(v_options_3510_, sizeof(void*)*1);
if (v_hasTrace_3511_ == 0)
{
v___y_3465_ = v_a_3415_;
v___y_3466_ = v_a_3416_;
v___y_3467_ = v_a_3417_;
v___y_3468_ = v_a_3418_;
v___y_3469_ = v_a_3419_;
v___y_3470_ = v_a_3420_;
v___y_3471_ = v_a_3421_;
v___y_3472_ = v_a_3422_;
v___y_3473_ = v_a_3423_;
v___y_3474_ = v_a_3424_;
v___y_3475_ = v_a_3425_;
goto v___jp_3464_;
}
else
{
lean_object* v_inheritedTraceOptions_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; uint8_t v___x_3515_; 
v_inheritedTraceOptions_3512_ = lean_ctor_get(v_toCold_3509_, 11);
v___x_3513_ = ((lean_object*)(l_Lean_Meta_Grind_Order_addEdge___closed__1));
v___x_3514_ = lean_obj_once(&l_Lean_Meta_Grind_Order_addEdge___closed__2, &l_Lean_Meta_Grind_Order_addEdge___closed__2_once, _init_l_Lean_Meta_Grind_Order_addEdge___closed__2);
v___x_3515_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3512_, v_options_3510_, v___x_3514_);
if (v___x_3515_ == 0)
{
v___y_3465_ = v_a_3415_;
v___y_3466_ = v_a_3416_;
v___y_3467_ = v_a_3417_;
v___y_3468_ = v_a_3418_;
v___y_3469_ = v_a_3419_;
v___y_3470_ = v_a_3420_;
v___y_3471_ = v_a_3421_;
v___y_3472_ = v_a_3422_;
v___y_3473_ = v_a_3423_;
v___y_3474_ = v_a_3424_;
v___y_3475_ = v_a_3425_;
goto v___jp_3464_;
}
else
{
lean_object* v___x_3516_; 
v___x_3516_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_u_3411_, v_a_3415_, v_a_3416_, v_a_3424_);
if (lean_obj_tag(v___x_3516_) == 0)
{
lean_object* v_a_3517_; lean_object* v___x_3518_; 
v_a_3517_ = lean_ctor_get(v___x_3516_, 0);
lean_inc(v_a_3517_);
lean_dec_ref_known(v___x_3516_, 1);
v___x_3518_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_v_3412_, v_a_3415_, v_a_3416_, v_a_3424_);
if (lean_obj_tag(v___x_3518_) == 0)
{
lean_object* v_a_3519_; lean_object* v_k_3520_; uint8_t v_strict_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___y_3529_; 
v_a_3519_ = lean_ctor_get(v___x_3518_, 0);
lean_inc(v_a_3519_);
lean_dec_ref_known(v___x_3518_, 1);
v_k_3520_ = lean_ctor_get(v_k_3413_, 0);
v_strict_3521_ = lean_ctor_get_uint8(v_k_3413_, sizeof(void*)*1);
v___x_3522_ = l_Lean_MessageData_ofExpr(v_a_3517_);
v___x_3523_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4);
v___x_3524_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3524_, 0, v___x_3522_);
lean_ctor_set(v___x_3524_, 1, v___x_3523_);
v___x_3525_ = l_Lean_MessageData_ofExpr(v_a_3519_);
v___x_3526_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3526_, 0, v___x_3524_);
lean_ctor_set(v___x_3526_, 1, v___x_3525_);
v___x_3527_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3527_, 0, v___x_3526_);
lean_ctor_set(v___x_3527_, 1, v___x_3523_);
if (v_strict_3521_ == 0)
{
lean_object* v___x_3534_; 
v___x_3534_ = l_Int_repr(v_k_3520_);
v___y_3529_ = v___x_3534_;
goto v___jp_3528_;
}
else
{
lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; 
v___x_3535_ = l_Int_repr(v_k_3520_);
v___x_3536_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5));
v___x_3537_ = lean_string_append(v___x_3535_, v___x_3536_);
v___y_3529_ = v___x_3537_;
goto v___jp_3528_;
}
v___jp_3528_:
{
lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; 
v___x_3530_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3530_, 0, v___y_3529_);
v___x_3531_ = l_Lean_MessageData_ofFormat(v___x_3530_);
v___x_3532_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3532_, 0, v___x_3527_);
lean_ctor_set(v___x_3532_, 1, v___x_3531_);
v___x_3533_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(v___x_3513_, v___x_3532_, v_a_3422_, v_a_3423_, v_a_3424_, v_a_3425_);
if (lean_obj_tag(v___x_3533_) == 0)
{
lean_dec_ref_known(v___x_3533_, 1);
v___y_3465_ = v_a_3415_;
v___y_3466_ = v_a_3416_;
v___y_3467_ = v_a_3417_;
v___y_3468_ = v_a_3418_;
v___y_3469_ = v_a_3419_;
v___y_3470_ = v_a_3420_;
v___y_3471_ = v_a_3421_;
v___y_3472_ = v_a_3422_;
v___y_3473_ = v_a_3423_;
v___y_3474_ = v_a_3424_;
v___y_3475_ = v_a_3425_;
goto v___jp_3464_;
}
else
{
lean_dec_ref(v_h_3414_);
lean_dec_ref(v_k_3413_);
lean_dec(v_v_3412_);
lean_dec(v_u_3411_);
return v___x_3533_;
}
}
}
else
{
lean_object* v_a_3538_; lean_object* v___x_3540_; uint8_t v_isShared_3541_; uint8_t v_isSharedCheck_3545_; 
lean_dec(v_a_3517_);
lean_dec_ref(v_h_3414_);
lean_dec_ref(v_k_3413_);
lean_dec(v_v_3412_);
lean_dec(v_u_3411_);
v_a_3538_ = lean_ctor_get(v___x_3518_, 0);
v_isSharedCheck_3545_ = !lean_is_exclusive(v___x_3518_);
if (v_isSharedCheck_3545_ == 0)
{
v___x_3540_ = v___x_3518_;
v_isShared_3541_ = v_isSharedCheck_3545_;
goto v_resetjp_3539_;
}
else
{
lean_inc(v_a_3538_);
lean_dec(v___x_3518_);
v___x_3540_ = lean_box(0);
v_isShared_3541_ = v_isSharedCheck_3545_;
goto v_resetjp_3539_;
}
v_resetjp_3539_:
{
lean_object* v___x_3543_; 
if (v_isShared_3541_ == 0)
{
v___x_3543_ = v___x_3540_;
goto v_reusejp_3542_;
}
else
{
lean_object* v_reuseFailAlloc_3544_; 
v_reuseFailAlloc_3544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3544_, 0, v_a_3538_);
v___x_3543_ = v_reuseFailAlloc_3544_;
goto v_reusejp_3542_;
}
v_reusejp_3542_:
{
return v___x_3543_;
}
}
}
}
else
{
lean_object* v_a_3546_; lean_object* v___x_3548_; uint8_t v_isShared_3549_; uint8_t v_isSharedCheck_3553_; 
lean_dec_ref(v_h_3414_);
lean_dec_ref(v_k_3413_);
lean_dec(v_v_3412_);
lean_dec(v_u_3411_);
v_a_3546_ = lean_ctor_get(v___x_3516_, 0);
v_isSharedCheck_3553_ = !lean_is_exclusive(v___x_3516_);
if (v_isSharedCheck_3553_ == 0)
{
v___x_3548_ = v___x_3516_;
v_isShared_3549_ = v_isSharedCheck_3553_;
goto v_resetjp_3547_;
}
else
{
lean_inc(v_a_3546_);
lean_dec(v___x_3516_);
v___x_3548_ = lean_box(0);
v_isShared_3549_ = v_isSharedCheck_3553_;
goto v_resetjp_3547_;
}
v_resetjp_3547_:
{
lean_object* v___x_3551_; 
if (v_isShared_3549_ == 0)
{
v___x_3551_ = v___x_3548_;
goto v_reusejp_3550_;
}
else
{
lean_object* v_reuseFailAlloc_3552_; 
v_reuseFailAlloc_3552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3552_, 0, v_a_3546_);
v___x_3551_ = v_reuseFailAlloc_3552_;
goto v_reusejp_3550_;
}
v_reusejp_3550_:
{
return v___x_3551_;
}
}
}
}
}
}
else
{
uint8_t v___x_3554_; 
lean_dec(v_v_3412_);
v___x_3554_ = l_Lean_Meta_Grind_Order_Weight_isNeg(v_k_3413_);
if (v___x_3554_ == 0)
{
lean_dec_ref(v_h_3414_);
lean_dec_ref(v_k_3413_);
lean_dec(v_u_3411_);
goto v___jp_3499_;
}
else
{
lean_object* v___x_3555_; 
v___x_3555_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_u_3411_, v_a_3415_, v_a_3416_, v_a_3424_);
lean_dec(v_u_3411_);
if (lean_obj_tag(v___x_3555_) == 0)
{
lean_object* v_a_3556_; lean_object* v___x_3557_; 
v_a_3556_ = lean_ctor_get(v___x_3555_, 0);
lean_inc(v_a_3556_);
lean_dec_ref_known(v___x_3555_, 1);
v___x_3557_ = l_Lean_Meta_Grind_Order_mkSelfUnsatProof(v_a_3556_, v_k_3413_, v_h_3414_, v_a_3415_, v_a_3416_, v_a_3417_, v_a_3418_, v_a_3419_, v_a_3420_, v_a_3421_, v_a_3422_, v_a_3423_, v_a_3424_, v_a_3425_);
lean_dec_ref(v_k_3413_);
if (lean_obj_tag(v___x_3557_) == 0)
{
lean_object* v_a_3558_; lean_object* v___x_3559_; 
v_a_3558_ = lean_ctor_get(v___x_3557_, 0);
lean_inc(v_a_3558_);
lean_dec_ref_known(v___x_3557_, 1);
v___x_3559_ = l_Lean_Meta_Grind_closeGoal(v_a_3558_, v_a_3416_, v_a_3417_, v_a_3418_, v_a_3419_, v_a_3420_, v_a_3421_, v_a_3422_, v_a_3423_, v_a_3424_, v_a_3425_);
if (lean_obj_tag(v___x_3559_) == 0)
{
lean_dec_ref_known(v___x_3559_, 1);
goto v___jp_3499_;
}
else
{
return v___x_3559_;
}
}
else
{
lean_object* v_a_3560_; lean_object* v___x_3562_; uint8_t v_isShared_3563_; uint8_t v_isSharedCheck_3567_; 
v_a_3560_ = lean_ctor_get(v___x_3557_, 0);
v_isSharedCheck_3567_ = !lean_is_exclusive(v___x_3557_);
if (v_isSharedCheck_3567_ == 0)
{
v___x_3562_ = v___x_3557_;
v_isShared_3563_ = v_isSharedCheck_3567_;
goto v_resetjp_3561_;
}
else
{
lean_inc(v_a_3560_);
lean_dec(v___x_3557_);
v___x_3562_ = lean_box(0);
v_isShared_3563_ = v_isSharedCheck_3567_;
goto v_resetjp_3561_;
}
v_resetjp_3561_:
{
lean_object* v___x_3565_; 
if (v_isShared_3563_ == 0)
{
v___x_3565_ = v___x_3562_;
goto v_reusejp_3564_;
}
else
{
lean_object* v_reuseFailAlloc_3566_; 
v_reuseFailAlloc_3566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3566_, 0, v_a_3560_);
v___x_3565_ = v_reuseFailAlloc_3566_;
goto v_reusejp_3564_;
}
v_reusejp_3564_:
{
return v___x_3565_;
}
}
}
}
else
{
lean_object* v_a_3568_; lean_object* v___x_3570_; uint8_t v_isShared_3571_; uint8_t v_isSharedCheck_3575_; 
lean_dec_ref(v_h_3414_);
lean_dec_ref(v_k_3413_);
v_a_3568_ = lean_ctor_get(v___x_3555_, 0);
v_isSharedCheck_3575_ = !lean_is_exclusive(v___x_3555_);
if (v_isSharedCheck_3575_ == 0)
{
v___x_3570_ = v___x_3555_;
v_isShared_3571_ = v_isSharedCheck_3575_;
goto v_resetjp_3569_;
}
else
{
lean_inc(v_a_3568_);
lean_dec(v___x_3555_);
v___x_3570_ = lean_box(0);
v_isShared_3571_ = v_isSharedCheck_3575_;
goto v_resetjp_3569_;
}
v_resetjp_3569_:
{
lean_object* v___x_3573_; 
if (v_isShared_3571_ == 0)
{
v___x_3573_ = v___x_3570_;
goto v_reusejp_3572_;
}
else
{
lean_object* v_reuseFailAlloc_3574_; 
v_reuseFailAlloc_3574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3574_, 0, v_a_3568_);
v___x_3573_ = v_reuseFailAlloc_3574_;
goto v_reusejp_3572_;
}
v_reusejp_3572_:
{
return v___x_3573_;
}
}
}
}
}
}
else
{
lean_object* v___x_3576_; lean_object* v___x_3578_; 
lean_dec_ref(v_h_3414_);
lean_dec_ref(v_k_3413_);
lean_dec(v_v_3412_);
lean_dec(v_u_3411_);
v___x_3576_ = lean_box(0);
if (v_isShared_3506_ == 0)
{
lean_ctor_set(v___x_3505_, 0, v___x_3576_);
v___x_3578_ = v___x_3505_;
goto v_reusejp_3577_;
}
else
{
lean_object* v_reuseFailAlloc_3579_; 
v_reuseFailAlloc_3579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3579_, 0, v___x_3576_);
v___x_3578_ = v_reuseFailAlloc_3579_;
goto v_reusejp_3577_;
}
v_reusejp_3577_:
{
return v___x_3578_;
}
}
}
}
else
{
lean_object* v_a_3581_; lean_object* v___x_3583_; uint8_t v_isShared_3584_; uint8_t v_isSharedCheck_3588_; 
lean_dec_ref(v_h_3414_);
lean_dec_ref(v_k_3413_);
lean_dec(v_v_3412_);
lean_dec(v_u_3411_);
v_a_3581_ = lean_ctor_get(v___x_3502_, 0);
v_isSharedCheck_3588_ = !lean_is_exclusive(v___x_3502_);
if (v_isSharedCheck_3588_ == 0)
{
v___x_3583_ = v___x_3502_;
v_isShared_3584_ = v_isSharedCheck_3588_;
goto v_resetjp_3582_;
}
else
{
lean_inc(v_a_3581_);
lean_dec(v___x_3502_);
v___x_3583_ = lean_box(0);
v_isShared_3584_ = v_isSharedCheck_3588_;
goto v_resetjp_3582_;
}
v_resetjp_3582_:
{
lean_object* v___x_3586_; 
if (v_isShared_3584_ == 0)
{
v___x_3586_ = v___x_3583_;
goto v_reusejp_3585_;
}
else
{
lean_object* v_reuseFailAlloc_3587_; 
v_reuseFailAlloc_3587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3587_, 0, v_a_3581_);
v___x_3586_ = v_reuseFailAlloc_3587_;
goto v_reusejp_3585_;
}
v_reusejp_3585_:
{
return v___x_3586_;
}
}
}
v___jp_3427_:
{
lean_object* v___x_3439_; 
v___x_3439_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isShorter___redArg(v_u_3411_, v_v_3412_, v_k_3413_, v___y_3428_, v___y_3429_, v___y_3437_);
if (lean_obj_tag(v___x_3439_) == 0)
{
lean_object* v_a_3440_; lean_object* v___x_3442_; uint8_t v_isShared_3443_; uint8_t v_isSharedCheck_3455_; 
v_a_3440_ = lean_ctor_get(v___x_3439_, 0);
v_isSharedCheck_3455_ = !lean_is_exclusive(v___x_3439_);
if (v_isSharedCheck_3455_ == 0)
{
v___x_3442_ = v___x_3439_;
v_isShared_3443_ = v_isSharedCheck_3455_;
goto v_resetjp_3441_;
}
else
{
lean_inc(v_a_3440_);
lean_dec(v___x_3439_);
v___x_3442_ = lean_box(0);
v_isShared_3443_ = v_isSharedCheck_3455_;
goto v_resetjp_3441_;
}
v_resetjp_3441_:
{
uint8_t v___x_3444_; 
v___x_3444_ = lean_unbox(v_a_3440_);
lean_dec(v_a_3440_);
if (v___x_3444_ == 0)
{
lean_object* v___x_3445_; lean_object* v___x_3447_; 
lean_dec_ref(v_h_3414_);
lean_dec_ref(v_k_3413_);
lean_dec(v_v_3412_);
lean_dec(v_u_3411_);
v___x_3445_ = lean_box(0);
if (v_isShared_3443_ == 0)
{
lean_ctor_set(v___x_3442_, 0, v___x_3445_);
v___x_3447_ = v___x_3442_;
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
else
{
lean_object* v___x_3449_; 
lean_del_object(v___x_3442_);
lean_inc_ref(v_k_3413_);
lean_inc(v_v_3412_);
lean_inc(v_u_3411_);
v___x_3449_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist___redArg(v_u_3411_, v_v_3412_, v_k_3413_, v___y_3428_, v___y_3429_);
if (lean_obj_tag(v___x_3449_) == 0)
{
lean_object* v___x_3450_; lean_object* v___x_3451_; 
lean_dec_ref_known(v___x_3449_, 1);
lean_inc_ref(v_k_3413_);
lean_inc_n(v_u_3411_, 2);
v___x_3450_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3450_, 0, v_u_3411_);
lean_ctor_set(v___x_3450_, 1, v_k_3413_);
lean_ctor_set(v___x_3450_, 2, v_h_3414_);
lean_inc(v_v_3412_);
v___x_3451_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___redArg(v_u_3411_, v_v_3412_, v___x_3450_, v___y_3428_, v___y_3429_);
if (lean_obj_tag(v___x_3451_) == 0)
{
lean_object* v___x_3452_; 
lean_dec_ref_known(v___x_3451_, 1);
lean_inc_ref(v_k_3413_);
lean_inc(v_v_3412_);
lean_inc(v_u_3411_);
v___x_3452_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate(v_u_3411_, v_v_3412_, v_k_3413_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_);
if (lean_obj_tag(v___x_3452_) == 0)
{
lean_object* v___x_3453_; 
lean_dec_ref_known(v___x_3452_, 1);
v___x_3453_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update(v_u_3411_, v_v_3412_, v_k_3413_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_);
if (lean_obj_tag(v___x_3453_) == 0)
{
lean_object* v___x_3454_; 
lean_dec_ref_known(v___x_3453_, 1);
v___x_3454_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending(v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_);
return v___x_3454_;
}
else
{
return v___x_3453_;
}
}
else
{
lean_dec_ref(v_k_3413_);
lean_dec(v_v_3412_);
lean_dec(v_u_3411_);
return v___x_3452_;
}
}
else
{
lean_dec_ref(v_k_3413_);
lean_dec(v_v_3412_);
lean_dec(v_u_3411_);
return v___x_3451_;
}
}
else
{
lean_dec_ref(v_h_3414_);
lean_dec_ref(v_k_3413_);
lean_dec(v_v_3412_);
lean_dec(v_u_3411_);
return v___x_3449_;
}
}
}
}
else
{
lean_object* v_a_3456_; lean_object* v___x_3458_; uint8_t v_isShared_3459_; uint8_t v_isSharedCheck_3463_; 
lean_dec_ref(v_h_3414_);
lean_dec_ref(v_k_3413_);
lean_dec(v_v_3412_);
lean_dec(v_u_3411_);
v_a_3456_ = lean_ctor_get(v___x_3439_, 0);
v_isSharedCheck_3463_ = !lean_is_exclusive(v___x_3439_);
if (v_isSharedCheck_3463_ == 0)
{
v___x_3458_ = v___x_3439_;
v_isShared_3459_ = v_isSharedCheck_3463_;
goto v_resetjp_3457_;
}
else
{
lean_inc(v_a_3456_);
lean_dec(v___x_3439_);
v___x_3458_ = lean_box(0);
v_isShared_3459_ = v_isSharedCheck_3463_;
goto v_resetjp_3457_;
}
v_resetjp_3457_:
{
lean_object* v___x_3461_; 
if (v_isShared_3459_ == 0)
{
v___x_3461_ = v___x_3458_;
goto v_reusejp_3460_;
}
else
{
lean_object* v_reuseFailAlloc_3462_; 
v_reuseFailAlloc_3462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3462_, 0, v_a_3456_);
v___x_3461_ = v_reuseFailAlloc_3462_;
goto v_reusejp_3460_;
}
v_reusejp_3460_:
{
return v___x_3461_;
}
}
}
}
v___jp_3464_:
{
lean_object* v___x_3476_; 
v___x_3476_ = l_Lean_Meta_Grind_Order_getDist_x3f___redArg(v_v_3412_, v_u_3411_, v___y_3465_, v___y_3466_, v___y_3474_);
if (lean_obj_tag(v___x_3476_) == 0)
{
lean_object* v_a_3477_; 
v_a_3477_ = lean_ctor_get(v___x_3476_, 0);
lean_inc(v_a_3477_);
lean_dec_ref_known(v___x_3476_, 1);
if (lean_obj_tag(v_a_3477_) == 1)
{
lean_object* v_val_3478_; lean_object* v___x_3479_; uint8_t v___x_3480_; 
v_val_3478_ = lean_ctor_get(v_a_3477_, 0);
lean_inc_n(v_val_3478_, 2);
lean_dec_ref_known(v_a_3477_, 1);
v___x_3479_ = l_Lean_Meta_Grind_Order_Weight_add(v_k_3413_, v_val_3478_);
v___x_3480_ = l_Lean_Meta_Grind_Order_Weight_isNeg(v___x_3479_);
lean_dec_ref(v___x_3479_);
if (v___x_3480_ == 0)
{
lean_dec(v_val_3478_);
v___y_3428_ = v___y_3465_;
v___y_3429_ = v___y_3466_;
v___y_3430_ = v___y_3467_;
v___y_3431_ = v___y_3468_;
v___y_3432_ = v___y_3469_;
v___y_3433_ = v___y_3470_;
v___y_3434_ = v___y_3471_;
v___y_3435_ = v___y_3472_;
v___y_3436_ = v___y_3473_;
v___y_3437_ = v___y_3474_;
v___y_3438_ = v___y_3475_;
goto v___jp_3427_;
}
else
{
lean_object* v___x_3481_; 
v___x_3481_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setUnsat(v_u_3411_, v_v_3412_, v_k_3413_, v_h_3414_, v_val_3478_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_);
lean_dec(v_val_3478_);
lean_dec_ref(v_k_3413_);
lean_dec(v_v_3412_);
lean_dec(v_u_3411_);
if (lean_obj_tag(v___x_3481_) == 0)
{
lean_object* v___x_3483_; uint8_t v_isShared_3484_; uint8_t v_isSharedCheck_3489_; 
v_isSharedCheck_3489_ = !lean_is_exclusive(v___x_3481_);
if (v_isSharedCheck_3489_ == 0)
{
lean_object* v_unused_3490_; 
v_unused_3490_ = lean_ctor_get(v___x_3481_, 0);
lean_dec(v_unused_3490_);
v___x_3483_ = v___x_3481_;
v_isShared_3484_ = v_isSharedCheck_3489_;
goto v_resetjp_3482_;
}
else
{
lean_dec(v___x_3481_);
v___x_3483_ = lean_box(0);
v_isShared_3484_ = v_isSharedCheck_3489_;
goto v_resetjp_3482_;
}
v_resetjp_3482_:
{
lean_object* v___x_3485_; lean_object* v___x_3487_; 
v___x_3485_ = lean_box(0);
if (v_isShared_3484_ == 0)
{
lean_ctor_set(v___x_3483_, 0, v___x_3485_);
v___x_3487_ = v___x_3483_;
goto v_reusejp_3486_;
}
else
{
lean_object* v_reuseFailAlloc_3488_; 
v_reuseFailAlloc_3488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3488_, 0, v___x_3485_);
v___x_3487_ = v_reuseFailAlloc_3488_;
goto v_reusejp_3486_;
}
v_reusejp_3486_:
{
return v___x_3487_;
}
}
}
else
{
return v___x_3481_;
}
}
}
else
{
lean_dec(v_a_3477_);
v___y_3428_ = v___y_3465_;
v___y_3429_ = v___y_3466_;
v___y_3430_ = v___y_3467_;
v___y_3431_ = v___y_3468_;
v___y_3432_ = v___y_3469_;
v___y_3433_ = v___y_3470_;
v___y_3434_ = v___y_3471_;
v___y_3435_ = v___y_3472_;
v___y_3436_ = v___y_3473_;
v___y_3437_ = v___y_3474_;
v___y_3438_ = v___y_3475_;
goto v___jp_3427_;
}
}
else
{
lean_object* v_a_3491_; lean_object* v___x_3493_; uint8_t v_isShared_3494_; uint8_t v_isSharedCheck_3498_; 
lean_dec_ref(v_h_3414_);
lean_dec_ref(v_k_3413_);
lean_dec(v_v_3412_);
lean_dec(v_u_3411_);
v_a_3491_ = lean_ctor_get(v___x_3476_, 0);
v_isSharedCheck_3498_ = !lean_is_exclusive(v___x_3476_);
if (v_isSharedCheck_3498_ == 0)
{
v___x_3493_ = v___x_3476_;
v_isShared_3494_ = v_isSharedCheck_3498_;
goto v_resetjp_3492_;
}
else
{
lean_inc(v_a_3491_);
lean_dec(v___x_3476_);
v___x_3493_ = lean_box(0);
v_isShared_3494_ = v_isSharedCheck_3498_;
goto v_resetjp_3492_;
}
v_resetjp_3492_:
{
lean_object* v___x_3496_; 
if (v_isShared_3494_ == 0)
{
v___x_3496_ = v___x_3493_;
goto v_reusejp_3495_;
}
else
{
lean_object* v_reuseFailAlloc_3497_; 
v_reuseFailAlloc_3497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3497_, 0, v_a_3491_);
v___x_3496_ = v_reuseFailAlloc_3497_;
goto v_reusejp_3495_;
}
v_reusejp_3495_:
{
return v___x_3496_;
}
}
}
}
v___jp_3499_:
{
lean_object* v___x_3500_; lean_object* v___x_3501_; 
v___x_3500_ = lean_box(0);
v___x_3501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3501_, 0, v___x_3500_);
return v___x_3501_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_addEdge___boxed(lean_object* v_u_3589_, lean_object* v_v_3590_, lean_object* v_k_3591_, lean_object* v_h_3592_, lean_object* v_a_3593_, lean_object* v_a_3594_, lean_object* v_a_3595_, lean_object* v_a_3596_, lean_object* v_a_3597_, lean_object* v_a_3598_, lean_object* v_a_3599_, lean_object* v_a_3600_, lean_object* v_a_3601_, lean_object* v_a_3602_, lean_object* v_a_3603_, lean_object* v_a_3604_){
_start:
{
lean_object* v_res_3605_; 
v_res_3605_ = l_Lean_Meta_Grind_Order_addEdge(v_u_3589_, v_v_3590_, v_k_3591_, v_h_3592_, v_a_3593_, v_a_3594_, v_a_3595_, v_a_3596_, v_a_3597_, v_a_3598_, v_a_3599_, v_a_3600_, v_a_3601_, v_a_3602_, v_a_3603_);
lean_dec(v_a_3603_);
lean_dec_ref(v_a_3602_);
lean_dec(v_a_3601_);
lean_dec_ref(v_a_3600_);
lean_dec(v_a_3599_);
lean_dec_ref(v_a_3598_);
lean_dec(v_a_3597_);
lean_dec_ref(v_a_3596_);
lean_dec(v_a_3595_);
lean_dec(v_a_3594_);
lean_dec(v_a_3593_);
return v_res_3605_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__2(void){
_start:
{
lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; 
v___x_3612_ = lean_box(0);
v___x_3613_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__1));
v___x_3614_ = l_Lean_mkConst(v___x_3613_, v___x_3612_);
return v___x_3614_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5(void){
_start:
{
lean_object* v_cls_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; 
v_cls_3620_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__4));
v___x_3621_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__6));
v___x_3622_ = l_Lean_Name_append(v___x_3621_, v_cls_3620_);
return v___x_3622_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue(lean_object* v_c_3623_, lean_object* v_e_3624_, lean_object* v_he_3625_, lean_object* v_a_3626_, lean_object* v_a_3627_, lean_object* v_a_3628_, lean_object* v_a_3629_, lean_object* v_a_3630_, lean_object* v_a_3631_, lean_object* v_a_3632_, lean_object* v_a_3633_, lean_object* v_a_3634_, lean_object* v_a_3635_, lean_object* v_a_3636_){
_start:
{
lean_object* v___y_3639_; lean_object* v___y_3640_; lean_object* v___y_3641_; lean_object* v___y_3642_; lean_object* v___y_3643_; lean_object* v___y_3644_; lean_object* v___y_3645_; lean_object* v___y_3646_; lean_object* v___y_3647_; lean_object* v___y_3648_; lean_object* v___y_3649_; lean_object* v___y_3650_; lean_object* v___y_3651_; lean_object* v___y_3652_; lean_object* v___y_3653_; uint8_t v___y_3654_; lean_object* v_h_3658_; lean_object* v___y_3659_; lean_object* v___y_3660_; lean_object* v___y_3661_; lean_object* v___y_3662_; lean_object* v___y_3663_; lean_object* v___y_3664_; lean_object* v___y_3665_; lean_object* v___y_3666_; lean_object* v___y_3667_; lean_object* v___y_3668_; lean_object* v___y_3669_; lean_object* v___y_3680_; lean_object* v___y_3681_; lean_object* v___y_3682_; lean_object* v___y_3683_; lean_object* v___y_3684_; lean_object* v___y_3685_; lean_object* v___y_3686_; lean_object* v___y_3687_; lean_object* v___y_3688_; lean_object* v___y_3689_; lean_object* v___y_3690_; lean_object* v_toCold_3698_; lean_object* v_options_3699_; uint8_t v_hasTrace_3700_; 
v_toCold_3698_ = lean_ctor_get(v_a_3635_, 0);
v_options_3699_ = lean_ctor_get(v_toCold_3698_, 2);
v_hasTrace_3700_ = lean_ctor_get_uint8(v_options_3699_, sizeof(void*)*1);
if (v_hasTrace_3700_ == 0)
{
v___y_3680_ = v_a_3626_;
v___y_3681_ = v_a_3627_;
v___y_3682_ = v_a_3628_;
v___y_3683_ = v_a_3629_;
v___y_3684_ = v_a_3630_;
v___y_3685_ = v_a_3631_;
v___y_3686_ = v_a_3632_;
v___y_3687_ = v_a_3633_;
v___y_3688_ = v_a_3634_;
v___y_3689_ = v_a_3635_;
v___y_3690_ = v_a_3636_;
goto v___jp_3679_;
}
else
{
lean_object* v_inheritedTraceOptions_3701_; lean_object* v_cls_3702_; lean_object* v___x_3703_; uint8_t v___x_3704_; 
v_inheritedTraceOptions_3701_ = lean_ctor_get(v_toCold_3698_, 11);
v_cls_3702_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__4));
v___x_3703_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5);
v___x_3704_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3701_, v_options_3699_, v___x_3703_);
if (v___x_3704_ == 0)
{
v___y_3680_ = v_a_3626_;
v___y_3681_ = v_a_3627_;
v___y_3682_ = v_a_3628_;
v___y_3683_ = v_a_3629_;
v___y_3684_ = v_a_3630_;
v___y_3685_ = v_a_3631_;
v___y_3686_ = v_a_3632_;
v___y_3687_ = v_a_3633_;
v___y_3688_ = v_a_3634_;
v___y_3689_ = v_a_3635_;
v___y_3690_ = v_a_3636_;
goto v___jp_3679_;
}
else
{
lean_object* v___x_3705_; 
v___x_3705_ = l_Lean_Meta_Grind_Order_Cnstr_pp___redArg(v_c_3623_, v_a_3626_, v_a_3627_, v_a_3635_);
if (lean_obj_tag(v___x_3705_) == 0)
{
lean_object* v_a_3706_; lean_object* v___x_3707_; 
v_a_3706_ = lean_ctor_get(v___x_3705_, 0);
lean_inc(v_a_3706_);
lean_dec_ref_known(v___x_3705_, 1);
v___x_3707_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(v_cls_3702_, v_a_3706_, v_a_3633_, v_a_3634_, v_a_3635_, v_a_3636_);
if (lean_obj_tag(v___x_3707_) == 0)
{
lean_dec_ref_known(v___x_3707_, 1);
v___y_3680_ = v_a_3626_;
v___y_3681_ = v_a_3627_;
v___y_3682_ = v_a_3628_;
v___y_3683_ = v_a_3629_;
v___y_3684_ = v_a_3630_;
v___y_3685_ = v_a_3631_;
v___y_3686_ = v_a_3632_;
v___y_3687_ = v_a_3633_;
v___y_3688_ = v_a_3634_;
v___y_3689_ = v_a_3635_;
v___y_3690_ = v_a_3636_;
goto v___jp_3679_;
}
else
{
lean_dec_ref(v_he_3625_);
lean_dec_ref(v_e_3624_);
lean_dec_ref(v_c_3623_);
return v___x_3707_;
}
}
else
{
lean_object* v_a_3708_; lean_object* v___x_3710_; uint8_t v_isShared_3711_; uint8_t v_isSharedCheck_3715_; 
lean_dec_ref(v_he_3625_);
lean_dec_ref(v_e_3624_);
lean_dec_ref(v_c_3623_);
v_a_3708_ = lean_ctor_get(v___x_3705_, 0);
v_isSharedCheck_3715_ = !lean_is_exclusive(v___x_3705_);
if (v_isSharedCheck_3715_ == 0)
{
v___x_3710_ = v___x_3705_;
v_isShared_3711_ = v_isSharedCheck_3715_;
goto v_resetjp_3709_;
}
else
{
lean_inc(v_a_3708_);
lean_dec(v___x_3705_);
v___x_3710_ = lean_box(0);
v_isShared_3711_ = v_isSharedCheck_3715_;
goto v_resetjp_3709_;
}
v_resetjp_3709_:
{
lean_object* v___x_3713_; 
if (v_isShared_3711_ == 0)
{
v___x_3713_ = v___x_3710_;
goto v_reusejp_3712_;
}
else
{
lean_object* v_reuseFailAlloc_3714_; 
v_reuseFailAlloc_3714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3714_, 0, v_a_3708_);
v___x_3713_ = v_reuseFailAlloc_3714_;
goto v_reusejp_3712_;
}
v_reusejp_3712_:
{
return v___x_3713_;
}
}
}
}
}
v___jp_3638_:
{
lean_object* v___x_3655_; lean_object* v___x_3656_; 
v___x_3655_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3655_, 0, v___y_3651_);
lean_ctor_set_uint8(v___x_3655_, sizeof(void*)*1, v___y_3654_);
v___x_3656_ = l_Lean_Meta_Grind_Order_addEdge(v___y_3642_, v___y_3647_, v___x_3655_, v___y_3648_, v___y_3644_, v___y_3652_, v___y_3649_, v___y_3643_, v___y_3650_, v___y_3653_, v___y_3639_, v___y_3646_, v___y_3640_, v___y_3645_, v___y_3641_);
return v___x_3656_;
}
v___jp_3657_:
{
uint8_t v_kind_3670_; 
v_kind_3670_ = lean_ctor_get_uint8(v_c_3623_, sizeof(void*)*5);
if (v_kind_3670_ == 1)
{
lean_object* v_u_3671_; lean_object* v_v_3672_; lean_object* v_k_3673_; uint8_t v___x_3674_; 
v_u_3671_ = lean_ctor_get(v_c_3623_, 0);
lean_inc(v_u_3671_);
v_v_3672_ = lean_ctor_get(v_c_3623_, 1);
lean_inc(v_v_3672_);
v_k_3673_ = lean_ctor_get(v_c_3623_, 2);
lean_inc(v_k_3673_);
lean_dec_ref(v_c_3623_);
v___x_3674_ = 1;
v___y_3639_ = v___y_3665_;
v___y_3640_ = v___y_3667_;
v___y_3641_ = v___y_3669_;
v___y_3642_ = v_u_3671_;
v___y_3643_ = v___y_3662_;
v___y_3644_ = v___y_3659_;
v___y_3645_ = v___y_3668_;
v___y_3646_ = v___y_3666_;
v___y_3647_ = v_v_3672_;
v___y_3648_ = v_h_3658_;
v___y_3649_ = v___y_3661_;
v___y_3650_ = v___y_3663_;
v___y_3651_ = v_k_3673_;
v___y_3652_ = v___y_3660_;
v___y_3653_ = v___y_3664_;
v___y_3654_ = v___x_3674_;
goto v___jp_3638_;
}
else
{
lean_object* v_u_3675_; lean_object* v_v_3676_; lean_object* v_k_3677_; uint8_t v___x_3678_; 
v_u_3675_ = lean_ctor_get(v_c_3623_, 0);
lean_inc(v_u_3675_);
v_v_3676_ = lean_ctor_get(v_c_3623_, 1);
lean_inc(v_v_3676_);
v_k_3677_ = lean_ctor_get(v_c_3623_, 2);
lean_inc(v_k_3677_);
lean_dec_ref(v_c_3623_);
v___x_3678_ = 0;
v___y_3639_ = v___y_3665_;
v___y_3640_ = v___y_3667_;
v___y_3641_ = v___y_3669_;
v___y_3642_ = v_u_3675_;
v___y_3643_ = v___y_3662_;
v___y_3644_ = v___y_3659_;
v___y_3645_ = v___y_3668_;
v___y_3646_ = v___y_3666_;
v___y_3647_ = v_v_3676_;
v___y_3648_ = v_h_3658_;
v___y_3649_ = v___y_3661_;
v___y_3650_ = v___y_3663_;
v___y_3651_ = v_k_3677_;
v___y_3652_ = v___y_3660_;
v___y_3653_ = v___y_3664_;
v___y_3654_ = v___x_3678_;
goto v___jp_3638_;
}
}
v___jp_3679_:
{
lean_object* v_h_x3f_3691_; 
v_h_x3f_3691_ = lean_ctor_get(v_c_3623_, 4);
if (lean_obj_tag(v_h_x3f_3691_) == 1)
{
lean_object* v_e_3692_; lean_object* v_val_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; 
v_e_3692_ = lean_ctor_get(v_c_3623_, 3);
v_val_3693_ = lean_ctor_get(v_h_x3f_3691_, 0);
v___x_3694_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__2, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__2);
lean_inc_ref(v_e_3624_);
v___x_3695_ = l_Lean_Meta_mkOfEqTrueCore(v_e_3624_, v_he_3625_);
lean_inc(v_val_3693_);
lean_inc_ref(v_e_3692_);
v___x_3696_ = l_Lean_mkApp4(v___x_3694_, v_e_3624_, v_e_3692_, v_val_3693_, v___x_3695_);
v_h_3658_ = v___x_3696_;
v___y_3659_ = v___y_3680_;
v___y_3660_ = v___y_3681_;
v___y_3661_ = v___y_3682_;
v___y_3662_ = v___y_3683_;
v___y_3663_ = v___y_3684_;
v___y_3664_ = v___y_3685_;
v___y_3665_ = v___y_3686_;
v___y_3666_ = v___y_3687_;
v___y_3667_ = v___y_3688_;
v___y_3668_ = v___y_3689_;
v___y_3669_ = v___y_3690_;
goto v___jp_3657_;
}
else
{
lean_object* v___x_3697_; 
v___x_3697_ = l_Lean_Meta_mkOfEqTrueCore(v_e_3624_, v_he_3625_);
v_h_3658_ = v___x_3697_;
v___y_3659_ = v___y_3680_;
v___y_3660_ = v___y_3681_;
v___y_3661_ = v___y_3682_;
v___y_3662_ = v___y_3683_;
v___y_3663_ = v___y_3684_;
v___y_3664_ = v___y_3685_;
v___y_3665_ = v___y_3686_;
v___y_3666_ = v___y_3687_;
v___y_3667_ = v___y_3688_;
v___y_3668_ = v___y_3689_;
v___y_3669_ = v___y_3690_;
goto v___jp_3657_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___boxed(lean_object* v_c_3716_, lean_object* v_e_3717_, lean_object* v_he_3718_, lean_object* v_a_3719_, lean_object* v_a_3720_, lean_object* v_a_3721_, lean_object* v_a_3722_, lean_object* v_a_3723_, lean_object* v_a_3724_, lean_object* v_a_3725_, lean_object* v_a_3726_, lean_object* v_a_3727_, lean_object* v_a_3728_, lean_object* v_a_3729_, lean_object* v_a_3730_){
_start:
{
lean_object* v_res_3731_; 
v_res_3731_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue(v_c_3716_, v_e_3717_, v_he_3718_, v_a_3719_, v_a_3720_, v_a_3721_, v_a_3722_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_, v_a_3727_, v_a_3728_, v_a_3729_);
lean_dec(v_a_3729_);
lean_dec_ref(v_a_3728_);
lean_dec(v_a_3727_);
lean_dec_ref(v_a_3726_);
lean_dec(v_a_3725_);
lean_dec_ref(v_a_3724_);
lean_dec(v_a_3723_);
lean_dec_ref(v_a_3722_);
lean_dec(v_a_3721_);
lean_dec(v_a_3720_);
lean_dec(v_a_3719_);
return v_res_3731_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__2(void){
_start:
{
lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; 
v___x_3738_ = lean_box(0);
v___x_3739_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__1));
v___x_3740_ = l_Lean_mkConst(v___x_3739_, v___x_3738_);
return v___x_3740_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__3(void){
_start:
{
lean_object* v___x_3741_; lean_object* v___x_3742_; 
v___x_3741_ = lean_unsigned_to_nat(1u);
v___x_3742_ = lean_nat_to_int(v___x_3741_);
return v___x_3742_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4(void){
_start:
{
lean_object* v___x_3743_; lean_object* v___x_3744_; 
v___x_3743_ = lean_unsigned_to_nat(0u);
v___x_3744_ = lean_nat_to_int(v___x_3743_);
return v___x_3744_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__8(void){
_start:
{
lean_object* v___x_3750_; lean_object* v___x_3751_; 
v___x_3750_ = lean_unsigned_to_nat(0u);
v___x_3751_ = l_Lean_Level_ofNat(v___x_3750_);
return v___x_3751_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__9(void){
_start:
{
lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; 
v___x_3752_ = lean_box(0);
v___x_3753_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__8, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__8);
v___x_3754_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3754_, 0, v___x_3753_);
lean_ctor_set(v___x_3754_, 1, v___x_3752_);
return v___x_3754_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10(void){
_start:
{
lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; 
v___x_3755_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__9, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__9);
v___x_3756_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__7));
v___x_3757_ = l_Lean_Expr_const___override(v___x_3756_, v___x_3755_);
return v___x_3757_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13(void){
_start:
{
lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; 
v___x_3761_ = lean_box(0);
v___x_3762_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__12));
v___x_3763_ = l_Lean_Expr_const___override(v___x_3762_, v___x_3761_);
return v___x_3763_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16(void){
_start:
{
lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; 
v___x_3768_ = lean_box(0);
v___x_3769_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__15));
v___x_3770_ = l_Lean_Expr_const___override(v___x_3769_, v___x_3768_);
return v___x_3770_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__29(void){
_start:
{
lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; 
v___x_3807_ = lean_box(0);
v___x_3808_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__28));
v___x_3809_ = l_Lean_mkConst(v___x_3808_, v___x_3807_);
return v___x_3809_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__31(void){
_start:
{
lean_object* v___x_3811_; lean_object* v___x_3812_; 
v___x_3811_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__30));
v___x_3812_ = l_Lean_stringToMessageData(v___x_3811_);
return v___x_3812_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse(lean_object* v_c_3813_, lean_object* v_e_3814_, lean_object* v_he_3815_, lean_object* v_a_3816_, lean_object* v_a_3817_, lean_object* v_a_3818_, lean_object* v_a_3819_, lean_object* v_a_3820_, lean_object* v_a_3821_, lean_object* v_a_3822_, lean_object* v_a_3823_, lean_object* v_a_3824_, lean_object* v_a_3825_, lean_object* v_a_3826_){
_start:
{
lean_object* v___y_3829_; lean_object* v___y_3830_; lean_object* v_k_x27_3831_; lean_object* v_h_3832_; uint8_t v_strict_3833_; lean_object* v___y_3834_; lean_object* v___y_3835_; lean_object* v___y_3836_; lean_object* v___y_3837_; lean_object* v___y_3838_; lean_object* v___y_3839_; lean_object* v___y_3840_; lean_object* v___y_3841_; lean_object* v___y_3842_; lean_object* v___y_3843_; lean_object* v___y_3844_; lean_object* v___y_3848_; lean_object* v___y_3849_; lean_object* v___y_3850_; lean_object* v___y_3851_; lean_object* v___y_3852_; lean_object* v___y_3853_; lean_object* v___y_3854_; lean_object* v___y_3855_; lean_object* v___y_3856_; lean_object* v___y_3857_; lean_object* v___y_3858_; lean_object* v___y_3859_; lean_object* v___y_3860_; lean_object* v___y_3861_; lean_object* v___y_3862_; lean_object* v___y_3863_; lean_object* v___y_3864_; lean_object* v___y_3865_; lean_object* v___y_3866_; lean_object* v___y_3867_; lean_object* v___y_3868_; lean_object* v___y_3872_; lean_object* v___y_3873_; lean_object* v___y_3874_; lean_object* v___y_3875_; lean_object* v___y_3876_; lean_object* v___y_3877_; lean_object* v___y_3878_; lean_object* v___y_3879_; lean_object* v___y_3880_; lean_object* v___y_3881_; lean_object* v___y_3882_; lean_object* v___y_3883_; lean_object* v___y_3884_; lean_object* v___y_3885_; lean_object* v___y_3886_; lean_object* v___y_3887_; lean_object* v___y_3888_; uint8_t v___y_3889_; lean_object* v___x_3935_; 
v___x_3935_ = l_Lean_Meta_Grind_Order_isLinearPreorder(v_a_3816_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_, v_a_3821_, v_a_3822_, v_a_3823_, v_a_3824_, v_a_3825_, v_a_3826_);
if (lean_obj_tag(v___x_3935_) == 0)
{
lean_object* v_a_3936_; lean_object* v___x_3938_; uint8_t v_isShared_3939_; uint8_t v_isSharedCheck_4258_; 
v_a_3936_ = lean_ctor_get(v___x_3935_, 0);
v_isSharedCheck_4258_ = !lean_is_exclusive(v___x_3935_);
if (v_isSharedCheck_4258_ == 0)
{
v___x_3938_ = v___x_3935_;
v_isShared_3939_ = v_isSharedCheck_4258_;
goto v_resetjp_3937_;
}
else
{
lean_inc(v_a_3936_);
lean_dec(v___x_3935_);
v___x_3938_ = lean_box(0);
v_isShared_3939_ = v_isSharedCheck_4258_;
goto v_resetjp_3937_;
}
v_resetjp_3937_:
{
lean_object* v___y_3941_; lean_object* v___y_3942_; lean_object* v___y_3943_; lean_object* v___y_3944_; lean_object* v___y_3945_; lean_object* v___y_3946_; lean_object* v___y_3947_; lean_object* v___y_3948_; lean_object* v___y_3949_; lean_object* v___y_3950_; lean_object* v___y_3951_; lean_object* v___y_3952_; lean_object* v___y_3953_; uint8_t v___y_3954_; lean_object* v___y_3955_; lean_object* v___y_3956_; lean_object* v___y_3957_; lean_object* v___y_3958_; lean_object* v___y_3959_; lean_object* v___y_3960_; lean_object* v___y_3961_; lean_object* v___y_3967_; lean_object* v___y_3968_; lean_object* v___y_3969_; lean_object* v___y_3970_; lean_object* v___y_3971_; lean_object* v___y_3972_; lean_object* v___y_3973_; lean_object* v___y_3974_; lean_object* v___y_3975_; lean_object* v___y_3976_; lean_object* v___y_3977_; lean_object* v___y_3978_; uint8_t v___y_3979_; lean_object* v___y_3980_; lean_object* v___y_3981_; lean_object* v___y_3982_; lean_object* v___y_3983_; lean_object* v___y_3984_; lean_object* v___y_3985_; lean_object* v___y_3986_; lean_object* v___y_3999_; lean_object* v___y_4000_; lean_object* v___y_4001_; lean_object* v___y_4002_; lean_object* v___y_4003_; lean_object* v___y_4004_; lean_object* v___y_4005_; lean_object* v___y_4006_; lean_object* v___y_4007_; uint8_t v___y_4008_; lean_object* v___y_4009_; lean_object* v___y_4010_; lean_object* v___y_4011_; lean_object* v___y_4012_; lean_object* v___y_4013_; lean_object* v___y_4014_; lean_object* v___y_4015_; lean_object* v_h_4058_; lean_object* v___y_4059_; lean_object* v___y_4060_; lean_object* v___y_4061_; lean_object* v___y_4062_; lean_object* v___y_4063_; lean_object* v___y_4064_; lean_object* v___y_4065_; lean_object* v___y_4066_; lean_object* v___y_4067_; lean_object* v___y_4068_; lean_object* v___y_4069_; lean_object* v___y_4215_; lean_object* v___y_4216_; lean_object* v___y_4217_; lean_object* v___y_4218_; lean_object* v___y_4219_; lean_object* v___y_4220_; lean_object* v___y_4221_; lean_object* v___y_4222_; lean_object* v___y_4223_; lean_object* v___y_4224_; lean_object* v___y_4225_; uint8_t v___x_4233_; 
v___x_4233_ = lean_unbox(v_a_3936_);
if (v___x_4233_ == 0)
{
lean_object* v___x_4234_; lean_object* v___x_4236_; 
lean_dec(v_a_3936_);
lean_dec_ref(v_he_3815_);
lean_dec_ref(v_e_3814_);
lean_dec_ref(v_c_3813_);
v___x_4234_ = lean_box(0);
if (v_isShared_3939_ == 0)
{
lean_ctor_set(v___x_3938_, 0, v___x_4234_);
v___x_4236_ = v___x_3938_;
goto v_reusejp_4235_;
}
else
{
lean_object* v_reuseFailAlloc_4237_; 
v_reuseFailAlloc_4237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4237_, 0, v___x_4234_);
v___x_4236_ = v_reuseFailAlloc_4237_;
goto v_reusejp_4235_;
}
v_reusejp_4235_:
{
return v___x_4236_;
}
}
else
{
lean_object* v_toCold_4238_; lean_object* v_options_4239_; uint8_t v_hasTrace_4240_; 
lean_del_object(v___x_3938_);
v_toCold_4238_ = lean_ctor_get(v_a_3825_, 0);
v_options_4239_ = lean_ctor_get(v_toCold_4238_, 2);
v_hasTrace_4240_ = lean_ctor_get_uint8(v_options_4239_, sizeof(void*)*1);
if (v_hasTrace_4240_ == 0)
{
v___y_4215_ = v_a_3816_;
v___y_4216_ = v_a_3817_;
v___y_4217_ = v_a_3818_;
v___y_4218_ = v_a_3819_;
v___y_4219_ = v_a_3820_;
v___y_4220_ = v_a_3821_;
v___y_4221_ = v_a_3822_;
v___y_4222_ = v_a_3823_;
v___y_4223_ = v_a_3824_;
v___y_4224_ = v_a_3825_;
v___y_4225_ = v_a_3826_;
goto v___jp_4214_;
}
else
{
lean_object* v_inheritedTraceOptions_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; uint8_t v___x_4244_; 
v_inheritedTraceOptions_4241_ = lean_ctor_get(v_toCold_4238_, 11);
v___x_4242_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__4));
v___x_4243_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5);
v___x_4244_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4241_, v_options_4239_, v___x_4243_);
if (v___x_4244_ == 0)
{
v___y_4215_ = v_a_3816_;
v___y_4216_ = v_a_3817_;
v___y_4217_ = v_a_3818_;
v___y_4218_ = v_a_3819_;
v___y_4219_ = v_a_3820_;
v___y_4220_ = v_a_3821_;
v___y_4221_ = v_a_3822_;
v___y_4222_ = v_a_3823_;
v___y_4223_ = v_a_3824_;
v___y_4224_ = v_a_3825_;
v___y_4225_ = v_a_3826_;
goto v___jp_4214_;
}
else
{
lean_object* v___x_4245_; 
v___x_4245_ = l_Lean_Meta_Grind_Order_Cnstr_pp___redArg(v_c_3813_, v_a_3816_, v_a_3817_, v_a_3825_);
if (lean_obj_tag(v___x_4245_) == 0)
{
lean_object* v_a_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; 
v_a_4246_ = lean_ctor_get(v___x_4245_, 0);
lean_inc(v_a_4246_);
lean_dec_ref_known(v___x_4245_, 1);
v___x_4247_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__31, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__31_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__31);
v___x_4248_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4248_, 0, v___x_4247_);
lean_ctor_set(v___x_4248_, 1, v_a_4246_);
v___x_4249_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(v___x_4242_, v___x_4248_, v_a_3823_, v_a_3824_, v_a_3825_, v_a_3826_);
if (lean_obj_tag(v___x_4249_) == 0)
{
lean_dec_ref_known(v___x_4249_, 1);
v___y_4215_ = v_a_3816_;
v___y_4216_ = v_a_3817_;
v___y_4217_ = v_a_3818_;
v___y_4218_ = v_a_3819_;
v___y_4219_ = v_a_3820_;
v___y_4220_ = v_a_3821_;
v___y_4221_ = v_a_3822_;
v___y_4222_ = v_a_3823_;
v___y_4223_ = v_a_3824_;
v___y_4224_ = v_a_3825_;
v___y_4225_ = v_a_3826_;
goto v___jp_4214_;
}
else
{
lean_dec(v_a_3936_);
lean_dec_ref(v_he_3815_);
lean_dec_ref(v_e_3814_);
lean_dec_ref(v_c_3813_);
return v___x_4249_;
}
}
else
{
lean_object* v_a_4250_; lean_object* v___x_4252_; uint8_t v_isShared_4253_; uint8_t v_isSharedCheck_4257_; 
lean_dec(v_a_3936_);
lean_dec_ref(v_he_3815_);
lean_dec_ref(v_e_3814_);
lean_dec_ref(v_c_3813_);
v_a_4250_ = lean_ctor_get(v___x_4245_, 0);
v_isSharedCheck_4257_ = !lean_is_exclusive(v___x_4245_);
if (v_isSharedCheck_4257_ == 0)
{
v___x_4252_ = v___x_4245_;
v_isShared_4253_ = v_isSharedCheck_4257_;
goto v_resetjp_4251_;
}
else
{
lean_inc(v_a_4250_);
lean_dec(v___x_4245_);
v___x_4252_ = lean_box(0);
v_isShared_4253_ = v_isSharedCheck_4257_;
goto v_resetjp_4251_;
}
v_resetjp_4251_:
{
lean_object* v___x_4255_; 
if (v_isShared_4253_ == 0)
{
v___x_4255_ = v___x_4252_;
goto v_reusejp_4254_;
}
else
{
lean_object* v_reuseFailAlloc_4256_; 
v_reuseFailAlloc_4256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4256_, 0, v_a_4250_);
v___x_4255_ = v_reuseFailAlloc_4256_;
goto v_reusejp_4254_;
}
v_reusejp_4254_:
{
return v___x_4255_;
}
}
}
}
}
}
v___jp_3940_:
{
lean_object* v___x_3962_; lean_object* v___x_3963_; 
v___x_3962_ = l_Lean_eagerReflBoolTrue;
lean_inc_ref(v___y_3961_);
v___x_3963_ = l_Lean_mkApp6(v___y_3956_, v___y_3949_, v___y_3950_, v___y_3945_, v___y_3961_, v___x_3962_, v___y_3958_);
if (v___y_3954_ == 0)
{
uint8_t v___x_3964_; 
v___x_3964_ = lean_unbox(v_a_3936_);
lean_dec(v_a_3936_);
v___y_3872_ = v___y_3941_;
v___y_3873_ = v___y_3942_;
v___y_3874_ = v___y_3943_;
v___y_3875_ = v___y_3944_;
v___y_3876_ = v___y_3946_;
v___y_3877_ = v___y_3947_;
v___y_3878_ = v___y_3948_;
v___y_3879_ = v___y_3961_;
v___y_3880_ = v___x_3962_;
v___y_3881_ = v___x_3963_;
v___y_3882_ = v___y_3951_;
v___y_3883_ = v___y_3952_;
v___y_3884_ = v___y_3953_;
v___y_3885_ = v___y_3955_;
v___y_3886_ = v___y_3957_;
v___y_3887_ = v___y_3959_;
v___y_3888_ = v___y_3960_;
v___y_3889_ = v___x_3964_;
goto v___jp_3871_;
}
else
{
uint8_t v___x_3965_; 
lean_dec(v_a_3936_);
v___x_3965_ = 0;
v___y_3872_ = v___y_3941_;
v___y_3873_ = v___y_3942_;
v___y_3874_ = v___y_3943_;
v___y_3875_ = v___y_3944_;
v___y_3876_ = v___y_3946_;
v___y_3877_ = v___y_3947_;
v___y_3878_ = v___y_3948_;
v___y_3879_ = v___y_3961_;
v___y_3880_ = v___x_3962_;
v___y_3881_ = v___x_3963_;
v___y_3882_ = v___y_3951_;
v___y_3883_ = v___y_3952_;
v___y_3884_ = v___y_3953_;
v___y_3885_ = v___y_3955_;
v___y_3886_ = v___y_3957_;
v___y_3887_ = v___y_3959_;
v___y_3888_ = v___y_3960_;
v___y_3889_ = v___x_3965_;
goto v___jp_3871_;
}
}
v___jp_3966_:
{
lean_object* v___x_3987_; uint8_t v___x_3988_; 
v___x_3987_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4);
v___x_3988_ = lean_int_dec_le(v___x_3987_, v___y_3969_);
if (v___x_3988_ == 0)
{
lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; 
v___x_3989_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10);
v___x_3990_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13);
v___x_3991_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16);
v___x_3992_ = lean_int_neg(v___y_3969_);
v___x_3993_ = l_Int_toNat(v___x_3992_);
lean_dec(v___x_3992_);
v___x_3994_ = l_Lean_instToExprInt_mkNat(v___x_3993_);
v___x_3995_ = l_Lean_mkApp3(v___x_3989_, v___x_3990_, v___x_3991_, v___x_3994_);
v___y_3941_ = v___y_3967_;
v___y_3942_ = v___y_3968_;
v___y_3943_ = v___y_3969_;
v___y_3944_ = v___y_3970_;
v___y_3945_ = v___y_3986_;
v___y_3946_ = v___y_3971_;
v___y_3947_ = v___y_3972_;
v___y_3948_ = v___y_3973_;
v___y_3949_ = v___y_3974_;
v___y_3950_ = v___y_3975_;
v___y_3951_ = v___y_3976_;
v___y_3952_ = v___y_3977_;
v___y_3953_ = v___y_3978_;
v___y_3954_ = v___y_3979_;
v___y_3955_ = v___y_3981_;
v___y_3956_ = v___y_3980_;
v___y_3957_ = v___y_3983_;
v___y_3958_ = v___y_3982_;
v___y_3959_ = v___y_3984_;
v___y_3960_ = v___y_3985_;
v___y_3961_ = v___x_3995_;
goto v___jp_3940_;
}
else
{
lean_object* v___x_3996_; lean_object* v___x_3997_; 
v___x_3996_ = l_Int_toNat(v___y_3969_);
v___x_3997_ = l_Lean_instToExprInt_mkNat(v___x_3996_);
v___y_3941_ = v___y_3967_;
v___y_3942_ = v___y_3968_;
v___y_3943_ = v___y_3969_;
v___y_3944_ = v___y_3970_;
v___y_3945_ = v___y_3986_;
v___y_3946_ = v___y_3971_;
v___y_3947_ = v___y_3972_;
v___y_3948_ = v___y_3973_;
v___y_3949_ = v___y_3974_;
v___y_3950_ = v___y_3975_;
v___y_3951_ = v___y_3976_;
v___y_3952_ = v___y_3977_;
v___y_3953_ = v___y_3978_;
v___y_3954_ = v___y_3979_;
v___y_3955_ = v___y_3981_;
v___y_3956_ = v___y_3980_;
v___y_3957_ = v___y_3983_;
v___y_3958_ = v___y_3982_;
v___y_3959_ = v___y_3984_;
v___y_3960_ = v___y_3985_;
v___y_3961_ = v___x_3997_;
goto v___jp_3940_;
}
}
v___jp_3998_:
{
lean_object* v___x_4016_; 
lean_inc(v___y_4015_);
v___x_4016_ = l_Lean_Meta_Grind_Order_mkLinearOrdRingPrefix(v___y_4015_, v___y_4004_, v___y_4003_, v___y_4014_, v___y_4010_, v___y_4013_, v___y_4007_, v___y_4005_, v___y_4002_, v___y_4000_, v___y_4012_, v___y_4001_);
if (lean_obj_tag(v___x_4016_) == 0)
{
lean_object* v_a_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; 
v_a_4017_ = lean_ctor_get(v___x_4016_, 0);
lean_inc(v_a_4017_);
lean_dec_ref_known(v___x_4016_, 1);
v___x_4018_ = lean_int_neg(v___y_4009_);
v___x_4019_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v___y_3999_, v___y_4004_, v___y_4003_, v___y_4012_);
if (lean_obj_tag(v___x_4019_) == 0)
{
lean_object* v_a_4020_; lean_object* v___x_4021_; 
v_a_4020_ = lean_ctor_get(v___x_4019_, 0);
lean_inc(v_a_4020_);
lean_dec_ref_known(v___x_4019_, 1);
v___x_4021_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v___y_4006_, v___y_4004_, v___y_4003_, v___y_4012_);
if (lean_obj_tag(v___x_4021_) == 0)
{
lean_object* v_a_4022_; lean_object* v___x_4023_; uint8_t v___x_4024_; 
v_a_4022_ = lean_ctor_get(v___x_4021_, 0);
lean_inc(v_a_4022_);
lean_dec_ref_known(v___x_4021_, 1);
v___x_4023_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4);
v___x_4024_ = lean_int_dec_le(v___x_4023_, v___y_4009_);
if (v___x_4024_ == 0)
{
lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; 
lean_dec(v___y_4009_);
v___x_4025_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10);
v___x_4026_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13);
v___x_4027_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16);
v___x_4028_ = l_Int_toNat(v___x_4018_);
v___x_4029_ = l_Lean_instToExprInt_mkNat(v___x_4028_);
v___x_4030_ = l_Lean_mkApp3(v___x_4025_, v___x_4026_, v___x_4027_, v___x_4029_);
v___y_3967_ = v___y_3999_;
v___y_3968_ = v___y_4000_;
v___y_3969_ = v___x_4018_;
v___y_3970_ = v___y_4001_;
v___y_3971_ = v___y_4002_;
v___y_3972_ = v___y_4003_;
v___y_3973_ = v___y_4004_;
v___y_3974_ = v_a_4020_;
v___y_3975_ = v_a_4022_;
v___y_3976_ = v___y_4005_;
v___y_3977_ = v___y_4006_;
v___y_3978_ = v___y_4007_;
v___y_3979_ = v___y_4008_;
v___y_3980_ = v_a_4017_;
v___y_3981_ = v___y_4010_;
v___y_3982_ = v___y_4011_;
v___y_3983_ = v___y_4012_;
v___y_3984_ = v___y_4013_;
v___y_3985_ = v___y_4014_;
v___y_3986_ = v___x_4030_;
goto v___jp_3966_;
}
else
{
lean_object* v___x_4031_; lean_object* v___x_4032_; 
v___x_4031_ = l_Int_toNat(v___y_4009_);
lean_dec(v___y_4009_);
v___x_4032_ = l_Lean_instToExprInt_mkNat(v___x_4031_);
v___y_3967_ = v___y_3999_;
v___y_3968_ = v___y_4000_;
v___y_3969_ = v___x_4018_;
v___y_3970_ = v___y_4001_;
v___y_3971_ = v___y_4002_;
v___y_3972_ = v___y_4003_;
v___y_3973_ = v___y_4004_;
v___y_3974_ = v_a_4020_;
v___y_3975_ = v_a_4022_;
v___y_3976_ = v___y_4005_;
v___y_3977_ = v___y_4006_;
v___y_3978_ = v___y_4007_;
v___y_3979_ = v___y_4008_;
v___y_3980_ = v_a_4017_;
v___y_3981_ = v___y_4010_;
v___y_3982_ = v___y_4011_;
v___y_3983_ = v___y_4012_;
v___y_3984_ = v___y_4013_;
v___y_3985_ = v___y_4014_;
v___y_3986_ = v___x_4032_;
goto v___jp_3966_;
}
}
else
{
lean_object* v_a_4033_; lean_object* v___x_4035_; uint8_t v_isShared_4036_; uint8_t v_isSharedCheck_4040_; 
lean_dec(v_a_4020_);
lean_dec(v___x_4018_);
lean_dec(v_a_4017_);
lean_dec_ref(v___y_4011_);
lean_dec(v___y_4009_);
lean_dec(v___y_4006_);
lean_dec(v___y_3999_);
lean_dec(v_a_3936_);
v_a_4033_ = lean_ctor_get(v___x_4021_, 0);
v_isSharedCheck_4040_ = !lean_is_exclusive(v___x_4021_);
if (v_isSharedCheck_4040_ == 0)
{
v___x_4035_ = v___x_4021_;
v_isShared_4036_ = v_isSharedCheck_4040_;
goto v_resetjp_4034_;
}
else
{
lean_inc(v_a_4033_);
lean_dec(v___x_4021_);
v___x_4035_ = lean_box(0);
v_isShared_4036_ = v_isSharedCheck_4040_;
goto v_resetjp_4034_;
}
v_resetjp_4034_:
{
lean_object* v___x_4038_; 
if (v_isShared_4036_ == 0)
{
v___x_4038_ = v___x_4035_;
goto v_reusejp_4037_;
}
else
{
lean_object* v_reuseFailAlloc_4039_; 
v_reuseFailAlloc_4039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4039_, 0, v_a_4033_);
v___x_4038_ = v_reuseFailAlloc_4039_;
goto v_reusejp_4037_;
}
v_reusejp_4037_:
{
return v___x_4038_;
}
}
}
}
else
{
lean_object* v_a_4041_; lean_object* v___x_4043_; uint8_t v_isShared_4044_; uint8_t v_isSharedCheck_4048_; 
lean_dec(v___x_4018_);
lean_dec(v_a_4017_);
lean_dec_ref(v___y_4011_);
lean_dec(v___y_4009_);
lean_dec(v___y_4006_);
lean_dec(v___y_3999_);
lean_dec(v_a_3936_);
v_a_4041_ = lean_ctor_get(v___x_4019_, 0);
v_isSharedCheck_4048_ = !lean_is_exclusive(v___x_4019_);
if (v_isSharedCheck_4048_ == 0)
{
v___x_4043_ = v___x_4019_;
v_isShared_4044_ = v_isSharedCheck_4048_;
goto v_resetjp_4042_;
}
else
{
lean_inc(v_a_4041_);
lean_dec(v___x_4019_);
v___x_4043_ = lean_box(0);
v_isShared_4044_ = v_isSharedCheck_4048_;
goto v_resetjp_4042_;
}
v_resetjp_4042_:
{
lean_object* v___x_4046_; 
if (v_isShared_4044_ == 0)
{
v___x_4046_ = v___x_4043_;
goto v_reusejp_4045_;
}
else
{
lean_object* v_reuseFailAlloc_4047_; 
v_reuseFailAlloc_4047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4047_, 0, v_a_4041_);
v___x_4046_ = v_reuseFailAlloc_4047_;
goto v_reusejp_4045_;
}
v_reusejp_4045_:
{
return v___x_4046_;
}
}
}
}
else
{
lean_object* v_a_4049_; lean_object* v___x_4051_; uint8_t v_isShared_4052_; uint8_t v_isSharedCheck_4056_; 
lean_dec_ref(v___y_4011_);
lean_dec(v___y_4009_);
lean_dec(v___y_4006_);
lean_dec(v___y_3999_);
lean_dec(v_a_3936_);
v_a_4049_ = lean_ctor_get(v___x_4016_, 0);
v_isSharedCheck_4056_ = !lean_is_exclusive(v___x_4016_);
if (v_isSharedCheck_4056_ == 0)
{
v___x_4051_ = v___x_4016_;
v_isShared_4052_ = v_isSharedCheck_4056_;
goto v_resetjp_4050_;
}
else
{
lean_inc(v_a_4049_);
lean_dec(v___x_4016_);
v___x_4051_ = lean_box(0);
v_isShared_4052_ = v_isSharedCheck_4056_;
goto v_resetjp_4050_;
}
v_resetjp_4050_:
{
lean_object* v___x_4054_; 
if (v_isShared_4052_ == 0)
{
v___x_4054_ = v___x_4051_;
goto v_reusejp_4053_;
}
else
{
lean_object* v_reuseFailAlloc_4055_; 
v_reuseFailAlloc_4055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4055_, 0, v_a_4049_);
v___x_4054_ = v_reuseFailAlloc_4055_;
goto v_reusejp_4053_;
}
v_reusejp_4053_:
{
return v___x_4054_;
}
}
}
}
v___jp_4057_:
{
lean_object* v___x_4070_; 
v___x_4070_ = l_Lean_Meta_Grind_Order_isRing(v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_, v___y_4067_, v___y_4068_, v___y_4069_);
if (lean_obj_tag(v___x_4070_) == 0)
{
lean_object* v_a_4071_; uint8_t v___x_4072_; 
v_a_4071_ = lean_ctor_get(v___x_4070_, 0);
lean_inc(v_a_4071_);
lean_dec_ref_known(v___x_4070_, 1);
v___x_4072_ = lean_unbox(v_a_4071_);
if (v___x_4072_ == 0)
{
uint8_t v_kind_4073_; 
v_kind_4073_ = lean_ctor_get_uint8(v_c_3813_, sizeof(void*)*5);
if (v_kind_4073_ == 1)
{
lean_object* v_u_4074_; lean_object* v_v_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; 
lean_dec(v_a_3936_);
v_u_4074_ = lean_ctor_get(v_c_3813_, 0);
lean_inc(v_u_4074_);
v_v_4075_ = lean_ctor_get(v_c_3813_, 1);
lean_inc(v_v_4075_);
lean_dec_ref(v_c_3813_);
v___x_4076_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__18));
v___x_4077_ = l_Lean_Meta_Grind_Order_mkLeLtLinearPrefix(v___x_4076_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_, v___y_4067_, v___y_4068_, v___y_4069_);
if (lean_obj_tag(v___x_4077_) == 0)
{
lean_object* v_a_4078_; lean_object* v___x_4079_; 
v_a_4078_ = lean_ctor_get(v___x_4077_, 0);
lean_inc(v_a_4078_);
lean_dec_ref_known(v___x_4077_, 1);
v___x_4079_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_u_4074_, v___y_4059_, v___y_4060_, v___y_4068_);
if (lean_obj_tag(v___x_4079_) == 0)
{
lean_object* v_a_4080_; lean_object* v___x_4081_; 
v_a_4080_ = lean_ctor_get(v___x_4079_, 0);
lean_inc(v_a_4080_);
lean_dec_ref_known(v___x_4079_, 1);
v___x_4081_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_v_4075_, v___y_4059_, v___y_4060_, v___y_4068_);
if (lean_obj_tag(v___x_4081_) == 0)
{
lean_object* v_a_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; uint8_t v___x_4086_; lean_object* v___x_4087_; 
v_a_4082_ = lean_ctor_get(v___x_4081_, 0);
lean_inc(v_a_4082_);
lean_dec_ref_known(v___x_4081_, 1);
v___x_4083_ = l_Lean_mkApp3(v_a_4078_, v_a_4080_, v_a_4082_, v_h_4058_);
v___x_4084_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4);
v___x_4085_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4085_, 0, v___x_4084_);
v___x_4086_ = lean_unbox(v_a_4071_);
lean_dec(v_a_4071_);
lean_ctor_set_uint8(v___x_4085_, sizeof(void*)*1, v___x_4086_);
v___x_4087_ = l_Lean_Meta_Grind_Order_addEdge(v_v_4075_, v_u_4074_, v___x_4085_, v___x_4083_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_, v___y_4067_, v___y_4068_, v___y_4069_);
return v___x_4087_;
}
else
{
lean_object* v_a_4088_; lean_object* v___x_4090_; uint8_t v_isShared_4091_; uint8_t v_isSharedCheck_4095_; 
lean_dec(v_a_4080_);
lean_dec(v_a_4078_);
lean_dec(v_v_4075_);
lean_dec(v_u_4074_);
lean_dec(v_a_4071_);
lean_dec_ref(v_h_4058_);
v_a_4088_ = lean_ctor_get(v___x_4081_, 0);
v_isSharedCheck_4095_ = !lean_is_exclusive(v___x_4081_);
if (v_isSharedCheck_4095_ == 0)
{
v___x_4090_ = v___x_4081_;
v_isShared_4091_ = v_isSharedCheck_4095_;
goto v_resetjp_4089_;
}
else
{
lean_inc(v_a_4088_);
lean_dec(v___x_4081_);
v___x_4090_ = lean_box(0);
v_isShared_4091_ = v_isSharedCheck_4095_;
goto v_resetjp_4089_;
}
v_resetjp_4089_:
{
lean_object* v___x_4093_; 
if (v_isShared_4091_ == 0)
{
v___x_4093_ = v___x_4090_;
goto v_reusejp_4092_;
}
else
{
lean_object* v_reuseFailAlloc_4094_; 
v_reuseFailAlloc_4094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4094_, 0, v_a_4088_);
v___x_4093_ = v_reuseFailAlloc_4094_;
goto v_reusejp_4092_;
}
v_reusejp_4092_:
{
return v___x_4093_;
}
}
}
}
else
{
lean_object* v_a_4096_; lean_object* v___x_4098_; uint8_t v_isShared_4099_; uint8_t v_isSharedCheck_4103_; 
lean_dec(v_a_4078_);
lean_dec(v_v_4075_);
lean_dec(v_u_4074_);
lean_dec(v_a_4071_);
lean_dec_ref(v_h_4058_);
v_a_4096_ = lean_ctor_get(v___x_4079_, 0);
v_isSharedCheck_4103_ = !lean_is_exclusive(v___x_4079_);
if (v_isSharedCheck_4103_ == 0)
{
v___x_4098_ = v___x_4079_;
v_isShared_4099_ = v_isSharedCheck_4103_;
goto v_resetjp_4097_;
}
else
{
lean_inc(v_a_4096_);
lean_dec(v___x_4079_);
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
lean_dec(v_v_4075_);
lean_dec(v_u_4074_);
lean_dec(v_a_4071_);
lean_dec_ref(v_h_4058_);
v_a_4104_ = lean_ctor_get(v___x_4077_, 0);
v_isSharedCheck_4111_ = !lean_is_exclusive(v___x_4077_);
if (v_isSharedCheck_4111_ == 0)
{
v___x_4106_ = v___x_4077_;
v_isShared_4107_ = v_isSharedCheck_4111_;
goto v_resetjp_4105_;
}
else
{
lean_inc(v_a_4104_);
lean_dec(v___x_4077_);
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
lean_object* v_u_4112_; lean_object* v_v_4113_; lean_object* v___x_4114_; 
lean_dec(v_a_4071_);
v_u_4112_ = lean_ctor_get(v_c_3813_, 0);
lean_inc(v_u_4112_);
v_v_4113_ = lean_ctor_get(v_c_3813_, 1);
lean_inc(v_v_4113_);
lean_dec_ref(v_c_3813_);
v___x_4114_ = l_Lean_Meta_Grind_Order_hasLt(v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_, v___y_4067_, v___y_4068_, v___y_4069_);
if (lean_obj_tag(v___x_4114_) == 0)
{
lean_object* v_a_4115_; uint8_t v___x_4116_; 
v_a_4115_ = lean_ctor_get(v___x_4114_, 0);
lean_inc(v_a_4115_);
lean_dec_ref_known(v___x_4114_, 1);
v___x_4116_ = lean_unbox(v_a_4115_);
if (v___x_4116_ == 0)
{
lean_object* v___x_4117_; lean_object* v___x_4118_; 
lean_dec(v_a_3936_);
v___x_4117_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__20));
v___x_4118_ = l_Lean_Meta_Grind_Order_mkLeLinearPrefix(v___x_4117_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_, v___y_4067_, v___y_4068_, v___y_4069_);
if (lean_obj_tag(v___x_4118_) == 0)
{
lean_object* v_a_4119_; lean_object* v___x_4120_; 
v_a_4119_ = lean_ctor_get(v___x_4118_, 0);
lean_inc(v_a_4119_);
lean_dec_ref_known(v___x_4118_, 1);
v___x_4120_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_u_4112_, v___y_4059_, v___y_4060_, v___y_4068_);
if (lean_obj_tag(v___x_4120_) == 0)
{
lean_object* v_a_4121_; lean_object* v___x_4122_; 
v_a_4121_ = lean_ctor_get(v___x_4120_, 0);
lean_inc(v_a_4121_);
lean_dec_ref_known(v___x_4120_, 1);
v___x_4122_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_v_4113_, v___y_4059_, v___y_4060_, v___y_4068_);
if (lean_obj_tag(v___x_4122_) == 0)
{
lean_object* v_a_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; uint8_t v___x_4127_; lean_object* v___x_4128_; 
v_a_4123_ = lean_ctor_get(v___x_4122_, 0);
lean_inc(v_a_4123_);
lean_dec_ref_known(v___x_4122_, 1);
v___x_4124_ = l_Lean_mkApp3(v_a_4119_, v_a_4121_, v_a_4123_, v_h_4058_);
v___x_4125_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4);
v___x_4126_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4126_, 0, v___x_4125_);
v___x_4127_ = lean_unbox(v_a_4115_);
lean_dec(v_a_4115_);
lean_ctor_set_uint8(v___x_4126_, sizeof(void*)*1, v___x_4127_);
v___x_4128_ = l_Lean_Meta_Grind_Order_addEdge(v_v_4113_, v_u_4112_, v___x_4126_, v___x_4124_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_, v___y_4067_, v___y_4068_, v___y_4069_);
return v___x_4128_;
}
else
{
lean_object* v_a_4129_; lean_object* v___x_4131_; uint8_t v_isShared_4132_; uint8_t v_isSharedCheck_4136_; 
lean_dec(v_a_4121_);
lean_dec(v_a_4119_);
lean_dec(v_a_4115_);
lean_dec(v_v_4113_);
lean_dec(v_u_4112_);
lean_dec_ref(v_h_4058_);
v_a_4129_ = lean_ctor_get(v___x_4122_, 0);
v_isSharedCheck_4136_ = !lean_is_exclusive(v___x_4122_);
if (v_isSharedCheck_4136_ == 0)
{
v___x_4131_ = v___x_4122_;
v_isShared_4132_ = v_isSharedCheck_4136_;
goto v_resetjp_4130_;
}
else
{
lean_inc(v_a_4129_);
lean_dec(v___x_4122_);
v___x_4131_ = lean_box(0);
v_isShared_4132_ = v_isSharedCheck_4136_;
goto v_resetjp_4130_;
}
v_resetjp_4130_:
{
lean_object* v___x_4134_; 
if (v_isShared_4132_ == 0)
{
v___x_4134_ = v___x_4131_;
goto v_reusejp_4133_;
}
else
{
lean_object* v_reuseFailAlloc_4135_; 
v_reuseFailAlloc_4135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4135_, 0, v_a_4129_);
v___x_4134_ = v_reuseFailAlloc_4135_;
goto v_reusejp_4133_;
}
v_reusejp_4133_:
{
return v___x_4134_;
}
}
}
}
else
{
lean_object* v_a_4137_; lean_object* v___x_4139_; uint8_t v_isShared_4140_; uint8_t v_isSharedCheck_4144_; 
lean_dec(v_a_4119_);
lean_dec(v_a_4115_);
lean_dec(v_v_4113_);
lean_dec(v_u_4112_);
lean_dec_ref(v_h_4058_);
v_a_4137_ = lean_ctor_get(v___x_4120_, 0);
v_isSharedCheck_4144_ = !lean_is_exclusive(v___x_4120_);
if (v_isSharedCheck_4144_ == 0)
{
v___x_4139_ = v___x_4120_;
v_isShared_4140_ = v_isSharedCheck_4144_;
goto v_resetjp_4138_;
}
else
{
lean_inc(v_a_4137_);
lean_dec(v___x_4120_);
v___x_4139_ = lean_box(0);
v_isShared_4140_ = v_isSharedCheck_4144_;
goto v_resetjp_4138_;
}
v_resetjp_4138_:
{
lean_object* v___x_4142_; 
if (v_isShared_4140_ == 0)
{
v___x_4142_ = v___x_4139_;
goto v_reusejp_4141_;
}
else
{
lean_object* v_reuseFailAlloc_4143_; 
v_reuseFailAlloc_4143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4143_, 0, v_a_4137_);
v___x_4142_ = v_reuseFailAlloc_4143_;
goto v_reusejp_4141_;
}
v_reusejp_4141_:
{
return v___x_4142_;
}
}
}
}
else
{
lean_object* v_a_4145_; lean_object* v___x_4147_; uint8_t v_isShared_4148_; uint8_t v_isSharedCheck_4152_; 
lean_dec(v_a_4115_);
lean_dec(v_v_4113_);
lean_dec(v_u_4112_);
lean_dec_ref(v_h_4058_);
v_a_4145_ = lean_ctor_get(v___x_4118_, 0);
v_isSharedCheck_4152_ = !lean_is_exclusive(v___x_4118_);
if (v_isSharedCheck_4152_ == 0)
{
v___x_4147_ = v___x_4118_;
v_isShared_4148_ = v_isSharedCheck_4152_;
goto v_resetjp_4146_;
}
else
{
lean_inc(v_a_4145_);
lean_dec(v___x_4118_);
v___x_4147_ = lean_box(0);
v_isShared_4148_ = v_isSharedCheck_4152_;
goto v_resetjp_4146_;
}
v_resetjp_4146_:
{
lean_object* v___x_4150_; 
if (v_isShared_4148_ == 0)
{
v___x_4150_ = v___x_4147_;
goto v_reusejp_4149_;
}
else
{
lean_object* v_reuseFailAlloc_4151_; 
v_reuseFailAlloc_4151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4151_, 0, v_a_4145_);
v___x_4150_ = v_reuseFailAlloc_4151_;
goto v_reusejp_4149_;
}
v_reusejp_4149_:
{
return v___x_4150_;
}
}
}
}
else
{
lean_object* v___x_4153_; lean_object* v___x_4154_; 
lean_dec(v_a_4115_);
v___x_4153_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__22));
v___x_4154_ = l_Lean_Meta_Grind_Order_mkLeLtLinearPrefix(v___x_4153_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_, v___y_4067_, v___y_4068_, v___y_4069_);
if (lean_obj_tag(v___x_4154_) == 0)
{
lean_object* v_a_4155_; lean_object* v___x_4156_; 
v_a_4155_ = lean_ctor_get(v___x_4154_, 0);
lean_inc(v_a_4155_);
lean_dec_ref_known(v___x_4154_, 1);
v___x_4156_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_u_4112_, v___y_4059_, v___y_4060_, v___y_4068_);
if (lean_obj_tag(v___x_4156_) == 0)
{
lean_object* v_a_4157_; lean_object* v___x_4158_; 
v_a_4157_ = lean_ctor_get(v___x_4156_, 0);
lean_inc(v_a_4157_);
lean_dec_ref_known(v___x_4156_, 1);
v___x_4158_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v_v_4113_, v___y_4059_, v___y_4060_, v___y_4068_);
if (lean_obj_tag(v___x_4158_) == 0)
{
lean_object* v_a_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; uint8_t v___x_4163_; lean_object* v___x_4164_; 
v_a_4159_ = lean_ctor_get(v___x_4158_, 0);
lean_inc(v_a_4159_);
lean_dec_ref_known(v___x_4158_, 1);
v___x_4160_ = l_Lean_mkApp3(v_a_4155_, v_a_4157_, v_a_4159_, v_h_4058_);
v___x_4161_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4);
v___x_4162_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4162_, 0, v___x_4161_);
v___x_4163_ = lean_unbox(v_a_3936_);
lean_dec(v_a_3936_);
lean_ctor_set_uint8(v___x_4162_, sizeof(void*)*1, v___x_4163_);
v___x_4164_ = l_Lean_Meta_Grind_Order_addEdge(v_v_4113_, v_u_4112_, v___x_4162_, v___x_4160_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_, v___y_4067_, v___y_4068_, v___y_4069_);
return v___x_4164_;
}
else
{
lean_object* v_a_4165_; lean_object* v___x_4167_; uint8_t v_isShared_4168_; uint8_t v_isSharedCheck_4172_; 
lean_dec(v_a_4157_);
lean_dec(v_a_4155_);
lean_dec(v_v_4113_);
lean_dec(v_u_4112_);
lean_dec_ref(v_h_4058_);
lean_dec(v_a_3936_);
v_a_4165_ = lean_ctor_get(v___x_4158_, 0);
v_isSharedCheck_4172_ = !lean_is_exclusive(v___x_4158_);
if (v_isSharedCheck_4172_ == 0)
{
v___x_4167_ = v___x_4158_;
v_isShared_4168_ = v_isSharedCheck_4172_;
goto v_resetjp_4166_;
}
else
{
lean_inc(v_a_4165_);
lean_dec(v___x_4158_);
v___x_4167_ = lean_box(0);
v_isShared_4168_ = v_isSharedCheck_4172_;
goto v_resetjp_4166_;
}
v_resetjp_4166_:
{
lean_object* v___x_4170_; 
if (v_isShared_4168_ == 0)
{
v___x_4170_ = v___x_4167_;
goto v_reusejp_4169_;
}
else
{
lean_object* v_reuseFailAlloc_4171_; 
v_reuseFailAlloc_4171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4171_, 0, v_a_4165_);
v___x_4170_ = v_reuseFailAlloc_4171_;
goto v_reusejp_4169_;
}
v_reusejp_4169_:
{
return v___x_4170_;
}
}
}
}
else
{
lean_object* v_a_4173_; lean_object* v___x_4175_; uint8_t v_isShared_4176_; uint8_t v_isSharedCheck_4180_; 
lean_dec(v_a_4155_);
lean_dec(v_v_4113_);
lean_dec(v_u_4112_);
lean_dec_ref(v_h_4058_);
lean_dec(v_a_3936_);
v_a_4173_ = lean_ctor_get(v___x_4156_, 0);
v_isSharedCheck_4180_ = !lean_is_exclusive(v___x_4156_);
if (v_isSharedCheck_4180_ == 0)
{
v___x_4175_ = v___x_4156_;
v_isShared_4176_ = v_isSharedCheck_4180_;
goto v_resetjp_4174_;
}
else
{
lean_inc(v_a_4173_);
lean_dec(v___x_4156_);
v___x_4175_ = lean_box(0);
v_isShared_4176_ = v_isSharedCheck_4180_;
goto v_resetjp_4174_;
}
v_resetjp_4174_:
{
lean_object* v___x_4178_; 
if (v_isShared_4176_ == 0)
{
v___x_4178_ = v___x_4175_;
goto v_reusejp_4177_;
}
else
{
lean_object* v_reuseFailAlloc_4179_; 
v_reuseFailAlloc_4179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4179_, 0, v_a_4173_);
v___x_4178_ = v_reuseFailAlloc_4179_;
goto v_reusejp_4177_;
}
v_reusejp_4177_:
{
return v___x_4178_;
}
}
}
}
else
{
lean_object* v_a_4181_; lean_object* v___x_4183_; uint8_t v_isShared_4184_; uint8_t v_isSharedCheck_4188_; 
lean_dec(v_v_4113_);
lean_dec(v_u_4112_);
lean_dec_ref(v_h_4058_);
lean_dec(v_a_3936_);
v_a_4181_ = lean_ctor_get(v___x_4154_, 0);
v_isSharedCheck_4188_ = !lean_is_exclusive(v___x_4154_);
if (v_isSharedCheck_4188_ == 0)
{
v___x_4183_ = v___x_4154_;
v_isShared_4184_ = v_isSharedCheck_4188_;
goto v_resetjp_4182_;
}
else
{
lean_inc(v_a_4181_);
lean_dec(v___x_4154_);
v___x_4183_ = lean_box(0);
v_isShared_4184_ = v_isSharedCheck_4188_;
goto v_resetjp_4182_;
}
v_resetjp_4182_:
{
lean_object* v___x_4186_; 
if (v_isShared_4184_ == 0)
{
v___x_4186_ = v___x_4183_;
goto v_reusejp_4185_;
}
else
{
lean_object* v_reuseFailAlloc_4187_; 
v_reuseFailAlloc_4187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4187_, 0, v_a_4181_);
v___x_4186_ = v_reuseFailAlloc_4187_;
goto v_reusejp_4185_;
}
v_reusejp_4185_:
{
return v___x_4186_;
}
}
}
}
}
else
{
lean_object* v_a_4189_; lean_object* v___x_4191_; uint8_t v_isShared_4192_; uint8_t v_isSharedCheck_4196_; 
lean_dec(v_v_4113_);
lean_dec(v_u_4112_);
lean_dec_ref(v_h_4058_);
lean_dec(v_a_3936_);
v_a_4189_ = lean_ctor_get(v___x_4114_, 0);
v_isSharedCheck_4196_ = !lean_is_exclusive(v___x_4114_);
if (v_isSharedCheck_4196_ == 0)
{
v___x_4191_ = v___x_4114_;
v_isShared_4192_ = v_isSharedCheck_4196_;
goto v_resetjp_4190_;
}
else
{
lean_inc(v_a_4189_);
lean_dec(v___x_4114_);
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
}
else
{
uint8_t v_kind_4197_; 
lean_dec(v_a_4071_);
v_kind_4197_ = lean_ctor_get_uint8(v_c_3813_, sizeof(void*)*5);
if (v_kind_4197_ == 1)
{
lean_object* v_u_4198_; lean_object* v_v_4199_; lean_object* v_k_4200_; lean_object* v___x_4201_; 
v_u_4198_ = lean_ctor_get(v_c_3813_, 0);
lean_inc(v_u_4198_);
v_v_4199_ = lean_ctor_get(v_c_3813_, 1);
lean_inc(v_v_4199_);
v_k_4200_ = lean_ctor_get(v_c_3813_, 2);
lean_inc(v_k_4200_);
lean_dec_ref(v_c_3813_);
v___x_4201_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__24));
v___y_3999_ = v_u_4198_;
v___y_4000_ = v___y_4067_;
v___y_4001_ = v___y_4069_;
v___y_4002_ = v___y_4066_;
v___y_4003_ = v___y_4060_;
v___y_4004_ = v___y_4059_;
v___y_4005_ = v___y_4065_;
v___y_4006_ = v_v_4199_;
v___y_4007_ = v___y_4064_;
v___y_4008_ = v_kind_4197_;
v___y_4009_ = v_k_4200_;
v___y_4010_ = v___y_4062_;
v___y_4011_ = v_h_4058_;
v___y_4012_ = v___y_4068_;
v___y_4013_ = v___y_4063_;
v___y_4014_ = v___y_4061_;
v___y_4015_ = v___x_4201_;
goto v___jp_3998_;
}
else
{
lean_object* v_u_4202_; lean_object* v_v_4203_; lean_object* v_k_4204_; lean_object* v___x_4205_; 
v_u_4202_ = lean_ctor_get(v_c_3813_, 0);
lean_inc(v_u_4202_);
v_v_4203_ = lean_ctor_get(v_c_3813_, 1);
lean_inc(v_v_4203_);
v_k_4204_ = lean_ctor_get(v_c_3813_, 2);
lean_inc(v_k_4204_);
lean_dec_ref(v_c_3813_);
v___x_4205_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__26));
v___y_3999_ = v_u_4202_;
v___y_4000_ = v___y_4067_;
v___y_4001_ = v___y_4069_;
v___y_4002_ = v___y_4066_;
v___y_4003_ = v___y_4060_;
v___y_4004_ = v___y_4059_;
v___y_4005_ = v___y_4065_;
v___y_4006_ = v_v_4203_;
v___y_4007_ = v___y_4064_;
v___y_4008_ = v_kind_4197_;
v___y_4009_ = v_k_4204_;
v___y_4010_ = v___y_4062_;
v___y_4011_ = v_h_4058_;
v___y_4012_ = v___y_4068_;
v___y_4013_ = v___y_4063_;
v___y_4014_ = v___y_4061_;
v___y_4015_ = v___x_4205_;
goto v___jp_3998_;
}
}
}
else
{
lean_object* v_a_4206_; lean_object* v___x_4208_; uint8_t v_isShared_4209_; uint8_t v_isSharedCheck_4213_; 
lean_dec_ref(v_h_4058_);
lean_dec(v_a_3936_);
lean_dec_ref(v_c_3813_);
v_a_4206_ = lean_ctor_get(v___x_4070_, 0);
v_isSharedCheck_4213_ = !lean_is_exclusive(v___x_4070_);
if (v_isSharedCheck_4213_ == 0)
{
v___x_4208_ = v___x_4070_;
v_isShared_4209_ = v_isSharedCheck_4213_;
goto v_resetjp_4207_;
}
else
{
lean_inc(v_a_4206_);
lean_dec(v___x_4070_);
v___x_4208_ = lean_box(0);
v_isShared_4209_ = v_isSharedCheck_4213_;
goto v_resetjp_4207_;
}
v_resetjp_4207_:
{
lean_object* v___x_4211_; 
if (v_isShared_4209_ == 0)
{
v___x_4211_ = v___x_4208_;
goto v_reusejp_4210_;
}
else
{
lean_object* v_reuseFailAlloc_4212_; 
v_reuseFailAlloc_4212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4212_, 0, v_a_4206_);
v___x_4211_ = v_reuseFailAlloc_4212_;
goto v_reusejp_4210_;
}
v_reusejp_4210_:
{
return v___x_4211_;
}
}
}
}
v___jp_4214_:
{
lean_object* v_h_x3f_4226_; 
v_h_x3f_4226_ = lean_ctor_get(v_c_3813_, 4);
if (lean_obj_tag(v_h_x3f_4226_) == 1)
{
lean_object* v_e_4227_; lean_object* v_val_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; 
v_e_4227_ = lean_ctor_get(v_c_3813_, 3);
v_val_4228_ = lean_ctor_get(v_h_x3f_4226_, 0);
v___x_4229_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__29, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__29_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__29);
lean_inc_ref(v_e_3814_);
v___x_4230_ = l_Lean_Meta_mkOfEqFalseCore(v_e_3814_, v_he_3815_);
lean_inc(v_val_4228_);
lean_inc_ref(v_e_4227_);
v___x_4231_ = l_Lean_mkApp4(v___x_4229_, v_e_3814_, v_e_4227_, v_val_4228_, v___x_4230_);
v_h_4058_ = v___x_4231_;
v___y_4059_ = v___y_4215_;
v___y_4060_ = v___y_4216_;
v___y_4061_ = v___y_4217_;
v___y_4062_ = v___y_4218_;
v___y_4063_ = v___y_4219_;
v___y_4064_ = v___y_4220_;
v___y_4065_ = v___y_4221_;
v___y_4066_ = v___y_4222_;
v___y_4067_ = v___y_4223_;
v___y_4068_ = v___y_4224_;
v___y_4069_ = v___y_4225_;
goto v___jp_4057_;
}
else
{
lean_object* v___x_4232_; 
v___x_4232_ = l_Lean_Meta_mkOfEqFalseCore(v_e_3814_, v_he_3815_);
v_h_4058_ = v___x_4232_;
v___y_4059_ = v___y_4215_;
v___y_4060_ = v___y_4216_;
v___y_4061_ = v___y_4217_;
v___y_4062_ = v___y_4218_;
v___y_4063_ = v___y_4219_;
v___y_4064_ = v___y_4220_;
v___y_4065_ = v___y_4221_;
v___y_4066_ = v___y_4222_;
v___y_4067_ = v___y_4223_;
v___y_4068_ = v___y_4224_;
v___y_4069_ = v___y_4225_;
goto v___jp_4057_;
}
}
}
}
else
{
lean_object* v_a_4259_; lean_object* v___x_4261_; uint8_t v_isShared_4262_; uint8_t v_isSharedCheck_4266_; 
lean_dec_ref(v_he_3815_);
lean_dec_ref(v_e_3814_);
lean_dec_ref(v_c_3813_);
v_a_4259_ = lean_ctor_get(v___x_3935_, 0);
v_isSharedCheck_4266_ = !lean_is_exclusive(v___x_3935_);
if (v_isSharedCheck_4266_ == 0)
{
v___x_4261_ = v___x_3935_;
v_isShared_4262_ = v_isSharedCheck_4266_;
goto v_resetjp_4260_;
}
else
{
lean_inc(v_a_4259_);
lean_dec(v___x_3935_);
v___x_4261_ = lean_box(0);
v_isShared_4262_ = v_isSharedCheck_4266_;
goto v_resetjp_4260_;
}
v_resetjp_4260_:
{
lean_object* v___x_4264_; 
if (v_isShared_4262_ == 0)
{
v___x_4264_ = v___x_4261_;
goto v_reusejp_4263_;
}
else
{
lean_object* v_reuseFailAlloc_4265_; 
v_reuseFailAlloc_4265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4265_, 0, v_a_4259_);
v___x_4264_ = v_reuseFailAlloc_4265_;
goto v_reusejp_4263_;
}
v_reusejp_4263_:
{
return v___x_4264_;
}
}
}
v___jp_3828_:
{
lean_object* v___x_3845_; lean_object* v___x_3846_; 
v___x_3845_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3845_, 0, v_k_x27_3831_);
lean_ctor_set_uint8(v___x_3845_, sizeof(void*)*1, v_strict_3833_);
v___x_3846_ = l_Lean_Meta_Grind_Order_addEdge(v___y_3830_, v___y_3829_, v___x_3845_, v_h_3832_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_);
return v___x_3846_;
}
v___jp_3847_:
{
lean_object* v___x_3869_; uint8_t v___x_3870_; 
lean_inc_ref(v___y_3852_);
v___x_3869_ = l_Lean_mkApp6(v___y_3852_, v___y_3854_, v___y_3856_, v___y_3857_, v___y_3868_, v___y_3859_, v___y_3860_);
v___x_3870_ = 0;
v___y_3829_ = v___y_3848_;
v___y_3830_ = v___y_3862_;
v_k_x27_3831_ = v___y_3861_;
v_h_3832_ = v___x_3869_;
v_strict_3833_ = v___x_3870_;
v___y_3834_ = v___y_3855_;
v___y_3835_ = v___y_3853_;
v___y_3836_ = v___y_3867_;
v___y_3837_ = v___y_3864_;
v___y_3838_ = v___y_3866_;
v___y_3839_ = v___y_3863_;
v___y_3840_ = v___y_3858_;
v___y_3841_ = v___y_3851_;
v___y_3842_ = v___y_3849_;
v___y_3843_ = v___y_3865_;
v___y_3844_ = v___y_3850_;
goto v___jp_3828_;
}
v___jp_3871_:
{
lean_object* v___x_3890_; 
v___x_3890_ = l_Lean_Meta_Grind_Order_isInt(v___y_3878_, v___y_3877_, v___y_3888_, v___y_3885_, v___y_3887_, v___y_3884_, v___y_3882_, v___y_3876_, v___y_3873_, v___y_3886_, v___y_3875_);
if (lean_obj_tag(v___x_3890_) == 0)
{
lean_object* v_a_3891_; uint8_t v___x_3892_; 
v_a_3891_ = lean_ctor_get(v___x_3890_, 0);
lean_inc(v_a_3891_);
lean_dec_ref_known(v___x_3890_, 1);
v___x_3892_ = lean_unbox(v_a_3891_);
lean_dec(v_a_3891_);
if (v___x_3892_ == 0)
{
lean_dec_ref(v___y_3880_);
lean_dec_ref(v___y_3879_);
v___y_3829_ = v___y_3872_;
v___y_3830_ = v___y_3883_;
v_k_x27_3831_ = v___y_3874_;
v_h_3832_ = v___y_3881_;
v_strict_3833_ = v___y_3889_;
v___y_3834_ = v___y_3878_;
v___y_3835_ = v___y_3877_;
v___y_3836_ = v___y_3888_;
v___y_3837_ = v___y_3885_;
v___y_3838_ = v___y_3887_;
v___y_3839_ = v___y_3884_;
v___y_3840_ = v___y_3882_;
v___y_3841_ = v___y_3876_;
v___y_3842_ = v___y_3873_;
v___y_3843_ = v___y_3886_;
v___y_3844_ = v___y_3875_;
goto v___jp_3828_;
}
else
{
if (v___y_3889_ == 0)
{
lean_dec_ref(v___y_3880_);
lean_dec_ref(v___y_3879_);
v___y_3829_ = v___y_3872_;
v___y_3830_ = v___y_3883_;
v_k_x27_3831_ = v___y_3874_;
v_h_3832_ = v___y_3881_;
v_strict_3833_ = v___y_3889_;
v___y_3834_ = v___y_3878_;
v___y_3835_ = v___y_3877_;
v___y_3836_ = v___y_3888_;
v___y_3837_ = v___y_3885_;
v___y_3838_ = v___y_3887_;
v___y_3839_ = v___y_3884_;
v___y_3840_ = v___y_3882_;
v___y_3841_ = v___y_3876_;
v___y_3842_ = v___y_3873_;
v___y_3843_ = v___y_3886_;
v___y_3844_ = v___y_3875_;
goto v___jp_3828_;
}
else
{
lean_object* v___x_3893_; 
v___x_3893_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v___y_3883_, v___y_3878_, v___y_3877_, v___y_3886_);
if (lean_obj_tag(v___x_3893_) == 0)
{
lean_object* v_a_3894_; lean_object* v___x_3895_; 
v_a_3894_ = lean_ctor_get(v___x_3893_, 0);
lean_inc(v_a_3894_);
lean_dec_ref_known(v___x_3893_, 1);
v___x_3895_ = l_Lean_Meta_Grind_Order_getExpr___redArg(v___y_3872_, v___y_3878_, v___y_3877_, v___y_3886_);
if (lean_obj_tag(v___x_3895_) == 0)
{
lean_object* v_a_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; uint8_t v___x_3901_; 
v_a_3896_ = lean_ctor_get(v___x_3895_, 0);
lean_inc(v_a_3896_);
lean_dec_ref_known(v___x_3895_, 1);
v___x_3897_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__2, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__2);
v___x_3898_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__3, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__3);
v___x_3899_ = lean_int_sub(v___y_3874_, v___x_3898_);
lean_dec(v___y_3874_);
v___x_3900_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4);
v___x_3901_ = lean_int_dec_le(v___x_3900_, v___x_3899_);
if (v___x_3901_ == 0)
{
lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; 
v___x_3902_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10);
v___x_3903_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13);
v___x_3904_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16);
v___x_3905_ = lean_int_neg(v___x_3899_);
v___x_3906_ = l_Int_toNat(v___x_3905_);
lean_dec(v___x_3905_);
v___x_3907_ = l_Lean_instToExprInt_mkNat(v___x_3906_);
v___x_3908_ = l_Lean_mkApp3(v___x_3902_, v___x_3903_, v___x_3904_, v___x_3907_);
v___y_3848_ = v___y_3872_;
v___y_3849_ = v___y_3873_;
v___y_3850_ = v___y_3875_;
v___y_3851_ = v___y_3876_;
v___y_3852_ = v___x_3897_;
v___y_3853_ = v___y_3877_;
v___y_3854_ = v_a_3894_;
v___y_3855_ = v___y_3878_;
v___y_3856_ = v_a_3896_;
v___y_3857_ = v___y_3879_;
v___y_3858_ = v___y_3882_;
v___y_3859_ = v___y_3880_;
v___y_3860_ = v___y_3881_;
v___y_3861_ = v___x_3899_;
v___y_3862_ = v___y_3883_;
v___y_3863_ = v___y_3884_;
v___y_3864_ = v___y_3885_;
v___y_3865_ = v___y_3886_;
v___y_3866_ = v___y_3887_;
v___y_3867_ = v___y_3888_;
v___y_3868_ = v___x_3908_;
goto v___jp_3847_;
}
else
{
lean_object* v___x_3909_; lean_object* v___x_3910_; 
v___x_3909_ = l_Int_toNat(v___x_3899_);
v___x_3910_ = l_Lean_instToExprInt_mkNat(v___x_3909_);
v___y_3848_ = v___y_3872_;
v___y_3849_ = v___y_3873_;
v___y_3850_ = v___y_3875_;
v___y_3851_ = v___y_3876_;
v___y_3852_ = v___x_3897_;
v___y_3853_ = v___y_3877_;
v___y_3854_ = v_a_3894_;
v___y_3855_ = v___y_3878_;
v___y_3856_ = v_a_3896_;
v___y_3857_ = v___y_3879_;
v___y_3858_ = v___y_3882_;
v___y_3859_ = v___y_3880_;
v___y_3860_ = v___y_3881_;
v___y_3861_ = v___x_3899_;
v___y_3862_ = v___y_3883_;
v___y_3863_ = v___y_3884_;
v___y_3864_ = v___y_3885_;
v___y_3865_ = v___y_3886_;
v___y_3866_ = v___y_3887_;
v___y_3867_ = v___y_3888_;
v___y_3868_ = v___x_3910_;
goto v___jp_3847_;
}
}
else
{
lean_object* v_a_3911_; lean_object* v___x_3913_; uint8_t v_isShared_3914_; uint8_t v_isSharedCheck_3918_; 
lean_dec(v_a_3894_);
lean_dec(v___y_3883_);
lean_dec_ref(v___y_3881_);
lean_dec_ref(v___y_3880_);
lean_dec_ref(v___y_3879_);
lean_dec(v___y_3874_);
lean_dec(v___y_3872_);
v_a_3911_ = lean_ctor_get(v___x_3895_, 0);
v_isSharedCheck_3918_ = !lean_is_exclusive(v___x_3895_);
if (v_isSharedCheck_3918_ == 0)
{
v___x_3913_ = v___x_3895_;
v_isShared_3914_ = v_isSharedCheck_3918_;
goto v_resetjp_3912_;
}
else
{
lean_inc(v_a_3911_);
lean_dec(v___x_3895_);
v___x_3913_ = lean_box(0);
v_isShared_3914_ = v_isSharedCheck_3918_;
goto v_resetjp_3912_;
}
v_resetjp_3912_:
{
lean_object* v___x_3916_; 
if (v_isShared_3914_ == 0)
{
v___x_3916_ = v___x_3913_;
goto v_reusejp_3915_;
}
else
{
lean_object* v_reuseFailAlloc_3917_; 
v_reuseFailAlloc_3917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3917_, 0, v_a_3911_);
v___x_3916_ = v_reuseFailAlloc_3917_;
goto v_reusejp_3915_;
}
v_reusejp_3915_:
{
return v___x_3916_;
}
}
}
}
else
{
lean_object* v_a_3919_; lean_object* v___x_3921_; uint8_t v_isShared_3922_; uint8_t v_isSharedCheck_3926_; 
lean_dec(v___y_3883_);
lean_dec_ref(v___y_3881_);
lean_dec_ref(v___y_3880_);
lean_dec_ref(v___y_3879_);
lean_dec(v___y_3874_);
lean_dec(v___y_3872_);
v_a_3919_ = lean_ctor_get(v___x_3893_, 0);
v_isSharedCheck_3926_ = !lean_is_exclusive(v___x_3893_);
if (v_isSharedCheck_3926_ == 0)
{
v___x_3921_ = v___x_3893_;
v_isShared_3922_ = v_isSharedCheck_3926_;
goto v_resetjp_3920_;
}
else
{
lean_inc(v_a_3919_);
lean_dec(v___x_3893_);
v___x_3921_ = lean_box(0);
v_isShared_3922_ = v_isSharedCheck_3926_;
goto v_resetjp_3920_;
}
v_resetjp_3920_:
{
lean_object* v___x_3924_; 
if (v_isShared_3922_ == 0)
{
v___x_3924_ = v___x_3921_;
goto v_reusejp_3923_;
}
else
{
lean_object* v_reuseFailAlloc_3925_; 
v_reuseFailAlloc_3925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3925_, 0, v_a_3919_);
v___x_3924_ = v_reuseFailAlloc_3925_;
goto v_reusejp_3923_;
}
v_reusejp_3923_:
{
return v___x_3924_;
}
}
}
}
}
}
else
{
lean_object* v_a_3927_; lean_object* v___x_3929_; uint8_t v_isShared_3930_; uint8_t v_isSharedCheck_3934_; 
lean_dec(v___y_3883_);
lean_dec_ref(v___y_3881_);
lean_dec_ref(v___y_3880_);
lean_dec_ref(v___y_3879_);
lean_dec(v___y_3874_);
lean_dec(v___y_3872_);
v_a_3927_ = lean_ctor_get(v___x_3890_, 0);
v_isSharedCheck_3934_ = !lean_is_exclusive(v___x_3890_);
if (v_isSharedCheck_3934_ == 0)
{
v___x_3929_ = v___x_3890_;
v_isShared_3930_ = v_isSharedCheck_3934_;
goto v_resetjp_3928_;
}
else
{
lean_inc(v_a_3927_);
lean_dec(v___x_3890_);
v___x_3929_ = lean_box(0);
v_isShared_3930_ = v_isSharedCheck_3934_;
goto v_resetjp_3928_;
}
v_resetjp_3928_:
{
lean_object* v___x_3932_; 
if (v_isShared_3930_ == 0)
{
v___x_3932_ = v___x_3929_;
goto v_reusejp_3931_;
}
else
{
lean_object* v_reuseFailAlloc_3933_; 
v_reuseFailAlloc_3933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3933_, 0, v_a_3927_);
v___x_3932_ = v_reuseFailAlloc_3933_;
goto v_reusejp_3931_;
}
v_reusejp_3931_:
{
return v___x_3932_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___boxed(lean_object* v_c_4267_, lean_object* v_e_4268_, lean_object* v_he_4269_, lean_object* v_a_4270_, lean_object* v_a_4271_, lean_object* v_a_4272_, lean_object* v_a_4273_, lean_object* v_a_4274_, lean_object* v_a_4275_, lean_object* v_a_4276_, lean_object* v_a_4277_, lean_object* v_a_4278_, lean_object* v_a_4279_, lean_object* v_a_4280_, lean_object* v_a_4281_){
_start:
{
lean_object* v_res_4282_; 
v_res_4282_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse(v_c_4267_, v_e_4268_, v_he_4269_, v_a_4270_, v_a_4271_, v_a_4272_, v_a_4273_, v_a_4274_, v_a_4275_, v_a_4276_, v_a_4277_, v_a_4278_, v_a_4279_, v_a_4280_);
lean_dec(v_a_4280_);
lean_dec_ref(v_a_4279_);
lean_dec(v_a_4278_);
lean_dec_ref(v_a_4277_);
lean_dec(v_a_4276_);
lean_dec_ref(v_a_4275_);
lean_dec(v_a_4274_);
lean_dec_ref(v_a_4273_);
lean_dec(v_a_4272_);
lean_dec(v_a_4271_);
lean_dec(v_a_4270_);
return v_res_4282_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___redArg(lean_object* v_e_4283_, lean_object* v_a_4284_, lean_object* v_a_4285_){
_start:
{
lean_object* v___x_4287_; 
v___x_4287_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_4284_, v_a_4285_);
if (lean_obj_tag(v___x_4287_) == 0)
{
lean_object* v_a_4288_; lean_object* v___x_4290_; uint8_t v_isShared_4291_; uint8_t v_isSharedCheck_4297_; 
v_a_4288_ = lean_ctor_get(v___x_4287_, 0);
v_isSharedCheck_4297_ = !lean_is_exclusive(v___x_4287_);
if (v_isSharedCheck_4297_ == 0)
{
v___x_4290_ = v___x_4287_;
v_isShared_4291_ = v_isSharedCheck_4297_;
goto v_resetjp_4289_;
}
else
{
lean_inc(v_a_4288_);
lean_dec(v___x_4287_);
v___x_4290_ = lean_box(0);
v_isShared_4291_ = v_isSharedCheck_4297_;
goto v_resetjp_4289_;
}
v_resetjp_4289_:
{
lean_object* v_exprToStructId_4292_; lean_object* v___x_4293_; lean_object* v___x_4295_; 
v_exprToStructId_4292_ = lean_ctor_get(v_a_4288_, 2);
lean_inc_ref(v_exprToStructId_4292_);
lean_dec(v_a_4288_);
v___x_4293_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_exprToStructId_4292_, v_e_4283_);
lean_dec_ref(v_exprToStructId_4292_);
if (v_isShared_4291_ == 0)
{
lean_ctor_set(v___x_4290_, 0, v___x_4293_);
v___x_4295_ = v___x_4290_;
goto v_reusejp_4294_;
}
else
{
lean_object* v_reuseFailAlloc_4296_; 
v_reuseFailAlloc_4296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4296_, 0, v___x_4293_);
v___x_4295_ = v_reuseFailAlloc_4296_;
goto v_reusejp_4294_;
}
v_reusejp_4294_:
{
return v___x_4295_;
}
}
}
else
{
lean_object* v_a_4298_; lean_object* v___x_4300_; uint8_t v_isShared_4301_; uint8_t v_isSharedCheck_4305_; 
v_a_4298_ = lean_ctor_get(v___x_4287_, 0);
v_isSharedCheck_4305_ = !lean_is_exclusive(v___x_4287_);
if (v_isSharedCheck_4305_ == 0)
{
v___x_4300_ = v___x_4287_;
v_isShared_4301_ = v_isSharedCheck_4305_;
goto v_resetjp_4299_;
}
else
{
lean_inc(v_a_4298_);
lean_dec(v___x_4287_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___redArg___boxed(lean_object* v_e_4306_, lean_object* v_a_4307_, lean_object* v_a_4308_, lean_object* v_a_4309_){
_start:
{
lean_object* v_res_4310_; 
v_res_4310_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___redArg(v_e_4306_, v_a_4307_, v_a_4308_);
lean_dec_ref(v_a_4308_);
lean_dec(v_a_4307_);
lean_dec_ref(v_e_4306_);
return v_res_4310_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f(lean_object* v_e_4311_, lean_object* v_a_4312_, lean_object* v_a_4313_, lean_object* v_a_4314_, lean_object* v_a_4315_, lean_object* v_a_4316_, lean_object* v_a_4317_, lean_object* v_a_4318_, lean_object* v_a_4319_, lean_object* v_a_4320_, lean_object* v_a_4321_){
_start:
{
lean_object* v___x_4323_; 
v___x_4323_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___redArg(v_e_4311_, v_a_4312_, v_a_4320_);
return v___x_4323_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___boxed(lean_object* v_e_4324_, lean_object* v_a_4325_, lean_object* v_a_4326_, lean_object* v_a_4327_, lean_object* v_a_4328_, lean_object* v_a_4329_, lean_object* v_a_4330_, lean_object* v_a_4331_, lean_object* v_a_4332_, lean_object* v_a_4333_, lean_object* v_a_4334_, lean_object* v_a_4335_){
_start:
{
lean_object* v_res_4336_; 
v_res_4336_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f(v_e_4324_, v_a_4325_, v_a_4326_, v_a_4327_, v_a_4328_, v_a_4329_, v_a_4330_, v_a_4331_, v_a_4332_, v_a_4333_, v_a_4334_);
lean_dec(v_a_4334_);
lean_dec_ref(v_a_4333_);
lean_dec(v_a_4332_);
lean_dec_ref(v_a_4331_);
lean_dec(v_a_4330_);
lean_dec_ref(v_a_4329_);
lean_dec(v_a_4328_);
lean_dec_ref(v_a_4327_);
lean_dec(v_a_4326_);
lean_dec(v_a_4325_);
lean_dec_ref(v_e_4324_);
return v_res_4336_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__2(void){
_start:
{
lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; 
v___x_4343_ = lean_box(0);
v___x_4344_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__1));
v___x_4345_ = l_Lean_mkConst(v___x_4344_, v___x_4343_);
return v___x_4345_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__5(void){
_start:
{
lean_object* v___x_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; 
v___x_4352_ = lean_box(0);
v___x_4353_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__4));
v___x_4354_ = l_Lean_mkConst(v___x_4353_, v___x_4352_);
return v___x_4354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go(lean_object* v_e_4355_, lean_object* v_e_x27_4356_, lean_object* v_he_x3f_4357_, lean_object* v_a_4358_, lean_object* v_a_4359_, lean_object* v_a_4360_, lean_object* v_a_4361_, lean_object* v_a_4362_, lean_object* v_a_4363_, lean_object* v_a_4364_, lean_object* v_a_4365_, lean_object* v_a_4366_, lean_object* v_a_4367_){
_start:
{
lean_object* v___x_4369_; 
v___x_4369_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___redArg(v_e_x27_4356_, v_a_4358_, v_a_4366_);
if (lean_obj_tag(v___x_4369_) == 0)
{
lean_object* v_a_4370_; lean_object* v___x_4372_; uint8_t v_isShared_4373_; uint8_t v_isSharedCheck_4460_; 
v_a_4370_ = lean_ctor_get(v___x_4369_, 0);
v_isSharedCheck_4460_ = !lean_is_exclusive(v___x_4369_);
if (v_isSharedCheck_4460_ == 0)
{
v___x_4372_ = v___x_4369_;
v_isShared_4373_ = v_isSharedCheck_4460_;
goto v_resetjp_4371_;
}
else
{
lean_inc(v_a_4370_);
lean_dec(v___x_4369_);
v___x_4372_ = lean_box(0);
v_isShared_4373_ = v_isSharedCheck_4460_;
goto v_resetjp_4371_;
}
v_resetjp_4371_:
{
if (lean_obj_tag(v_a_4370_) == 1)
{
lean_object* v_val_4374_; lean_object* v___x_4375_; 
lean_del_object(v___x_4372_);
v_val_4374_ = lean_ctor_get(v_a_4370_, 0);
lean_inc(v_val_4374_);
lean_dec_ref_known(v_a_4370_, 1);
v___x_4375_ = l_Lean_Meta_Grind_Order_getCnstr_x3f___redArg(v_e_x27_4356_, v_val_4374_, v_a_4358_, v_a_4366_);
if (lean_obj_tag(v___x_4375_) == 0)
{
lean_object* v_a_4376_; lean_object* v___x_4378_; uint8_t v_isShared_4379_; uint8_t v_isSharedCheck_4447_; 
v_a_4376_ = lean_ctor_get(v___x_4375_, 0);
v_isSharedCheck_4447_ = !lean_is_exclusive(v___x_4375_);
if (v_isSharedCheck_4447_ == 0)
{
v___x_4378_ = v___x_4375_;
v_isShared_4379_ = v_isSharedCheck_4447_;
goto v_resetjp_4377_;
}
else
{
lean_inc(v_a_4376_);
lean_dec(v___x_4375_);
v___x_4378_ = lean_box(0);
v_isShared_4379_ = v_isSharedCheck_4447_;
goto v_resetjp_4377_;
}
v_resetjp_4377_:
{
if (lean_obj_tag(v_a_4376_) == 1)
{
lean_object* v_val_4380_; lean_object* v___x_4381_; 
lean_del_object(v___x_4378_);
v_val_4380_ = lean_ctor_get(v_a_4376_, 0);
lean_inc(v_val_4380_);
lean_dec_ref_known(v_a_4376_, 1);
lean_inc_ref(v_e_4355_);
v___x_4381_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_4355_, v_a_4358_, v_a_4362_, v_a_4364_, v_a_4365_, v_a_4366_, v_a_4367_);
if (lean_obj_tag(v___x_4381_) == 0)
{
lean_object* v_a_4382_; uint8_t v___x_4383_; 
v_a_4382_ = lean_ctor_get(v___x_4381_, 0);
lean_inc(v_a_4382_);
lean_dec_ref_known(v___x_4381_, 1);
v___x_4383_ = lean_unbox(v_a_4382_);
lean_dec(v_a_4382_);
if (v___x_4383_ == 0)
{
lean_object* v___x_4384_; 
lean_inc_ref(v_e_4355_);
v___x_4384_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_4355_, v_a_4358_, v_a_4362_, v_a_4364_, v_a_4365_, v_a_4366_, v_a_4367_);
if (lean_obj_tag(v___x_4384_) == 0)
{
lean_object* v_a_4385_; lean_object* v___x_4387_; uint8_t v_isShared_4388_; uint8_t v_isSharedCheck_4410_; 
v_a_4385_ = lean_ctor_get(v___x_4384_, 0);
v_isSharedCheck_4410_ = !lean_is_exclusive(v___x_4384_);
if (v_isSharedCheck_4410_ == 0)
{
v___x_4387_ = v___x_4384_;
v_isShared_4388_ = v_isSharedCheck_4410_;
goto v_resetjp_4386_;
}
else
{
lean_inc(v_a_4385_);
lean_dec(v___x_4384_);
v___x_4387_ = lean_box(0);
v_isShared_4388_ = v_isSharedCheck_4410_;
goto v_resetjp_4386_;
}
v_resetjp_4386_:
{
uint8_t v___x_4389_; 
v___x_4389_ = lean_unbox(v_a_4385_);
lean_dec(v_a_4385_);
if (v___x_4389_ == 0)
{
lean_object* v___x_4390_; lean_object* v___x_4392_; 
lean_dec(v_val_4380_);
lean_dec(v_val_4374_);
lean_dec(v_he_x3f_4357_);
lean_dec_ref(v_e_x27_4356_);
lean_dec_ref(v_e_4355_);
v___x_4390_ = lean_box(0);
if (v_isShared_4388_ == 0)
{
lean_ctor_set(v___x_4387_, 0, v___x_4390_);
v___x_4392_ = v___x_4387_;
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
lean_object* v___x_4394_; 
lean_del_object(v___x_4387_);
lean_inc_ref(v_e_4355_);
v___x_4394_ = l_Lean_Meta_Grind_mkEqFalseProof(v_e_4355_, v_a_4358_, v_a_4359_, v_a_4360_, v_a_4361_, v_a_4362_, v_a_4363_, v_a_4364_, v_a_4365_, v_a_4366_, v_a_4367_);
if (lean_obj_tag(v___x_4394_) == 0)
{
if (lean_obj_tag(v_he_x3f_4357_) == 1)
{
lean_object* v_a_4395_; lean_object* v_val_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; 
v_a_4395_ = lean_ctor_get(v___x_4394_, 0);
lean_inc(v_a_4395_);
lean_dec_ref_known(v___x_4394_, 1);
v_val_4396_ = lean_ctor_get(v_he_x3f_4357_, 0);
lean_inc(v_val_4396_);
lean_dec_ref_known(v_he_x3f_4357_, 1);
v___x_4397_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__2, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__2);
lean_inc_ref(v_e_x27_4356_);
v___x_4398_ = l_Lean_mkApp4(v___x_4397_, v_e_4355_, v_e_x27_4356_, v_val_4396_, v_a_4395_);
v___x_4399_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse(v_val_4380_, v_e_x27_4356_, v___x_4398_, v_val_4374_, v_a_4358_, v_a_4359_, v_a_4360_, v_a_4361_, v_a_4362_, v_a_4363_, v_a_4364_, v_a_4365_, v_a_4366_, v_a_4367_);
lean_dec(v_val_4374_);
return v___x_4399_;
}
else
{
lean_object* v_a_4400_; lean_object* v___x_4401_; 
lean_dec(v_he_x3f_4357_);
lean_dec_ref(v_e_4355_);
v_a_4400_ = lean_ctor_get(v___x_4394_, 0);
lean_inc(v_a_4400_);
lean_dec_ref_known(v___x_4394_, 1);
v___x_4401_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse(v_val_4380_, v_e_x27_4356_, v_a_4400_, v_val_4374_, v_a_4358_, v_a_4359_, v_a_4360_, v_a_4361_, v_a_4362_, v_a_4363_, v_a_4364_, v_a_4365_, v_a_4366_, v_a_4367_);
lean_dec(v_val_4374_);
return v___x_4401_;
}
}
else
{
lean_object* v_a_4402_; lean_object* v___x_4404_; uint8_t v_isShared_4405_; uint8_t v_isSharedCheck_4409_; 
lean_dec(v_val_4380_);
lean_dec(v_val_4374_);
lean_dec(v_he_x3f_4357_);
lean_dec_ref(v_e_x27_4356_);
lean_dec_ref(v_e_4355_);
v_a_4402_ = lean_ctor_get(v___x_4394_, 0);
v_isSharedCheck_4409_ = !lean_is_exclusive(v___x_4394_);
if (v_isSharedCheck_4409_ == 0)
{
v___x_4404_ = v___x_4394_;
v_isShared_4405_ = v_isSharedCheck_4409_;
goto v_resetjp_4403_;
}
else
{
lean_inc(v_a_4402_);
lean_dec(v___x_4394_);
v___x_4404_ = lean_box(0);
v_isShared_4405_ = v_isSharedCheck_4409_;
goto v_resetjp_4403_;
}
v_resetjp_4403_:
{
lean_object* v___x_4407_; 
if (v_isShared_4405_ == 0)
{
v___x_4407_ = v___x_4404_;
goto v_reusejp_4406_;
}
else
{
lean_object* v_reuseFailAlloc_4408_; 
v_reuseFailAlloc_4408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4408_, 0, v_a_4402_);
v___x_4407_ = v_reuseFailAlloc_4408_;
goto v_reusejp_4406_;
}
v_reusejp_4406_:
{
return v___x_4407_;
}
}
}
}
}
}
else
{
lean_object* v_a_4411_; lean_object* v___x_4413_; uint8_t v_isShared_4414_; uint8_t v_isSharedCheck_4418_; 
lean_dec(v_val_4380_);
lean_dec(v_val_4374_);
lean_dec(v_he_x3f_4357_);
lean_dec_ref(v_e_x27_4356_);
lean_dec_ref(v_e_4355_);
v_a_4411_ = lean_ctor_get(v___x_4384_, 0);
v_isSharedCheck_4418_ = !lean_is_exclusive(v___x_4384_);
if (v_isSharedCheck_4418_ == 0)
{
v___x_4413_ = v___x_4384_;
v_isShared_4414_ = v_isSharedCheck_4418_;
goto v_resetjp_4412_;
}
else
{
lean_inc(v_a_4411_);
lean_dec(v___x_4384_);
v___x_4413_ = lean_box(0);
v_isShared_4414_ = v_isSharedCheck_4418_;
goto v_resetjp_4412_;
}
v_resetjp_4412_:
{
lean_object* v___x_4416_; 
if (v_isShared_4414_ == 0)
{
v___x_4416_ = v___x_4413_;
goto v_reusejp_4415_;
}
else
{
lean_object* v_reuseFailAlloc_4417_; 
v_reuseFailAlloc_4417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4417_, 0, v_a_4411_);
v___x_4416_ = v_reuseFailAlloc_4417_;
goto v_reusejp_4415_;
}
v_reusejp_4415_:
{
return v___x_4416_;
}
}
}
}
else
{
lean_object* v___x_4419_; 
lean_inc_ref(v_e_4355_);
v___x_4419_ = l_Lean_Meta_Grind_mkEqTrueProof(v_e_4355_, v_a_4358_, v_a_4359_, v_a_4360_, v_a_4361_, v_a_4362_, v_a_4363_, v_a_4364_, v_a_4365_, v_a_4366_, v_a_4367_);
if (lean_obj_tag(v___x_4419_) == 0)
{
if (lean_obj_tag(v_he_x3f_4357_) == 1)
{
lean_object* v_a_4420_; lean_object* v_val_4421_; lean_object* v___x_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; 
v_a_4420_ = lean_ctor_get(v___x_4419_, 0);
lean_inc(v_a_4420_);
lean_dec_ref_known(v___x_4419_, 1);
v_val_4421_ = lean_ctor_get(v_he_x3f_4357_, 0);
lean_inc(v_val_4421_);
lean_dec_ref_known(v_he_x3f_4357_, 1);
v___x_4422_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__5);
lean_inc_ref(v_e_x27_4356_);
v___x_4423_ = l_Lean_mkApp4(v___x_4422_, v_e_4355_, v_e_x27_4356_, v_val_4421_, v_a_4420_);
v___x_4424_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue(v_val_4380_, v_e_x27_4356_, v___x_4423_, v_val_4374_, v_a_4358_, v_a_4359_, v_a_4360_, v_a_4361_, v_a_4362_, v_a_4363_, v_a_4364_, v_a_4365_, v_a_4366_, v_a_4367_);
lean_dec(v_val_4374_);
return v___x_4424_;
}
else
{
lean_object* v_a_4425_; lean_object* v___x_4426_; 
lean_dec(v_he_x3f_4357_);
lean_dec_ref(v_e_4355_);
v_a_4425_ = lean_ctor_get(v___x_4419_, 0);
lean_inc(v_a_4425_);
lean_dec_ref_known(v___x_4419_, 1);
v___x_4426_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue(v_val_4380_, v_e_x27_4356_, v_a_4425_, v_val_4374_, v_a_4358_, v_a_4359_, v_a_4360_, v_a_4361_, v_a_4362_, v_a_4363_, v_a_4364_, v_a_4365_, v_a_4366_, v_a_4367_);
lean_dec(v_val_4374_);
return v___x_4426_;
}
}
else
{
lean_object* v_a_4427_; lean_object* v___x_4429_; uint8_t v_isShared_4430_; uint8_t v_isSharedCheck_4434_; 
lean_dec(v_val_4380_);
lean_dec(v_val_4374_);
lean_dec(v_he_x3f_4357_);
lean_dec_ref(v_e_x27_4356_);
lean_dec_ref(v_e_4355_);
v_a_4427_ = lean_ctor_get(v___x_4419_, 0);
v_isSharedCheck_4434_ = !lean_is_exclusive(v___x_4419_);
if (v_isSharedCheck_4434_ == 0)
{
v___x_4429_ = v___x_4419_;
v_isShared_4430_ = v_isSharedCheck_4434_;
goto v_resetjp_4428_;
}
else
{
lean_inc(v_a_4427_);
lean_dec(v___x_4419_);
v___x_4429_ = lean_box(0);
v_isShared_4430_ = v_isSharedCheck_4434_;
goto v_resetjp_4428_;
}
v_resetjp_4428_:
{
lean_object* v___x_4432_; 
if (v_isShared_4430_ == 0)
{
v___x_4432_ = v___x_4429_;
goto v_reusejp_4431_;
}
else
{
lean_object* v_reuseFailAlloc_4433_; 
v_reuseFailAlloc_4433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4433_, 0, v_a_4427_);
v___x_4432_ = v_reuseFailAlloc_4433_;
goto v_reusejp_4431_;
}
v_reusejp_4431_:
{
return v___x_4432_;
}
}
}
}
}
else
{
lean_object* v_a_4435_; lean_object* v___x_4437_; uint8_t v_isShared_4438_; uint8_t v_isSharedCheck_4442_; 
lean_dec(v_val_4380_);
lean_dec(v_val_4374_);
lean_dec(v_he_x3f_4357_);
lean_dec_ref(v_e_x27_4356_);
lean_dec_ref(v_e_4355_);
v_a_4435_ = lean_ctor_get(v___x_4381_, 0);
v_isSharedCheck_4442_ = !lean_is_exclusive(v___x_4381_);
if (v_isSharedCheck_4442_ == 0)
{
v___x_4437_ = v___x_4381_;
v_isShared_4438_ = v_isSharedCheck_4442_;
goto v_resetjp_4436_;
}
else
{
lean_inc(v_a_4435_);
lean_dec(v___x_4381_);
v___x_4437_ = lean_box(0);
v_isShared_4438_ = v_isSharedCheck_4442_;
goto v_resetjp_4436_;
}
v_resetjp_4436_:
{
lean_object* v___x_4440_; 
if (v_isShared_4438_ == 0)
{
v___x_4440_ = v___x_4437_;
goto v_reusejp_4439_;
}
else
{
lean_object* v_reuseFailAlloc_4441_; 
v_reuseFailAlloc_4441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4441_, 0, v_a_4435_);
v___x_4440_ = v_reuseFailAlloc_4441_;
goto v_reusejp_4439_;
}
v_reusejp_4439_:
{
return v___x_4440_;
}
}
}
}
else
{
lean_object* v___x_4443_; lean_object* v___x_4445_; 
lean_dec(v_a_4376_);
lean_dec(v_val_4374_);
lean_dec(v_he_x3f_4357_);
lean_dec_ref(v_e_x27_4356_);
lean_dec_ref(v_e_4355_);
v___x_4443_ = lean_box(0);
if (v_isShared_4379_ == 0)
{
lean_ctor_set(v___x_4378_, 0, v___x_4443_);
v___x_4445_ = v___x_4378_;
goto v_reusejp_4444_;
}
else
{
lean_object* v_reuseFailAlloc_4446_; 
v_reuseFailAlloc_4446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4446_, 0, v___x_4443_);
v___x_4445_ = v_reuseFailAlloc_4446_;
goto v_reusejp_4444_;
}
v_reusejp_4444_:
{
return v___x_4445_;
}
}
}
}
else
{
lean_object* v_a_4448_; lean_object* v___x_4450_; uint8_t v_isShared_4451_; uint8_t v_isSharedCheck_4455_; 
lean_dec(v_val_4374_);
lean_dec(v_he_x3f_4357_);
lean_dec_ref(v_e_x27_4356_);
lean_dec_ref(v_e_4355_);
v_a_4448_ = lean_ctor_get(v___x_4375_, 0);
v_isSharedCheck_4455_ = !lean_is_exclusive(v___x_4375_);
if (v_isSharedCheck_4455_ == 0)
{
v___x_4450_ = v___x_4375_;
v_isShared_4451_ = v_isSharedCheck_4455_;
goto v_resetjp_4449_;
}
else
{
lean_inc(v_a_4448_);
lean_dec(v___x_4375_);
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
else
{
lean_object* v___x_4456_; lean_object* v___x_4458_; 
lean_dec(v_a_4370_);
lean_dec(v_he_x3f_4357_);
lean_dec_ref(v_e_x27_4356_);
lean_dec_ref(v_e_4355_);
v___x_4456_ = lean_box(0);
if (v_isShared_4373_ == 0)
{
lean_ctor_set(v___x_4372_, 0, v___x_4456_);
v___x_4458_ = v___x_4372_;
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
}
}
else
{
lean_object* v_a_4461_; lean_object* v___x_4463_; uint8_t v_isShared_4464_; uint8_t v_isSharedCheck_4468_; 
lean_dec(v_he_x3f_4357_);
lean_dec_ref(v_e_x27_4356_);
lean_dec_ref(v_e_4355_);
v_a_4461_ = lean_ctor_get(v___x_4369_, 0);
v_isSharedCheck_4468_ = !lean_is_exclusive(v___x_4369_);
if (v_isSharedCheck_4468_ == 0)
{
v___x_4463_ = v___x_4369_;
v_isShared_4464_ = v_isSharedCheck_4468_;
goto v_resetjp_4462_;
}
else
{
lean_inc(v_a_4461_);
lean_dec(v___x_4369_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___boxed(lean_object* v_e_4469_, lean_object* v_e_x27_4470_, lean_object* v_he_x3f_4471_, lean_object* v_a_4472_, lean_object* v_a_4473_, lean_object* v_a_4474_, lean_object* v_a_4475_, lean_object* v_a_4476_, lean_object* v_a_4477_, lean_object* v_a_4478_, lean_object* v_a_4479_, lean_object* v_a_4480_, lean_object* v_a_4481_, lean_object* v_a_4482_){
_start:
{
lean_object* v_res_4483_; 
v_res_4483_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go(v_e_4469_, v_e_x27_4470_, v_he_x3f_4471_, v_a_4472_, v_a_4473_, v_a_4474_, v_a_4475_, v_a_4476_, v_a_4477_, v_a_4478_, v_a_4479_, v_a_4480_, v_a_4481_);
lean_dec(v_a_4481_);
lean_dec_ref(v_a_4480_);
lean_dec(v_a_4479_);
lean_dec_ref(v_a_4478_);
lean_dec(v_a_4477_);
lean_dec_ref(v_a_4476_);
lean_dec(v_a_4475_);
lean_dec_ref(v_a_4474_);
lean_dec(v_a_4473_);
lean_dec(v_a_4472_);
return v_res_4483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq(lean_object* v_e_4484_, lean_object* v_a_4485_, lean_object* v_a_4486_, lean_object* v_a_4487_, lean_object* v_a_4488_, lean_object* v_a_4489_, lean_object* v_a_4490_, lean_object* v_a_4491_, lean_object* v_a_4492_, lean_object* v_a_4493_, lean_object* v_a_4494_){
_start:
{
lean_object* v___x_4496_; 
v___x_4496_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_4485_, v_a_4493_);
if (lean_obj_tag(v___x_4496_) == 0)
{
lean_object* v_a_4497_; lean_object* v_termMap_4498_; lean_object* v___x_4499_; 
v_a_4497_ = lean_ctor_get(v___x_4496_, 0);
lean_inc(v_a_4497_);
lean_dec_ref_known(v___x_4496_, 1);
v_termMap_4498_ = lean_ctor_get(v_a_4497_, 3);
lean_inc_ref(v_termMap_4498_);
lean_dec(v_a_4497_);
v___x_4499_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMap_4498_, v_e_4484_);
lean_dec_ref(v_termMap_4498_);
if (lean_obj_tag(v___x_4499_) == 1)
{
lean_object* v_val_4500_; lean_object* v___x_4502_; uint8_t v_isShared_4503_; uint8_t v_isSharedCheck_4510_; 
v_val_4500_ = lean_ctor_get(v___x_4499_, 0);
v_isSharedCheck_4510_ = !lean_is_exclusive(v___x_4499_);
if (v_isSharedCheck_4510_ == 0)
{
v___x_4502_ = v___x_4499_;
v_isShared_4503_ = v_isSharedCheck_4510_;
goto v_resetjp_4501_;
}
else
{
lean_inc(v_val_4500_);
lean_dec(v___x_4499_);
v___x_4502_ = lean_box(0);
v_isShared_4503_ = v_isSharedCheck_4510_;
goto v_resetjp_4501_;
}
v_resetjp_4501_:
{
lean_object* v_e_4504_; lean_object* v_h_4505_; lean_object* v___x_4507_; 
v_e_4504_ = lean_ctor_get(v_val_4500_, 0);
lean_inc_ref(v_e_4504_);
v_h_4505_ = lean_ctor_get(v_val_4500_, 1);
lean_inc_ref(v_h_4505_);
lean_dec(v_val_4500_);
if (v_isShared_4503_ == 0)
{
lean_ctor_set(v___x_4502_, 0, v_h_4505_);
v___x_4507_ = v___x_4502_;
goto v_reusejp_4506_;
}
else
{
lean_object* v_reuseFailAlloc_4509_; 
v_reuseFailAlloc_4509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4509_, 0, v_h_4505_);
v___x_4507_ = v_reuseFailAlloc_4509_;
goto v_reusejp_4506_;
}
v_reusejp_4506_:
{
lean_object* v___x_4508_; 
v___x_4508_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go(v_e_4484_, v_e_4504_, v___x_4507_, v_a_4485_, v_a_4486_, v_a_4487_, v_a_4488_, v_a_4489_, v_a_4490_, v_a_4491_, v_a_4492_, v_a_4493_, v_a_4494_);
return v___x_4508_;
}
}
}
else
{
lean_object* v___x_4511_; lean_object* v___x_4512_; 
lean_dec(v___x_4499_);
v___x_4511_ = lean_box(0);
lean_inc_ref(v_e_4484_);
v___x_4512_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go(v_e_4484_, v_e_4484_, v___x_4511_, v_a_4485_, v_a_4486_, v_a_4487_, v_a_4488_, v_a_4489_, v_a_4490_, v_a_4491_, v_a_4492_, v_a_4493_, v_a_4494_);
return v___x_4512_;
}
}
else
{
lean_object* v_a_4513_; lean_object* v___x_4515_; uint8_t v_isShared_4516_; uint8_t v_isSharedCheck_4520_; 
lean_dec_ref(v_e_4484_);
v_a_4513_ = lean_ctor_get(v___x_4496_, 0);
v_isSharedCheck_4520_ = !lean_is_exclusive(v___x_4496_);
if (v_isSharedCheck_4520_ == 0)
{
v___x_4515_ = v___x_4496_;
v_isShared_4516_ = v_isSharedCheck_4520_;
goto v_resetjp_4514_;
}
else
{
lean_inc(v_a_4513_);
lean_dec(v___x_4496_);
v___x_4515_ = lean_box(0);
v_isShared_4516_ = v_isSharedCheck_4520_;
goto v_resetjp_4514_;
}
v_resetjp_4514_:
{
lean_object* v___x_4518_; 
if (v_isShared_4516_ == 0)
{
v___x_4518_ = v___x_4515_;
goto v_reusejp_4517_;
}
else
{
lean_object* v_reuseFailAlloc_4519_; 
v_reuseFailAlloc_4519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4519_, 0, v_a_4513_);
v___x_4518_ = v_reuseFailAlloc_4519_;
goto v_reusejp_4517_;
}
v_reusejp_4517_:
{
return v___x_4518_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq___boxed(lean_object* v_e_4521_, lean_object* v_a_4522_, lean_object* v_a_4523_, lean_object* v_a_4524_, lean_object* v_a_4525_, lean_object* v_a_4526_, lean_object* v_a_4527_, lean_object* v_a_4528_, lean_object* v_a_4529_, lean_object* v_a_4530_, lean_object* v_a_4531_, lean_object* v_a_4532_){
_start:
{
lean_object* v_res_4533_; 
v_res_4533_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq(v_e_4521_, v_a_4522_, v_a_4523_, v_a_4524_, v_a_4525_, v_a_4526_, v_a_4527_, v_a_4528_, v_a_4529_, v_a_4530_, v_a_4531_);
lean_dec(v_a_4531_);
lean_dec_ref(v_a_4530_);
lean_dec(v_a_4529_);
lean_dec_ref(v_a_4528_);
lean_dec(v_a_4527_);
lean_dec_ref(v_a_4526_);
lean_dec(v_a_4525_);
lean_dec_ref(v_a_4524_);
lean_dec(v_a_4523_);
lean_dec(v_a_4522_);
return v_res_4533_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE(lean_object* v_e_4534_, lean_object* v_a_4535_, lean_object* v_a_4536_, lean_object* v_a_4537_, lean_object* v_a_4538_, lean_object* v_a_4539_, lean_object* v_a_4540_, lean_object* v_a_4541_, lean_object* v_a_4542_, lean_object* v_a_4543_, lean_object* v_a_4544_){
_start:
{
lean_object* v___x_4546_; 
v___x_4546_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq(v_e_4534_, v_a_4535_, v_a_4536_, v_a_4537_, v_a_4538_, v_a_4539_, v_a_4540_, v_a_4541_, v_a_4542_, v_a_4543_, v_a_4544_);
return v___x_4546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___boxed(lean_object* v_e_4547_, lean_object* v_a_4548_, lean_object* v_a_4549_, lean_object* v_a_4550_, lean_object* v_a_4551_, lean_object* v_a_4552_, lean_object* v_a_4553_, lean_object* v_a_4554_, lean_object* v_a_4555_, lean_object* v_a_4556_, lean_object* v_a_4557_, lean_object* v_a_4558_){
_start:
{
lean_object* v_res_4559_; 
v_res_4559_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE(v_e_4547_, v_a_4548_, v_a_4549_, v_a_4550_, v_a_4551_, v_a_4552_, v_a_4553_, v_a_4554_, v_a_4555_, v_a_4556_, v_a_4557_);
lean_dec(v_a_4557_);
lean_dec_ref(v_a_4556_);
lean_dec(v_a_4555_);
lean_dec_ref(v_a_4554_);
lean_dec(v_a_4553_);
lean_dec_ref(v_a_4552_);
lean_dec(v_a_4551_);
lean_dec_ref(v_a_4550_);
lean_dec(v_a_4549_);
lean_dec(v_a_4548_);
return v_res_4559_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_9_(){
_start:
{
lean_object* v___f_4567_; lean_object* v___x_4568_; lean_object* v___x_4569_; 
v___f_4567_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_9_));
v___x_4568_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_9_));
v___x_4569_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_4568_, v___f_4567_);
return v___x_4569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_9____boxed(lean_object* v_a_4570_){
_start:
{
lean_object* v_res_4571_; 
v_res_4571_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_9_();
return v_res_4571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT(lean_object* v_e_4572_, lean_object* v_a_4573_, lean_object* v_a_4574_, lean_object* v_a_4575_, lean_object* v_a_4576_, lean_object* v_a_4577_, lean_object* v_a_4578_, lean_object* v_a_4579_, lean_object* v_a_4580_, lean_object* v_a_4581_, lean_object* v_a_4582_){
_start:
{
lean_object* v___x_4584_; 
v___x_4584_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq(v_e_4572_, v_a_4573_, v_a_4574_, v_a_4575_, v_a_4576_, v_a_4577_, v_a_4578_, v_a_4579_, v_a_4580_, v_a_4581_, v_a_4582_);
return v___x_4584_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___boxed(lean_object* v_e_4585_, lean_object* v_a_4586_, lean_object* v_a_4587_, lean_object* v_a_4588_, lean_object* v_a_4589_, lean_object* v_a_4590_, lean_object* v_a_4591_, lean_object* v_a_4592_, lean_object* v_a_4593_, lean_object* v_a_4594_, lean_object* v_a_4595_, lean_object* v_a_4596_){
_start:
{
lean_object* v_res_4597_; 
v_res_4597_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT(v_e_4585_, v_a_4586_, v_a_4587_, v_a_4588_, v_a_4589_, v_a_4590_, v_a_4591_, v_a_4592_, v_a_4593_, v_a_4594_, v_a_4595_);
lean_dec(v_a_4595_);
lean_dec_ref(v_a_4594_);
lean_dec(v_a_4593_);
lean_dec_ref(v_a_4592_);
lean_dec(v_a_4591_);
lean_dec_ref(v_a_4590_);
lean_dec(v_a_4589_);
lean_dec_ref(v_a_4588_);
lean_dec(v_a_4587_);
lean_dec(v_a_4586_);
return v_res_4597_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_1204040634____hygCtx___hyg_9_(){
_start:
{
lean_object* v___f_4604_; lean_object* v___x_4605_; lean_object* v___x_4606_; 
v___f_4604_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_9_));
v___x_4605_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_1204040634____hygCtx___hyg_9_));
v___x_4606_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_4605_, v___f_4604_);
return v___x_4606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_1204040634____hygCtx___hyg_9____boxed(lean_object* v_a_4607_){
_start:
{
lean_object* v_res_4608_; 
v_res_4608_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_1204040634____hygCtx___hyg_9_();
return v_res_4608_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f___redArg(lean_object* v_e_4609_, lean_object* v_a_4610_, lean_object* v_a_4611_){
_start:
{
lean_object* v___x_4613_; 
v___x_4613_ = l_Lean_Meta_Grind_Order_get_x27___redArg(v_a_4610_, v_a_4611_);
if (lean_obj_tag(v___x_4613_) == 0)
{
lean_object* v_a_4614_; lean_object* v___x_4616_; uint8_t v_isShared_4617_; uint8_t v_isSharedCheck_4623_; 
v_a_4614_ = lean_ctor_get(v___x_4613_, 0);
v_isSharedCheck_4623_ = !lean_is_exclusive(v___x_4613_);
if (v_isSharedCheck_4623_ == 0)
{
v___x_4616_ = v___x_4613_;
v_isShared_4617_ = v_isSharedCheck_4623_;
goto v_resetjp_4615_;
}
else
{
lean_inc(v_a_4614_);
lean_dec(v___x_4613_);
v___x_4616_ = lean_box(0);
v_isShared_4617_ = v_isSharedCheck_4623_;
goto v_resetjp_4615_;
}
v_resetjp_4615_:
{
lean_object* v_termMap_4618_; lean_object* v___x_4619_; lean_object* v___x_4621_; 
v_termMap_4618_ = lean_ctor_get(v_a_4614_, 3);
lean_inc_ref(v_termMap_4618_);
lean_dec(v_a_4614_);
v___x_4619_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(v_termMap_4618_, v_e_4609_);
lean_dec_ref(v_termMap_4618_);
if (v_isShared_4617_ == 0)
{
lean_ctor_set(v___x_4616_, 0, v___x_4619_);
v___x_4621_ = v___x_4616_;
goto v_reusejp_4620_;
}
else
{
lean_object* v_reuseFailAlloc_4622_; 
v_reuseFailAlloc_4622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4622_, 0, v___x_4619_);
v___x_4621_ = v_reuseFailAlloc_4622_;
goto v_reusejp_4620_;
}
v_reusejp_4620_:
{
return v___x_4621_;
}
}
}
else
{
lean_object* v_a_4624_; lean_object* v___x_4626_; uint8_t v_isShared_4627_; uint8_t v_isSharedCheck_4631_; 
v_a_4624_ = lean_ctor_get(v___x_4613_, 0);
v_isSharedCheck_4631_ = !lean_is_exclusive(v___x_4613_);
if (v_isSharedCheck_4631_ == 0)
{
v___x_4626_ = v___x_4613_;
v_isShared_4627_ = v_isSharedCheck_4631_;
goto v_resetjp_4625_;
}
else
{
lean_inc(v_a_4624_);
lean_dec(v___x_4613_);
v___x_4626_ = lean_box(0);
v_isShared_4627_ = v_isSharedCheck_4631_;
goto v_resetjp_4625_;
}
v_resetjp_4625_:
{
lean_object* v___x_4629_; 
if (v_isShared_4627_ == 0)
{
v___x_4629_ = v___x_4626_;
goto v_reusejp_4628_;
}
else
{
lean_object* v_reuseFailAlloc_4630_; 
v_reuseFailAlloc_4630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4630_, 0, v_a_4624_);
v___x_4629_ = v_reuseFailAlloc_4630_;
goto v_reusejp_4628_;
}
v_reusejp_4628_:
{
return v___x_4629_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f___redArg___boxed(lean_object* v_e_4632_, lean_object* v_a_4633_, lean_object* v_a_4634_, lean_object* v_a_4635_){
_start:
{
lean_object* v_res_4636_; 
v_res_4636_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f___redArg(v_e_4632_, v_a_4633_, v_a_4634_);
lean_dec_ref(v_a_4634_);
lean_dec(v_a_4633_);
lean_dec_ref(v_e_4632_);
return v_res_4636_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f(lean_object* v_e_4637_, lean_object* v_a_4638_, lean_object* v_a_4639_, lean_object* v_a_4640_, lean_object* v_a_4641_, lean_object* v_a_4642_, lean_object* v_a_4643_, lean_object* v_a_4644_, lean_object* v_a_4645_, lean_object* v_a_4646_, lean_object* v_a_4647_){
_start:
{
lean_object* v___x_4649_; 
v___x_4649_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f___redArg(v_e_4637_, v_a_4638_, v_a_4646_);
return v___x_4649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f___boxed(lean_object* v_e_4650_, lean_object* v_a_4651_, lean_object* v_a_4652_, lean_object* v_a_4653_, lean_object* v_a_4654_, lean_object* v_a_4655_, lean_object* v_a_4656_, lean_object* v_a_4657_, lean_object* v_a_4658_, lean_object* v_a_4659_, lean_object* v_a_4660_, lean_object* v_a_4661_){
_start:
{
lean_object* v_res_4662_; 
v_res_4662_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f(v_e_4650_, v_a_4651_, v_a_4652_, v_a_4653_, v_a_4654_, v_a_4655_, v_a_4656_, v_a_4657_, v_a_4658_, v_a_4659_, v_a_4660_);
lean_dec(v_a_4660_);
lean_dec_ref(v_a_4659_);
lean_dec(v_a_4658_);
lean_dec_ref(v_a_4657_);
lean_dec(v_a_4656_);
lean_dec_ref(v_a_4655_);
lean_dec(v_a_4654_);
lean_dec_ref(v_a_4653_);
lean_dec(v_a_4652_);
lean_dec(v_a_4651_);
lean_dec_ref(v_e_4650_);
return v_res_4662_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__8(void){
_start:
{
uint8_t v___x_4687_; lean_object* v___x_4688_; lean_object* v___x_4689_; 
v___x_4687_ = 0;
v___x_4688_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4);
v___x_4689_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4689_, 0, v___x_4688_);
lean_ctor_set_uint8(v___x_4689_, sizeof(void*)*1, v___x_4687_);
return v___x_4689_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__10(void){
_start:
{
lean_object* v___x_4691_; lean_object* v___x_4692_; 
v___x_4691_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__9));
v___x_4692_ = l_Lean_stringToMessageData(v___x_4691_);
return v___x_4692_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go(lean_object* v_a_4693_, lean_object* v_b_4694_, lean_object* v_h_4695_, lean_object* v_a_4696_, lean_object* v_a_4697_, lean_object* v_a_4698_, lean_object* v_a_4699_, lean_object* v_a_4700_, lean_object* v_a_4701_, lean_object* v_a_4702_, lean_object* v_a_4703_, lean_object* v_a_4704_, lean_object* v_a_4705_){
_start:
{
lean_object* v___y_4708_; lean_object* v___y_4709_; lean_object* v___y_4710_; lean_object* v___y_4711_; lean_object* v___y_4712_; lean_object* v___y_4713_; lean_object* v___y_4714_; lean_object* v___y_4715_; lean_object* v___y_4716_; lean_object* v___y_4717_; lean_object* v___y_4718_; lean_object* v___x_4806_; 
v___x_4806_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___redArg(v_a_4693_, v_a_4696_, v_a_4704_);
if (lean_obj_tag(v___x_4806_) == 0)
{
lean_object* v_a_4807_; lean_object* v___x_4809_; uint8_t v_isShared_4810_; uint8_t v_isSharedCheck_4853_; 
v_a_4807_ = lean_ctor_get(v___x_4806_, 0);
v_isSharedCheck_4853_ = !lean_is_exclusive(v___x_4806_);
if (v_isSharedCheck_4853_ == 0)
{
v___x_4809_ = v___x_4806_;
v_isShared_4810_ = v_isSharedCheck_4853_;
goto v_resetjp_4808_;
}
else
{
lean_inc(v_a_4807_);
lean_dec(v___x_4806_);
v___x_4809_ = lean_box(0);
v_isShared_4810_ = v_isSharedCheck_4853_;
goto v_resetjp_4808_;
}
v_resetjp_4808_:
{
if (lean_obj_tag(v_a_4807_) == 1)
{
lean_object* v_val_4811_; lean_object* v___x_4812_; 
lean_del_object(v___x_4809_);
v_val_4811_ = lean_ctor_get(v_a_4807_, 0);
lean_inc(v_val_4811_);
lean_dec_ref_known(v_a_4807_, 1);
v___x_4812_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___redArg(v_b_4694_, v_a_4696_, v_a_4704_);
if (lean_obj_tag(v___x_4812_) == 0)
{
lean_object* v_a_4813_; lean_object* v___x_4815_; uint8_t v_isShared_4816_; uint8_t v_isSharedCheck_4840_; 
v_a_4813_ = lean_ctor_get(v___x_4812_, 0);
v_isSharedCheck_4840_ = !lean_is_exclusive(v___x_4812_);
if (v_isSharedCheck_4840_ == 0)
{
v___x_4815_ = v___x_4812_;
v_isShared_4816_ = v_isSharedCheck_4840_;
goto v_resetjp_4814_;
}
else
{
lean_inc(v_a_4813_);
lean_dec(v___x_4812_);
v___x_4815_ = lean_box(0);
v_isShared_4816_ = v_isSharedCheck_4840_;
goto v_resetjp_4814_;
}
v_resetjp_4814_:
{
if (lean_obj_tag(v_a_4813_) == 1)
{
lean_object* v_val_4817_; uint8_t v___x_4818_; 
v_val_4817_ = lean_ctor_get(v_a_4813_, 0);
lean_inc(v_val_4817_);
lean_dec_ref_known(v_a_4813_, 1);
v___x_4818_ = lean_nat_dec_eq(v_val_4811_, v_val_4817_);
lean_dec(v_val_4817_);
if (v___x_4818_ == 0)
{
lean_object* v___x_4819_; lean_object* v___x_4821_; 
lean_dec(v_val_4811_);
lean_dec_ref(v_h_4695_);
lean_dec_ref(v_b_4694_);
lean_dec_ref(v_a_4693_);
v___x_4819_ = lean_box(0);
if (v_isShared_4816_ == 0)
{
lean_ctor_set(v___x_4815_, 0, v___x_4819_);
v___x_4821_ = v___x_4815_;
goto v_reusejp_4820_;
}
else
{
lean_object* v_reuseFailAlloc_4822_; 
v_reuseFailAlloc_4822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4822_, 0, v___x_4819_);
v___x_4821_ = v_reuseFailAlloc_4822_;
goto v_reusejp_4820_;
}
v_reusejp_4820_:
{
return v___x_4821_;
}
}
else
{
lean_object* v_toCold_4823_; lean_object* v_options_4824_; uint8_t v_hasTrace_4825_; 
lean_del_object(v___x_4815_);
v_toCold_4823_ = lean_ctor_get(v_a_4704_, 0);
v_options_4824_ = lean_ctor_get(v_toCold_4823_, 2);
v_hasTrace_4825_ = lean_ctor_get_uint8(v_options_4824_, sizeof(void*)*1);
if (v_hasTrace_4825_ == 0)
{
v___y_4708_ = v_val_4811_;
v___y_4709_ = v_a_4696_;
v___y_4710_ = v_a_4697_;
v___y_4711_ = v_a_4698_;
v___y_4712_ = v_a_4699_;
v___y_4713_ = v_a_4700_;
v___y_4714_ = v_a_4701_;
v___y_4715_ = v_a_4702_;
v___y_4716_ = v_a_4703_;
v___y_4717_ = v_a_4704_;
v___y_4718_ = v_a_4705_;
goto v___jp_4707_;
}
else
{
lean_object* v_inheritedTraceOptions_4826_; lean_object* v___x_4827_; lean_object* v___x_4828_; uint8_t v___x_4829_; 
v_inheritedTraceOptions_4826_ = lean_ctor_get(v_toCold_4823_, 11);
v___x_4827_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__4));
v___x_4828_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__5);
v___x_4829_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4826_, v_options_4824_, v___x_4828_);
if (v___x_4829_ == 0)
{
v___y_4708_ = v_val_4811_;
v___y_4709_ = v_a_4696_;
v___y_4710_ = v_a_4697_;
v___y_4711_ = v_a_4698_;
v___y_4712_ = v_a_4699_;
v___y_4713_ = v_a_4700_;
v___y_4714_ = v_a_4701_;
v___y_4715_ = v_a_4702_;
v___y_4716_ = v_a_4703_;
v___y_4717_ = v_a_4704_;
v___y_4718_ = v_a_4705_;
goto v___jp_4707_;
}
else
{
lean_object* v___x_4830_; lean_object* v___x_4831_; lean_object* v___x_4832_; lean_object* v___x_4833_; lean_object* v___x_4834_; lean_object* v___x_4835_; 
lean_inc_ref(v_a_4693_);
v___x_4830_ = l_Lean_MessageData_ofExpr(v_a_4693_);
v___x_4831_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__10, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__10);
v___x_4832_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4832_, 0, v___x_4830_);
lean_ctor_set(v___x_4832_, 1, v___x_4831_);
lean_inc_ref(v_b_4694_);
v___x_4833_ = l_Lean_MessageData_ofExpr(v_b_4694_);
v___x_4834_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4834_, 0, v___x_4832_);
lean_ctor_set(v___x_4834_, 1, v___x_4833_);
v___x_4835_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(v___x_4827_, v___x_4834_, v_a_4702_, v_a_4703_, v_a_4704_, v_a_4705_);
if (lean_obj_tag(v___x_4835_) == 0)
{
lean_dec_ref_known(v___x_4835_, 1);
v___y_4708_ = v_val_4811_;
v___y_4709_ = v_a_4696_;
v___y_4710_ = v_a_4697_;
v___y_4711_ = v_a_4698_;
v___y_4712_ = v_a_4699_;
v___y_4713_ = v_a_4700_;
v___y_4714_ = v_a_4701_;
v___y_4715_ = v_a_4702_;
v___y_4716_ = v_a_4703_;
v___y_4717_ = v_a_4704_;
v___y_4718_ = v_a_4705_;
goto v___jp_4707_;
}
else
{
lean_dec(v_val_4811_);
lean_dec_ref(v_h_4695_);
lean_dec_ref(v_b_4694_);
lean_dec_ref(v_a_4693_);
return v___x_4835_;
}
}
}
}
}
else
{
lean_object* v___x_4836_; lean_object* v___x_4838_; 
lean_dec(v_a_4813_);
lean_dec(v_val_4811_);
lean_dec_ref(v_h_4695_);
lean_dec_ref(v_b_4694_);
lean_dec_ref(v_a_4693_);
v___x_4836_ = lean_box(0);
if (v_isShared_4816_ == 0)
{
lean_ctor_set(v___x_4815_, 0, v___x_4836_);
v___x_4838_ = v___x_4815_;
goto v_reusejp_4837_;
}
else
{
lean_object* v_reuseFailAlloc_4839_; 
v_reuseFailAlloc_4839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4839_, 0, v___x_4836_);
v___x_4838_ = v_reuseFailAlloc_4839_;
goto v_reusejp_4837_;
}
v_reusejp_4837_:
{
return v___x_4838_;
}
}
}
}
else
{
lean_object* v_a_4841_; lean_object* v___x_4843_; uint8_t v_isShared_4844_; uint8_t v_isSharedCheck_4848_; 
lean_dec(v_val_4811_);
lean_dec_ref(v_h_4695_);
lean_dec_ref(v_b_4694_);
lean_dec_ref(v_a_4693_);
v_a_4841_ = lean_ctor_get(v___x_4812_, 0);
v_isSharedCheck_4848_ = !lean_is_exclusive(v___x_4812_);
if (v_isSharedCheck_4848_ == 0)
{
v___x_4843_ = v___x_4812_;
v_isShared_4844_ = v_isSharedCheck_4848_;
goto v_resetjp_4842_;
}
else
{
lean_inc(v_a_4841_);
lean_dec(v___x_4812_);
v___x_4843_ = lean_box(0);
v_isShared_4844_ = v_isSharedCheck_4848_;
goto v_resetjp_4842_;
}
v_resetjp_4842_:
{
lean_object* v___x_4846_; 
if (v_isShared_4844_ == 0)
{
v___x_4846_ = v___x_4843_;
goto v_reusejp_4845_;
}
else
{
lean_object* v_reuseFailAlloc_4847_; 
v_reuseFailAlloc_4847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4847_, 0, v_a_4841_);
v___x_4846_ = v_reuseFailAlloc_4847_;
goto v_reusejp_4845_;
}
v_reusejp_4845_:
{
return v___x_4846_;
}
}
}
}
else
{
lean_object* v___x_4849_; lean_object* v___x_4851_; 
lean_dec(v_a_4807_);
lean_dec_ref(v_h_4695_);
lean_dec_ref(v_b_4694_);
lean_dec_ref(v_a_4693_);
v___x_4849_ = lean_box(0);
if (v_isShared_4810_ == 0)
{
lean_ctor_set(v___x_4809_, 0, v___x_4849_);
v___x_4851_ = v___x_4809_;
goto v_reusejp_4850_;
}
else
{
lean_object* v_reuseFailAlloc_4852_; 
v_reuseFailAlloc_4852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4852_, 0, v___x_4849_);
v___x_4851_ = v_reuseFailAlloc_4852_;
goto v_reusejp_4850_;
}
v_reusejp_4850_:
{
return v___x_4851_;
}
}
}
}
else
{
lean_object* v_a_4854_; lean_object* v___x_4856_; uint8_t v_isShared_4857_; uint8_t v_isSharedCheck_4861_; 
lean_dec_ref(v_h_4695_);
lean_dec_ref(v_b_4694_);
lean_dec_ref(v_a_4693_);
v_a_4854_ = lean_ctor_get(v___x_4806_, 0);
v_isSharedCheck_4861_ = !lean_is_exclusive(v___x_4806_);
if (v_isSharedCheck_4861_ == 0)
{
v___x_4856_ = v___x_4806_;
v_isShared_4857_ = v_isSharedCheck_4861_;
goto v_resetjp_4855_;
}
else
{
lean_inc(v_a_4854_);
lean_dec(v___x_4806_);
v___x_4856_ = lean_box(0);
v_isShared_4857_ = v_isSharedCheck_4861_;
goto v_resetjp_4855_;
}
v_resetjp_4855_:
{
lean_object* v___x_4859_; 
if (v_isShared_4857_ == 0)
{
v___x_4859_ = v___x_4856_;
goto v_reusejp_4858_;
}
else
{
lean_object* v_reuseFailAlloc_4860_; 
v_reuseFailAlloc_4860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4860_, 0, v_a_4854_);
v___x_4859_ = v_reuseFailAlloc_4860_;
goto v_reusejp_4858_;
}
v_reusejp_4858_:
{
return v___x_4859_;
}
}
}
v___jp_4707_:
{
lean_object* v___x_4719_; 
lean_inc_ref(v_a_4693_);
v___x_4719_ = l_Lean_Meta_Grind_Order_getNodeId___redArg(v_a_4693_, v___y_4708_, v___y_4709_, v___y_4715_, v___y_4716_, v___y_4717_, v___y_4718_);
if (lean_obj_tag(v___x_4719_) == 0)
{
lean_object* v_a_4720_; lean_object* v___x_4721_; 
v_a_4720_ = lean_ctor_get(v___x_4719_, 0);
lean_inc(v_a_4720_);
lean_dec_ref_known(v___x_4719_, 1);
lean_inc_ref(v_b_4694_);
v___x_4721_ = l_Lean_Meta_Grind_Order_getNodeId___redArg(v_b_4694_, v___y_4708_, v___y_4709_, v___y_4715_, v___y_4716_, v___y_4717_, v___y_4718_);
if (lean_obj_tag(v___x_4721_) == 0)
{
lean_object* v_a_4722_; lean_object* v___x_4723_; 
v_a_4722_ = lean_ctor_get(v___x_4721_, 0);
lean_inc(v_a_4722_);
lean_dec_ref_known(v___x_4721_, 1);
v___x_4723_ = l_Lean_Meta_Grind_Order_isRing(v___y_4708_, v___y_4709_, v___y_4710_, v___y_4711_, v___y_4712_, v___y_4713_, v___y_4714_, v___y_4715_, v___y_4716_, v___y_4717_, v___y_4718_);
if (lean_obj_tag(v___x_4723_) == 0)
{
lean_object* v_a_4724_; uint8_t v___x_4725_; 
v_a_4724_ = lean_ctor_get(v___x_4723_, 0);
lean_inc(v_a_4724_);
lean_dec_ref_known(v___x_4723_, 1);
v___x_4725_ = lean_unbox(v_a_4724_);
if (v___x_4725_ == 0)
{
lean_object* v___x_4726_; lean_object* v___x_4727_; 
v___x_4726_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__1));
v___x_4727_ = l_Lean_Meta_Grind_Order_mkLePreorderPrefix(v___x_4726_, v___y_4708_, v___y_4709_, v___y_4710_, v___y_4711_, v___y_4712_, v___y_4713_, v___y_4714_, v___y_4715_, v___y_4716_, v___y_4717_, v___y_4718_);
if (lean_obj_tag(v___x_4727_) == 0)
{
lean_object* v_a_4728_; lean_object* v___x_4729_; lean_object* v___x_4730_; lean_object* v___x_4731_; 
v_a_4728_ = lean_ctor_get(v___x_4727_, 0);
lean_inc(v_a_4728_);
lean_dec_ref_known(v___x_4727_, 1);
lean_inc_ref(v_h_4695_);
lean_inc_ref(v_b_4694_);
lean_inc_ref(v_a_4693_);
v___x_4729_ = l_Lean_mkApp3(v_a_4728_, v_a_4693_, v_b_4694_, v_h_4695_);
v___x_4730_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__3));
v___x_4731_ = l_Lean_Meta_Grind_Order_mkLePreorderPrefix(v___x_4730_, v___y_4708_, v___y_4709_, v___y_4710_, v___y_4711_, v___y_4712_, v___y_4713_, v___y_4714_, v___y_4715_, v___y_4716_, v___y_4717_, v___y_4718_);
if (lean_obj_tag(v___x_4731_) == 0)
{
lean_object* v_a_4732_; lean_object* v___x_4733_; lean_object* v___x_4734_; lean_object* v___x_4735_; uint8_t v___x_4736_; lean_object* v___x_4737_; 
v_a_4732_ = lean_ctor_get(v___x_4731_, 0);
lean_inc(v_a_4732_);
lean_dec_ref_known(v___x_4731_, 1);
v___x_4733_ = l_Lean_mkApp3(v_a_4732_, v_a_4693_, v_b_4694_, v_h_4695_);
v___x_4734_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4);
v___x_4735_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4735_, 0, v___x_4734_);
v___x_4736_ = lean_unbox(v_a_4724_);
lean_dec(v_a_4724_);
lean_ctor_set_uint8(v___x_4735_, sizeof(void*)*1, v___x_4736_);
lean_inc_ref(v___x_4735_);
lean_inc(v_a_4722_);
lean_inc(v_a_4720_);
v___x_4737_ = l_Lean_Meta_Grind_Order_addEdge(v_a_4720_, v_a_4722_, v___x_4735_, v___x_4729_, v___y_4708_, v___y_4709_, v___y_4710_, v___y_4711_, v___y_4712_, v___y_4713_, v___y_4714_, v___y_4715_, v___y_4716_, v___y_4717_, v___y_4718_);
if (lean_obj_tag(v___x_4737_) == 0)
{
lean_object* v___x_4738_; 
lean_dec_ref_known(v___x_4737_, 1);
v___x_4738_ = l_Lean_Meta_Grind_Order_addEdge(v_a_4722_, v_a_4720_, v___x_4735_, v___x_4733_, v___y_4708_, v___y_4709_, v___y_4710_, v___y_4711_, v___y_4712_, v___y_4713_, v___y_4714_, v___y_4715_, v___y_4716_, v___y_4717_, v___y_4718_);
lean_dec(v___y_4708_);
return v___x_4738_;
}
else
{
lean_dec_ref_known(v___x_4735_, 1);
lean_dec_ref(v___x_4733_);
lean_dec(v_a_4722_);
lean_dec(v_a_4720_);
lean_dec(v___y_4708_);
return v___x_4737_;
}
}
else
{
lean_object* v_a_4739_; lean_object* v___x_4741_; uint8_t v_isShared_4742_; uint8_t v_isSharedCheck_4746_; 
lean_dec_ref(v___x_4729_);
lean_dec(v_a_4724_);
lean_dec(v_a_4722_);
lean_dec(v_a_4720_);
lean_dec(v___y_4708_);
lean_dec_ref(v_h_4695_);
lean_dec_ref(v_b_4694_);
lean_dec_ref(v_a_4693_);
v_a_4739_ = lean_ctor_get(v___x_4731_, 0);
v_isSharedCheck_4746_ = !lean_is_exclusive(v___x_4731_);
if (v_isSharedCheck_4746_ == 0)
{
v___x_4741_ = v___x_4731_;
v_isShared_4742_ = v_isSharedCheck_4746_;
goto v_resetjp_4740_;
}
else
{
lean_inc(v_a_4739_);
lean_dec(v___x_4731_);
v___x_4741_ = lean_box(0);
v_isShared_4742_ = v_isSharedCheck_4746_;
goto v_resetjp_4740_;
}
v_resetjp_4740_:
{
lean_object* v___x_4744_; 
if (v_isShared_4742_ == 0)
{
v___x_4744_ = v___x_4741_;
goto v_reusejp_4743_;
}
else
{
lean_object* v_reuseFailAlloc_4745_; 
v_reuseFailAlloc_4745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4745_, 0, v_a_4739_);
v___x_4744_ = v_reuseFailAlloc_4745_;
goto v_reusejp_4743_;
}
v_reusejp_4743_:
{
return v___x_4744_;
}
}
}
}
else
{
lean_object* v_a_4747_; lean_object* v___x_4749_; uint8_t v_isShared_4750_; uint8_t v_isSharedCheck_4754_; 
lean_dec(v_a_4724_);
lean_dec(v_a_4722_);
lean_dec(v_a_4720_);
lean_dec(v___y_4708_);
lean_dec_ref(v_h_4695_);
lean_dec_ref(v_b_4694_);
lean_dec_ref(v_a_4693_);
v_a_4747_ = lean_ctor_get(v___x_4727_, 0);
v_isSharedCheck_4754_ = !lean_is_exclusive(v___x_4727_);
if (v_isSharedCheck_4754_ == 0)
{
v___x_4749_ = v___x_4727_;
v_isShared_4750_ = v_isSharedCheck_4754_;
goto v_resetjp_4748_;
}
else
{
lean_inc(v_a_4747_);
lean_dec(v___x_4727_);
v___x_4749_ = lean_box(0);
v_isShared_4750_ = v_isSharedCheck_4754_;
goto v_resetjp_4748_;
}
v_resetjp_4748_:
{
lean_object* v___x_4752_; 
if (v_isShared_4750_ == 0)
{
v___x_4752_ = v___x_4749_;
goto v_reusejp_4751_;
}
else
{
lean_object* v_reuseFailAlloc_4753_; 
v_reuseFailAlloc_4753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4753_, 0, v_a_4747_);
v___x_4752_ = v_reuseFailAlloc_4753_;
goto v_reusejp_4751_;
}
v_reusejp_4751_:
{
return v___x_4752_;
}
}
}
}
else
{
lean_object* v___x_4755_; lean_object* v___x_4756_; 
lean_dec(v_a_4724_);
v___x_4755_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__5));
v___x_4756_ = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(v___x_4755_, v___y_4708_, v___y_4709_, v___y_4710_, v___y_4711_, v___y_4712_, v___y_4713_, v___y_4714_, v___y_4715_, v___y_4716_, v___y_4717_, v___y_4718_);
if (lean_obj_tag(v___x_4756_) == 0)
{
lean_object* v_a_4757_; lean_object* v___x_4758_; lean_object* v___x_4759_; lean_object* v___x_4760_; 
v_a_4757_ = lean_ctor_get(v___x_4756_, 0);
lean_inc(v_a_4757_);
lean_dec_ref_known(v___x_4756_, 1);
lean_inc_ref(v_h_4695_);
lean_inc_ref(v_b_4694_);
lean_inc_ref(v_a_4693_);
v___x_4758_ = l_Lean_mkApp3(v_a_4757_, v_a_4693_, v_b_4694_, v_h_4695_);
v___x_4759_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__7));
v___x_4760_ = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(v___x_4759_, v___y_4708_, v___y_4709_, v___y_4710_, v___y_4711_, v___y_4712_, v___y_4713_, v___y_4714_, v___y_4715_, v___y_4716_, v___y_4717_, v___y_4718_);
if (lean_obj_tag(v___x_4760_) == 0)
{
lean_object* v_a_4761_; lean_object* v___x_4762_; lean_object* v___x_4763_; lean_object* v___x_4764_; 
v_a_4761_ = lean_ctor_get(v___x_4760_, 0);
lean_inc(v_a_4761_);
lean_dec_ref_known(v___x_4760_, 1);
v___x_4762_ = l_Lean_mkApp3(v_a_4761_, v_a_4693_, v_b_4694_, v_h_4695_);
v___x_4763_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__8, &l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__8);
lean_inc(v_a_4722_);
lean_inc(v_a_4720_);
v___x_4764_ = l_Lean_Meta_Grind_Order_addEdge(v_a_4720_, v_a_4722_, v___x_4763_, v___x_4758_, v___y_4708_, v___y_4709_, v___y_4710_, v___y_4711_, v___y_4712_, v___y_4713_, v___y_4714_, v___y_4715_, v___y_4716_, v___y_4717_, v___y_4718_);
if (lean_obj_tag(v___x_4764_) == 0)
{
lean_object* v___x_4765_; 
lean_dec_ref_known(v___x_4764_, 1);
v___x_4765_ = l_Lean_Meta_Grind_Order_addEdge(v_a_4722_, v_a_4720_, v___x_4763_, v___x_4762_, v___y_4708_, v___y_4709_, v___y_4710_, v___y_4711_, v___y_4712_, v___y_4713_, v___y_4714_, v___y_4715_, v___y_4716_, v___y_4717_, v___y_4718_);
lean_dec(v___y_4708_);
return v___x_4765_;
}
else
{
lean_dec_ref(v___x_4762_);
lean_dec(v_a_4722_);
lean_dec(v_a_4720_);
lean_dec(v___y_4708_);
return v___x_4764_;
}
}
else
{
lean_object* v_a_4766_; lean_object* v___x_4768_; uint8_t v_isShared_4769_; uint8_t v_isSharedCheck_4773_; 
lean_dec_ref(v___x_4758_);
lean_dec(v_a_4722_);
lean_dec(v_a_4720_);
lean_dec(v___y_4708_);
lean_dec_ref(v_h_4695_);
lean_dec_ref(v_b_4694_);
lean_dec_ref(v_a_4693_);
v_a_4766_ = lean_ctor_get(v___x_4760_, 0);
v_isSharedCheck_4773_ = !lean_is_exclusive(v___x_4760_);
if (v_isSharedCheck_4773_ == 0)
{
v___x_4768_ = v___x_4760_;
v_isShared_4769_ = v_isSharedCheck_4773_;
goto v_resetjp_4767_;
}
else
{
lean_inc(v_a_4766_);
lean_dec(v___x_4760_);
v___x_4768_ = lean_box(0);
v_isShared_4769_ = v_isSharedCheck_4773_;
goto v_resetjp_4767_;
}
v_resetjp_4767_:
{
lean_object* v___x_4771_; 
if (v_isShared_4769_ == 0)
{
v___x_4771_ = v___x_4768_;
goto v_reusejp_4770_;
}
else
{
lean_object* v_reuseFailAlloc_4772_; 
v_reuseFailAlloc_4772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4772_, 0, v_a_4766_);
v___x_4771_ = v_reuseFailAlloc_4772_;
goto v_reusejp_4770_;
}
v_reusejp_4770_:
{
return v___x_4771_;
}
}
}
}
else
{
lean_object* v_a_4774_; lean_object* v___x_4776_; uint8_t v_isShared_4777_; uint8_t v_isSharedCheck_4781_; 
lean_dec(v_a_4722_);
lean_dec(v_a_4720_);
lean_dec(v___y_4708_);
lean_dec_ref(v_h_4695_);
lean_dec_ref(v_b_4694_);
lean_dec_ref(v_a_4693_);
v_a_4774_ = lean_ctor_get(v___x_4756_, 0);
v_isSharedCheck_4781_ = !lean_is_exclusive(v___x_4756_);
if (v_isSharedCheck_4781_ == 0)
{
v___x_4776_ = v___x_4756_;
v_isShared_4777_ = v_isSharedCheck_4781_;
goto v_resetjp_4775_;
}
else
{
lean_inc(v_a_4774_);
lean_dec(v___x_4756_);
v___x_4776_ = lean_box(0);
v_isShared_4777_ = v_isSharedCheck_4781_;
goto v_resetjp_4775_;
}
v_resetjp_4775_:
{
lean_object* v___x_4779_; 
if (v_isShared_4777_ == 0)
{
v___x_4779_ = v___x_4776_;
goto v_reusejp_4778_;
}
else
{
lean_object* v_reuseFailAlloc_4780_; 
v_reuseFailAlloc_4780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4780_, 0, v_a_4774_);
v___x_4779_ = v_reuseFailAlloc_4780_;
goto v_reusejp_4778_;
}
v_reusejp_4778_:
{
return v___x_4779_;
}
}
}
}
}
else
{
lean_object* v_a_4782_; lean_object* v___x_4784_; uint8_t v_isShared_4785_; uint8_t v_isSharedCheck_4789_; 
lean_dec(v_a_4722_);
lean_dec(v_a_4720_);
lean_dec(v___y_4708_);
lean_dec_ref(v_h_4695_);
lean_dec_ref(v_b_4694_);
lean_dec_ref(v_a_4693_);
v_a_4782_ = lean_ctor_get(v___x_4723_, 0);
v_isSharedCheck_4789_ = !lean_is_exclusive(v___x_4723_);
if (v_isSharedCheck_4789_ == 0)
{
v___x_4784_ = v___x_4723_;
v_isShared_4785_ = v_isSharedCheck_4789_;
goto v_resetjp_4783_;
}
else
{
lean_inc(v_a_4782_);
lean_dec(v___x_4723_);
v___x_4784_ = lean_box(0);
v_isShared_4785_ = v_isSharedCheck_4789_;
goto v_resetjp_4783_;
}
v_resetjp_4783_:
{
lean_object* v___x_4787_; 
if (v_isShared_4785_ == 0)
{
v___x_4787_ = v___x_4784_;
goto v_reusejp_4786_;
}
else
{
lean_object* v_reuseFailAlloc_4788_; 
v_reuseFailAlloc_4788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4788_, 0, v_a_4782_);
v___x_4787_ = v_reuseFailAlloc_4788_;
goto v_reusejp_4786_;
}
v_reusejp_4786_:
{
return v___x_4787_;
}
}
}
}
else
{
lean_object* v_a_4790_; lean_object* v___x_4792_; uint8_t v_isShared_4793_; uint8_t v_isSharedCheck_4797_; 
lean_dec(v_a_4720_);
lean_dec(v___y_4708_);
lean_dec_ref(v_h_4695_);
lean_dec_ref(v_b_4694_);
lean_dec_ref(v_a_4693_);
v_a_4790_ = lean_ctor_get(v___x_4721_, 0);
v_isSharedCheck_4797_ = !lean_is_exclusive(v___x_4721_);
if (v_isSharedCheck_4797_ == 0)
{
v___x_4792_ = v___x_4721_;
v_isShared_4793_ = v_isSharedCheck_4797_;
goto v_resetjp_4791_;
}
else
{
lean_inc(v_a_4790_);
lean_dec(v___x_4721_);
v___x_4792_ = lean_box(0);
v_isShared_4793_ = v_isSharedCheck_4797_;
goto v_resetjp_4791_;
}
v_resetjp_4791_:
{
lean_object* v___x_4795_; 
if (v_isShared_4793_ == 0)
{
v___x_4795_ = v___x_4792_;
goto v_reusejp_4794_;
}
else
{
lean_object* v_reuseFailAlloc_4796_; 
v_reuseFailAlloc_4796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4796_, 0, v_a_4790_);
v___x_4795_ = v_reuseFailAlloc_4796_;
goto v_reusejp_4794_;
}
v_reusejp_4794_:
{
return v___x_4795_;
}
}
}
}
else
{
lean_object* v_a_4798_; lean_object* v___x_4800_; uint8_t v_isShared_4801_; uint8_t v_isSharedCheck_4805_; 
lean_dec(v___y_4708_);
lean_dec_ref(v_h_4695_);
lean_dec_ref(v_b_4694_);
lean_dec_ref(v_a_4693_);
v_a_4798_ = lean_ctor_get(v___x_4719_, 0);
v_isSharedCheck_4805_ = !lean_is_exclusive(v___x_4719_);
if (v_isSharedCheck_4805_ == 0)
{
v___x_4800_ = v___x_4719_;
v_isShared_4801_ = v_isSharedCheck_4805_;
goto v_resetjp_4799_;
}
else
{
lean_inc(v_a_4798_);
lean_dec(v___x_4719_);
v___x_4800_ = lean_box(0);
v_isShared_4801_ = v_isSharedCheck_4805_;
goto v_resetjp_4799_;
}
v_resetjp_4799_:
{
lean_object* v___x_4803_; 
if (v_isShared_4801_ == 0)
{
v___x_4803_ = v___x_4800_;
goto v_reusejp_4802_;
}
else
{
lean_object* v_reuseFailAlloc_4804_; 
v_reuseFailAlloc_4804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4804_, 0, v_a_4798_);
v___x_4803_ = v_reuseFailAlloc_4804_;
goto v_reusejp_4802_;
}
v_reusejp_4802_:
{
return v___x_4803_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___boxed(lean_object* v_a_4862_, lean_object* v_b_4863_, lean_object* v_h_4864_, lean_object* v_a_4865_, lean_object* v_a_4866_, lean_object* v_a_4867_, lean_object* v_a_4868_, lean_object* v_a_4869_, lean_object* v_a_4870_, lean_object* v_a_4871_, lean_object* v_a_4872_, lean_object* v_a_4873_, lean_object* v_a_4874_, lean_object* v_a_4875_){
_start:
{
lean_object* v_res_4876_; 
v_res_4876_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go(v_a_4862_, v_b_4863_, v_h_4864_, v_a_4865_, v_a_4866_, v_a_4867_, v_a_4868_, v_a_4869_, v_a_4870_, v_a_4871_, v_a_4872_, v_a_4873_, v_a_4874_);
lean_dec(v_a_4874_);
lean_dec_ref(v_a_4873_);
lean_dec(v_a_4872_);
lean_dec_ref(v_a_4871_);
lean_dec(v_a_4870_);
lean_dec_ref(v_a_4869_);
lean_dec(v_a_4868_);
lean_dec_ref(v_a_4867_);
lean_dec(v_a_4866_);
lean_dec(v_a_4865_);
return v_res_4876_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_processNewEq___closed__6(void){
_start:
{
lean_object* v___x_4892_; lean_object* v___x_4893_; lean_object* v___x_4894_; 
v___x_4892_ = lean_box(0);
v___x_4893_ = ((lean_object*)(l_Lean_Meta_Grind_Order_processNewEq___closed__5));
v___x_4894_ = l_Lean_mkConst(v___x_4893_, v___x_4892_);
return v___x_4894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_processNewEq(lean_object* v_a_4895_, lean_object* v_b_4896_, lean_object* v_a_4897_, lean_object* v_a_4898_, lean_object* v_a_4899_, lean_object* v_a_4900_, lean_object* v_a_4901_, lean_object* v_a_4902_, lean_object* v_a_4903_, lean_object* v_a_4904_, lean_object* v_a_4905_, lean_object* v_a_4906_){
_start:
{
size_t v___x_4908_; size_t v___x_4909_; uint8_t v___x_4910_; 
v___x_4908_ = lean_ptr_addr(v_a_4895_);
v___x_4909_ = lean_ptr_addr(v_b_4896_);
v___x_4910_ = lean_usize_dec_eq(v___x_4908_, v___x_4909_);
if (v___x_4910_ == 0)
{
lean_object* v___x_4911_; 
lean_inc(v_a_4906_);
lean_inc_ref(v_a_4905_);
lean_inc(v_a_4904_);
lean_inc_ref(v_a_4903_);
lean_inc(v_a_4902_);
lean_inc_ref(v_a_4901_);
lean_inc(v_a_4900_);
lean_inc_ref(v_a_4899_);
lean_inc(v_a_4898_);
lean_inc(v_a_4897_);
lean_inc_ref(v_b_4896_);
lean_inc_ref(v_a_4895_);
v___x_4911_ = lean_grind_mk_eq_proof(v_a_4895_, v_b_4896_, v_a_4897_, v_a_4898_, v_a_4899_, v_a_4900_, v_a_4901_, v_a_4902_, v_a_4903_, v_a_4904_, v_a_4905_, v_a_4906_);
if (lean_obj_tag(v___x_4911_) == 0)
{
lean_object* v_a_4912_; lean_object* v___x_4913_; 
v_a_4912_ = lean_ctor_get(v___x_4911_, 0);
lean_inc(v_a_4912_);
lean_dec_ref_known(v___x_4911_, 1);
v___x_4913_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f___redArg(v_a_4895_, v_a_4897_, v_a_4905_);
if (lean_obj_tag(v___x_4913_) == 0)
{
lean_object* v_a_4914_; 
v_a_4914_ = lean_ctor_get(v___x_4913_, 0);
lean_inc(v_a_4914_);
lean_dec_ref_known(v___x_4913_, 1);
if (lean_obj_tag(v_a_4914_) == 1)
{
lean_object* v_val_4915_; lean_object* v_e_4916_; lean_object* v_h_4917_; lean_object* v_00_u03b1_4918_; lean_object* v___x_4919_; 
v_val_4915_ = lean_ctor_get(v_a_4914_, 0);
lean_inc(v_val_4915_);
lean_dec_ref_known(v_a_4914_, 1);
v_e_4916_ = lean_ctor_get(v_val_4915_, 0);
lean_inc_ref(v_e_4916_);
v_h_4917_ = lean_ctor_get(v_val_4915_, 1);
lean_inc_ref(v_h_4917_);
v_00_u03b1_4918_ = lean_ctor_get(v_val_4915_, 2);
lean_inc_ref(v_00_u03b1_4918_);
lean_dec(v_val_4915_);
v___x_4919_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f___redArg(v_b_4896_, v_a_4897_, v_a_4905_);
if (lean_obj_tag(v___x_4919_) == 0)
{
lean_object* v_a_4920_; lean_object* v___x_4922_; uint8_t v_isShared_4923_; uint8_t v_isSharedCheck_4965_; 
v_a_4920_ = lean_ctor_get(v___x_4919_, 0);
v_isSharedCheck_4965_ = !lean_is_exclusive(v___x_4919_);
if (v_isSharedCheck_4965_ == 0)
{
v___x_4922_ = v___x_4919_;
v_isShared_4923_ = v_isSharedCheck_4965_;
goto v_resetjp_4921_;
}
else
{
lean_inc(v_a_4920_);
lean_dec(v___x_4919_);
v___x_4922_ = lean_box(0);
v_isShared_4923_ = v_isSharedCheck_4965_;
goto v_resetjp_4921_;
}
v_resetjp_4921_:
{
if (lean_obj_tag(v_a_4920_) == 1)
{
lean_object* v_val_4924_; lean_object* v_e_4925_; lean_object* v_h_4926_; lean_object* v___x_4927_; uint8_t v___x_4928_; 
lean_del_object(v___x_4922_);
v_val_4924_ = lean_ctor_get(v_a_4920_, 0);
lean_inc(v_val_4924_);
lean_dec_ref_known(v_a_4920_, 1);
v_e_4925_ = lean_ctor_get(v_val_4924_, 0);
lean_inc_ref(v_e_4925_);
v_h_4926_ = lean_ctor_get(v_val_4924_, 1);
lean_inc_ref(v_h_4926_);
lean_dec(v_val_4924_);
v___x_4927_ = l_Lean_Int_mkType;
v___x_4928_ = lean_expr_eqv(v_00_u03b1_4918_, v___x_4927_);
if (v___x_4928_ == 0)
{
lean_object* v___x_4929_; 
lean_inc_ref(v_00_u03b1_4918_);
v___x_4929_ = l_Lean_Meta_getDecLevel(v_00_u03b1_4918_, v_a_4903_, v_a_4904_, v_a_4905_, v_a_4906_);
if (lean_obj_tag(v___x_4929_) == 0)
{
lean_object* v_a_4930_; lean_object* v___x_4931_; lean_object* v___x_4932_; lean_object* v___x_4933_; lean_object* v___x_4934_; lean_object* v___x_4935_; lean_object* v___x_4936_; 
v_a_4930_ = lean_ctor_get(v___x_4929_, 0);
lean_inc(v_a_4930_);
lean_dec_ref_known(v___x_4929_, 1);
v___x_4931_ = ((lean_object*)(l_Lean_Meta_Grind_Order_processNewEq___closed__1));
v___x_4932_ = lean_box(0);
v___x_4933_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4933_, 0, v_a_4930_);
lean_ctor_set(v___x_4933_, 1, v___x_4932_);
lean_inc_ref(v___x_4933_);
v___x_4934_ = l_Lean_mkConst(v___x_4931_, v___x_4933_);
lean_inc_ref(v_00_u03b1_4918_);
v___x_4935_ = l_Lean_Expr_app___override(v___x_4934_, v_00_u03b1_4918_);
v___x_4936_ = l_Lean_Meta_Sym_synthInstance(v___x_4935_, v_a_4901_, v_a_4902_, v_a_4903_, v_a_4904_, v_a_4905_, v_a_4906_);
if (lean_obj_tag(v___x_4936_) == 0)
{
lean_object* v_a_4937_; lean_object* v___x_4938_; lean_object* v___x_4939_; lean_object* v___x_4940_; lean_object* v___x_4941_; 
v_a_4937_ = lean_ctor_get(v___x_4936_, 0);
lean_inc(v_a_4937_);
lean_dec_ref_known(v___x_4936_, 1);
v___x_4938_ = ((lean_object*)(l_Lean_Meta_Grind_Order_processNewEq___closed__3));
v___x_4939_ = l_Lean_mkConst(v___x_4938_, v___x_4933_);
lean_inc_ref(v_e_4925_);
lean_inc_ref(v_e_4916_);
v___x_4940_ = l_Lean_mkApp9(v___x_4939_, v_00_u03b1_4918_, v_a_4937_, v_a_4895_, v_b_4896_, v_e_4916_, v_e_4925_, v_h_4917_, v_h_4926_, v_a_4912_);
v___x_4941_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go(v_e_4916_, v_e_4925_, v___x_4940_, v_a_4897_, v_a_4898_, v_a_4899_, v_a_4900_, v_a_4901_, v_a_4902_, v_a_4903_, v_a_4904_, v_a_4905_, v_a_4906_);
return v___x_4941_;
}
else
{
lean_object* v_a_4942_; lean_object* v___x_4944_; uint8_t v_isShared_4945_; uint8_t v_isSharedCheck_4949_; 
lean_dec_ref_known(v___x_4933_, 2);
lean_dec_ref(v_h_4926_);
lean_dec_ref(v_e_4925_);
lean_dec_ref(v_00_u03b1_4918_);
lean_dec_ref(v_h_4917_);
lean_dec_ref(v_e_4916_);
lean_dec(v_a_4912_);
lean_dec_ref(v_b_4896_);
lean_dec_ref(v_a_4895_);
v_a_4942_ = lean_ctor_get(v___x_4936_, 0);
v_isSharedCheck_4949_ = !lean_is_exclusive(v___x_4936_);
if (v_isSharedCheck_4949_ == 0)
{
v___x_4944_ = v___x_4936_;
v_isShared_4945_ = v_isSharedCheck_4949_;
goto v_resetjp_4943_;
}
else
{
lean_inc(v_a_4942_);
lean_dec(v___x_4936_);
v___x_4944_ = lean_box(0);
v_isShared_4945_ = v_isSharedCheck_4949_;
goto v_resetjp_4943_;
}
v_resetjp_4943_:
{
lean_object* v___x_4947_; 
if (v_isShared_4945_ == 0)
{
v___x_4947_ = v___x_4944_;
goto v_reusejp_4946_;
}
else
{
lean_object* v_reuseFailAlloc_4948_; 
v_reuseFailAlloc_4948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4948_, 0, v_a_4942_);
v___x_4947_ = v_reuseFailAlloc_4948_;
goto v_reusejp_4946_;
}
v_reusejp_4946_:
{
return v___x_4947_;
}
}
}
}
else
{
lean_object* v_a_4950_; lean_object* v___x_4952_; uint8_t v_isShared_4953_; uint8_t v_isSharedCheck_4957_; 
lean_dec_ref(v_h_4926_);
lean_dec_ref(v_e_4925_);
lean_dec_ref(v_00_u03b1_4918_);
lean_dec_ref(v_h_4917_);
lean_dec_ref(v_e_4916_);
lean_dec(v_a_4912_);
lean_dec_ref(v_b_4896_);
lean_dec_ref(v_a_4895_);
v_a_4950_ = lean_ctor_get(v___x_4929_, 0);
v_isSharedCheck_4957_ = !lean_is_exclusive(v___x_4929_);
if (v_isSharedCheck_4957_ == 0)
{
v___x_4952_ = v___x_4929_;
v_isShared_4953_ = v_isSharedCheck_4957_;
goto v_resetjp_4951_;
}
else
{
lean_inc(v_a_4950_);
lean_dec(v___x_4929_);
v___x_4952_ = lean_box(0);
v_isShared_4953_ = v_isSharedCheck_4957_;
goto v_resetjp_4951_;
}
v_resetjp_4951_:
{
lean_object* v___x_4955_; 
if (v_isShared_4953_ == 0)
{
v___x_4955_ = v___x_4952_;
goto v_reusejp_4954_;
}
else
{
lean_object* v_reuseFailAlloc_4956_; 
v_reuseFailAlloc_4956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4956_, 0, v_a_4950_);
v___x_4955_ = v_reuseFailAlloc_4956_;
goto v_reusejp_4954_;
}
v_reusejp_4954_:
{
return v___x_4955_;
}
}
}
}
else
{
lean_object* v___x_4958_; lean_object* v___x_4959_; lean_object* v___x_4960_; 
lean_dec_ref(v_00_u03b1_4918_);
v___x_4958_ = lean_obj_once(&l_Lean_Meta_Grind_Order_processNewEq___closed__6, &l_Lean_Meta_Grind_Order_processNewEq___closed__6_once, _init_l_Lean_Meta_Grind_Order_processNewEq___closed__6);
lean_inc_ref(v_e_4925_);
lean_inc_ref(v_e_4916_);
v___x_4959_ = l_Lean_mkApp7(v___x_4958_, v_a_4895_, v_b_4896_, v_e_4916_, v_e_4925_, v_h_4917_, v_h_4926_, v_a_4912_);
v___x_4960_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go(v_e_4916_, v_e_4925_, v___x_4959_, v_a_4897_, v_a_4898_, v_a_4899_, v_a_4900_, v_a_4901_, v_a_4902_, v_a_4903_, v_a_4904_, v_a_4905_, v_a_4906_);
return v___x_4960_;
}
}
else
{
lean_object* v___x_4961_; lean_object* v___x_4963_; 
lean_dec(v_a_4920_);
lean_dec_ref(v_00_u03b1_4918_);
lean_dec_ref(v_h_4917_);
lean_dec_ref(v_e_4916_);
lean_dec(v_a_4912_);
lean_dec_ref(v_b_4896_);
lean_dec_ref(v_a_4895_);
v___x_4961_ = lean_box(0);
if (v_isShared_4923_ == 0)
{
lean_ctor_set(v___x_4922_, 0, v___x_4961_);
v___x_4963_ = v___x_4922_;
goto v_reusejp_4962_;
}
else
{
lean_object* v_reuseFailAlloc_4964_; 
v_reuseFailAlloc_4964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4964_, 0, v___x_4961_);
v___x_4963_ = v_reuseFailAlloc_4964_;
goto v_reusejp_4962_;
}
v_reusejp_4962_:
{
return v___x_4963_;
}
}
}
}
else
{
lean_object* v_a_4966_; lean_object* v___x_4968_; uint8_t v_isShared_4969_; uint8_t v_isSharedCheck_4973_; 
lean_dec_ref(v_00_u03b1_4918_);
lean_dec_ref(v_h_4917_);
lean_dec_ref(v_e_4916_);
lean_dec(v_a_4912_);
lean_dec_ref(v_b_4896_);
lean_dec_ref(v_a_4895_);
v_a_4966_ = lean_ctor_get(v___x_4919_, 0);
v_isSharedCheck_4973_ = !lean_is_exclusive(v___x_4919_);
if (v_isSharedCheck_4973_ == 0)
{
v___x_4968_ = v___x_4919_;
v_isShared_4969_ = v_isSharedCheck_4973_;
goto v_resetjp_4967_;
}
else
{
lean_inc(v_a_4966_);
lean_dec(v___x_4919_);
v___x_4968_ = lean_box(0);
v_isShared_4969_ = v_isSharedCheck_4973_;
goto v_resetjp_4967_;
}
v_resetjp_4967_:
{
lean_object* v___x_4971_; 
if (v_isShared_4969_ == 0)
{
v___x_4971_ = v___x_4968_;
goto v_reusejp_4970_;
}
else
{
lean_object* v_reuseFailAlloc_4972_; 
v_reuseFailAlloc_4972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4972_, 0, v_a_4966_);
v___x_4971_ = v_reuseFailAlloc_4972_;
goto v_reusejp_4970_;
}
v_reusejp_4970_:
{
return v___x_4971_;
}
}
}
}
else
{
lean_object* v___x_4974_; 
lean_dec(v_a_4914_);
v___x_4974_ = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go(v_a_4895_, v_b_4896_, v_a_4912_, v_a_4897_, v_a_4898_, v_a_4899_, v_a_4900_, v_a_4901_, v_a_4902_, v_a_4903_, v_a_4904_, v_a_4905_, v_a_4906_);
return v___x_4974_;
}
}
else
{
lean_object* v_a_4975_; lean_object* v___x_4977_; uint8_t v_isShared_4978_; uint8_t v_isSharedCheck_4982_; 
lean_dec(v_a_4912_);
lean_dec_ref(v_b_4896_);
lean_dec_ref(v_a_4895_);
v_a_4975_ = lean_ctor_get(v___x_4913_, 0);
v_isSharedCheck_4982_ = !lean_is_exclusive(v___x_4913_);
if (v_isSharedCheck_4982_ == 0)
{
v___x_4977_ = v___x_4913_;
v_isShared_4978_ = v_isSharedCheck_4982_;
goto v_resetjp_4976_;
}
else
{
lean_inc(v_a_4975_);
lean_dec(v___x_4913_);
v___x_4977_ = lean_box(0);
v_isShared_4978_ = v_isSharedCheck_4982_;
goto v_resetjp_4976_;
}
v_resetjp_4976_:
{
lean_object* v___x_4980_; 
if (v_isShared_4978_ == 0)
{
v___x_4980_ = v___x_4977_;
goto v_reusejp_4979_;
}
else
{
lean_object* v_reuseFailAlloc_4981_; 
v_reuseFailAlloc_4981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4981_, 0, v_a_4975_);
v___x_4980_ = v_reuseFailAlloc_4981_;
goto v_reusejp_4979_;
}
v_reusejp_4979_:
{
return v___x_4980_;
}
}
}
}
else
{
lean_object* v_a_4983_; lean_object* v___x_4985_; uint8_t v_isShared_4986_; uint8_t v_isSharedCheck_4990_; 
lean_dec_ref(v_b_4896_);
lean_dec_ref(v_a_4895_);
v_a_4983_ = lean_ctor_get(v___x_4911_, 0);
v_isSharedCheck_4990_ = !lean_is_exclusive(v___x_4911_);
if (v_isSharedCheck_4990_ == 0)
{
v___x_4985_ = v___x_4911_;
v_isShared_4986_ = v_isSharedCheck_4990_;
goto v_resetjp_4984_;
}
else
{
lean_inc(v_a_4983_);
lean_dec(v___x_4911_);
v___x_4985_ = lean_box(0);
v_isShared_4986_ = v_isSharedCheck_4990_;
goto v_resetjp_4984_;
}
v_resetjp_4984_:
{
lean_object* v___x_4988_; 
if (v_isShared_4986_ == 0)
{
v___x_4988_ = v___x_4985_;
goto v_reusejp_4987_;
}
else
{
lean_object* v_reuseFailAlloc_4989_; 
v_reuseFailAlloc_4989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4989_, 0, v_a_4983_);
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
lean_object* v___x_4991_; lean_object* v___x_4992_; 
lean_dec_ref(v_b_4896_);
lean_dec_ref(v_a_4895_);
v___x_4991_ = lean_box(0);
v___x_4992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4992_, 0, v___x_4991_);
return v___x_4992_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_processNewEq___boxed(lean_object* v_a_4993_, lean_object* v_b_4994_, lean_object* v_a_4995_, lean_object* v_a_4996_, lean_object* v_a_4997_, lean_object* v_a_4998_, lean_object* v_a_4999_, lean_object* v_a_5000_, lean_object* v_a_5001_, lean_object* v_a_5002_, lean_object* v_a_5003_, lean_object* v_a_5004_, lean_object* v_a_5005_){
_start:
{
lean_object* v_res_5006_; 
v_res_5006_ = l_Lean_Meta_Grind_Order_processNewEq(v_a_4993_, v_b_4994_, v_a_4995_, v_a_4996_, v_a_4997_, v_a_4998_, v_a_4999_, v_a_5000_, v_a_5001_, v_a_5002_, v_a_5003_, v_a_5004_);
lean_dec(v_a_5004_);
lean_dec_ref(v_a_5003_);
lean_dec(v_a_5002_);
lean_dec_ref(v_a_5001_);
lean_dec(v_a_5000_);
lean_dec_ref(v_a_4999_);
lean_dec(v_a_4998_);
lean_dec_ref(v_a_4997_);
lean_dec(v_a_4996_);
lean_dec(v_a_4995_);
return v_res_5006_;
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
