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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_getProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_mkTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_getExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_mkUnsatProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_closeGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setUnsat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setUnsat___boxed(lean_object**);
LEAN_EXPORT uint8_t l_Lean_AssocList_contains___at___00Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_contains___at___00Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_replace___at___00Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_modifyStruct___redArg(lean_object*, lean_object*, lean_object*);
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
lean_object* l_instMonadEST(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__0;
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__1;
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__2_value;
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__3_value;
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__4_value;
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__5_value;
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_getStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_AssocList_forM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachTargetOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachTargetOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_getDist_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_Order_instDecidableLTWeight(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isShorter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isShorter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg___closed__0_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg___closed__1_value;
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___lam__0(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
static double l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___redArg___closed__1_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___redArg___closed__2;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__1_value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 118, 119, 155, 86, 132, 17, 202)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__3_value),LEAN_SCALAR_PTR_LITERAL(142, 44, 102, 149, 148, 89, 41, 13)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__4_value;
lean_object* l_Lean_Meta_Grind_Order_ToPropagate_pp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg___closed__0;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg___closed__1;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
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
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5;
lean_object* l_Lean_Meta_Grind_Order_get_x27___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqTrue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_mkPropagateEqTrueProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateEqTrue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateEqTrue___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_instInhabitedGoalM(lean_object*);
static lean_object* l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0___closed__0;
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Lean.Meta.Tactic.Grind.Order.Assert"};
static const lean_object* l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "Lean.Meta.Grind.Order.propagateSelfEqTrue"};
static const lean_object* l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "assertion violation: c.u == c.v\n  "};
static const lean_object* l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__2_value;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__3;
lean_object* l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateSelfEqTrue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateSelfEqTrue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Order_propagateEqFalse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "eq_trans_false"};
static const lean_object* l_Lean_Meta_Grind_Order_propagateEqFalse___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Order_propagateEqFalse___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Order_propagateEqFalse___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Order_propagateEqFalse___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqFalse___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Order_propagateEqFalse___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqFalse___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(21, 231, 162, 19, 121, 184, 103, 23)}};
static const lean_ctor_object l_Lean_Meta_Grind_Order_propagateEqFalse___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqFalse___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqFalse___closed__0_value),LEAN_SCALAR_PTR_LITERAL(127, 213, 247, 44, 34, 57, 174, 253)}};
static const lean_object* l_Lean_Meta_Grind_Order_propagateEqFalse___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Order_propagateEqFalse___closed__1_value;
static lean_object* l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2;
lean_object* l_Lean_Meta_Grind_pushEqFalse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_mkPropagateEqFalseProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateEqFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateEqFalse___boxed(lean_object**);
static const lean_string_object l_Lean_Meta_Grind_Order_propagateSelfEqFalse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "Lean.Meta.Grind.Order.propagateSelfEqFalse"};
static const lean_object* l_Lean_Meta_Grind_Order_propagateSelfEqFalse___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Order_propagateSelfEqFalse___closed__0_value;
static lean_object* l_Lean_Meta_Grind_Order_propagateSelfEqFalse___closed__1;
lean_object* l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqv___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_alreadyInternalized___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqTrue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__3;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 2, .m_data = "-ε"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4_value;
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__6_value;
uint8_t l_Lean_Meta_Grind_Order_instDecidableLEWeight(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_Cnstr_pp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___boxed(lean_object**);
lean_object* l_Lean_Meta_Grind_isEqFalse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__3;
lean_object* l_Lean_Meta_Grind_Order_Weight_add(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_Order_Weight_isNeg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_UInt64_ofNat___boxed(lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_UInt64_ofNat___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__0_value;
lean_object* l_instHashableProd___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__1;
lean_object* l_instDecidableEqNat___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__2;
lean_object* l_instBEqProd___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__3;
lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_isPartialOrder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_Order_Weight_isZero(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
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
lean_object* l_Lean_Meta_Grind_isInconsistent___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_Order_mkSelfUnsatProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_addEdge(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_addEdge___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "eq_mp"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(21, 231, 162, 19, 121, 184, 103, 23)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(142, 160, 125, 46, 156, 174, 144, 143)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__1_value;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__2;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "assert"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__3_value;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__2_value),LEAN_SCALAR_PTR_LITERAL(40, 139, 28, 5, 248, 187, 127, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__3_value),LEAN_SCALAR_PTR_LITERAL(118, 196, 12, 238, 101, 107, 106, 246)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__4_value;
lean_object* l_Lean_Meta_mkOfEqTrueCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "int_lt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(21, 231, 162, 19, 121, 184, 103, 23)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__0_value),LEAN_SCALAR_PTR_LITERAL(159, 110, 8, 88, 103, 54, 255, 233)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__1_value;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__2;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__3;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__5_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__4_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__6_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__5_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__6_value;
lean_object* l_Lean_Level_ofNat(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__7;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__8;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__9;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__11_value;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__12;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instNegInt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__10_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__14_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__13_value),LEAN_SCALAR_PTR_LITERAL(217, 109, 233, 1, 211, 122, 77, 88)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__14_value;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__15;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "le_of_not_lt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__17_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__17_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(21, 231, 162, 19, 121, 184, 103, 23)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__17_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__16_value),LEAN_SCALAR_PTR_LITERAL(68, 55, 231, 12, 192, 19, 143, 220)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__17_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "le_of_not_le"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__18_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__19_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__19_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(21, 231, 162, 19, 121, 184, 103, 23)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__19_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__18_value),LEAN_SCALAR_PTR_LITERAL(22, 234, 13, 233, 13, 1, 104, 14)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__19 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__19_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "lt_of_not_le"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__20_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__21_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__21_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__21_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(21, 231, 162, 19, 121, 184, 103, 23)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__21_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__20_value),LEAN_SCALAR_PTR_LITERAL(12, 166, 193, 80, 9, 231, 149, 58)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__21 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__21_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "le_of_not_lt_k"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__22 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__22_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__23_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__23_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__23_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(21, 231, 162, 19, 121, 184, 103, 23)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__23_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__22_value),LEAN_SCALAR_PTR_LITERAL(106, 102, 104, 31, 59, 68, 161, 180)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__23 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__23_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "lt_of_not_le_k"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__24 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__24_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__25_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__25_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(21, 231, 162, 19, 121, 184, 103, 23)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__25_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__24_value),LEAN_SCALAR_PTR_LITERAL(103, 116, 151, 104, 206, 219, 96, 226)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__25 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__25_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "eq_mp_not"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__26 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__26_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__27_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__27_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__27_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(21, 231, 162, 19, 121, 184, 103, 23)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__27_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__26_value),LEAN_SCALAR_PTR_LITERAL(251, 101, 191, 216, 104, 179, 193, 169)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__27 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__27_value;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__28;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 2, .m_data = "¬ "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__29 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__29_value;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__30;
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
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__2;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "eq_trans_true'"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(21, 231, 162, 19, 121, 184, 103, 23)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__3_value),LEAN_SCALAR_PTR_LITERAL(38, 24, 59, 247, 190, 28, 198, 137)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__4_value;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__5;
lean_object* l_Lean_Meta_Grind_Order_getCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqFalseProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqTrueProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(lean_object*, lean_object*);
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
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__8;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " = "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__9_value;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__10;
lean_object* l_Lean_Meta_Grind_Order_getNodeId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_mkLePreorderPrefix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Order_mkOrdRingPrefix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Order_processNewEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "of_nat_eq"};
static const lean_object* l_Lean_Meta_Grind_Order_processNewEq___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Order_processNewEq___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Order_processNewEq___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Order_processNewEq___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Order_processNewEq___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Order_processNewEq___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Order_processNewEq___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Order_propagateEqTrue___closed__2_value),LEAN_SCALAR_PTR_LITERAL(21, 231, 162, 19, 121, 184, 103, 23)}};
static const lean_ctor_object l_Lean_Meta_Grind_Order_processNewEq___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Order_processNewEq___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Order_processNewEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(190, 179, 250, 96, 74, 22, 134, 180)}};
static const lean_object* l_Lean_Meta_Grind_Order_processNewEq___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Order_processNewEq___closed__1_value;
static lean_object* l_Lean_Meta_Grind_Order_processNewEq___closed__2;
lean_object* lean_grind_mk_eq_proof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_processNewEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_processNewEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_3, 0);
x_17 = lean_ctor_get(x_3, 2);
x_18 = lean_nat_dec_eq(x_1, x_16);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = l_Lean_Meta_Grind_Order_getProof(x_1, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = l_Lean_Meta_Grind_Order_mkTrans(x_20, x_3, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_3 = x_22;
goto _start;
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_21, 0);
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec_ref(x_3);
x_27 = !lean_is_exclusive(x_19);
if (x_27 == 0)
{
return x_19;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_19, 0);
lean_inc(x_28);
lean_dec(x_19);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; 
lean_inc_ref(x_17);
lean_dec_ref(x_3);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_17);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Grind_Order_getProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath_go(x_1, x_2, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setUnsat(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_18; 
x_18 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath(x_2, x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = l_Lean_Meta_Grind_Order_getExpr(x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = l_Lean_Meta_Grind_Order_getExpr(x_2, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_24 = l_Lean_Meta_Grind_Order_mkUnsatProof(x_21, x_23, x_3, x_4, x_5, x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
x_26 = l_Lean_Meta_Grind_closeGoal(x_25, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_27 = !lean_is_exclusive(x_24);
if (x_27 == 0)
{
return x_24;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_24, 0);
lean_inc(x_28);
lean_dec(x_24);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_4);
x_30 = !lean_is_exclusive(x_22);
if (x_30 == 0)
{
return x_22;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_22, 0);
lean_inc(x_31);
lean_dec(x_22);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_19);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_4);
x_33 = !lean_is_exclusive(x_20);
if (x_33 == 0)
{
return x_20;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_20, 0);
lean_inc(x_34);
lean_dec(x_20);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_4);
x_36 = !lean_is_exclusive(x_18);
if (x_36 == 0)
{
return x_18;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_18, 0);
lean_inc(x_37);
lean_dec(x_18);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setUnsat___boxed(lean_object** _args) {
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
x_18 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setUnsat(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_18;
}
}
LEAN_EXPORT uint8_t l_Lean_AssocList_contains___at___00Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_nat_dec_eq(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_contains___at___00Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_AssocList_contains___at___00Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_replace___at___00Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_nat_dec_eq(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Lean_AssocList_replace___at___00Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0_spec__1___redArg(x_1, x_2, x_7);
lean_ctor_set(x_3, 2, x_9);
return x_3;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_13 = lean_nat_dec_eq(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_AssocList_replace___at___00Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0_spec__1___redArg(x_1, x_2, x_12);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_12);
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_AssocList_contains___at___00Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0_spec__0___redArg(x_2, x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_1);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = l_Lean_AssocList_replace___at___00Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0_spec__1___redArg(x_2, x_3, x_1);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_6; size_t x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_usize_shift_right(x_4, x_5);
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_array_get_size(x_6);
x_10 = lean_nat_dec_lt(x_8, x_9);
if (x_10 == 0)
{
lean_dec(x_8);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_11; 
lean_inc_ref(x_6);
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
lean_object* x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_12 = lean_ctor_get(x_3, 0);
lean_dec(x_12);
x_13 = 1;
x_14 = lean_usize_shift_left(x_13, x_5);
x_15 = lean_usize_sub(x_14, x_13);
x_16 = lean_usize_land(x_4, x_15);
x_17 = 5;
x_18 = lean_usize_sub(x_5, x_17);
x_19 = lean_array_fget(x_6, x_8);
x_20 = lean_box(0);
x_21 = lean_array_fset(x_6, x_8, x_20);
x_22 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1_spec__3___redArg(x_1, x_2, x_19, x_16, x_18);
x_23 = lean_array_fset(x_21, x_8, x_22);
lean_dec(x_8);
lean_ctor_set(x_3, 0, x_23);
return x_3;
}
else
{
size_t x_24; size_t x_25; size_t x_26; size_t x_27; size_t x_28; size_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_3);
x_24 = 1;
x_25 = lean_usize_shift_left(x_24, x_5);
x_26 = lean_usize_sub(x_25, x_24);
x_27 = lean_usize_land(x_4, x_26);
x_28 = 5;
x_29 = lean_usize_sub(x_5, x_28);
x_30 = lean_array_fget(x_6, x_8);
x_31 = lean_box(0);
x_32 = lean_array_fset(x_6, x_8, x_31);
x_33 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1_spec__3___redArg(x_1, x_2, x_30, x_27, x_29);
x_34 = lean_array_fset(x_32, x_8, x_33);
lean_dec(x_8);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_3, 0);
x_37 = lean_usize_to_nat(x_4);
x_38 = lean_array_get_size(x_36);
x_39 = lean_nat_dec_lt(x_37, x_38);
if (x_39 == 0)
{
lean_dec(x_37);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_40; 
lean_inc_ref(x_36);
x_40 = !lean_is_exclusive(x_3);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_3, 0);
lean_dec(x_41);
x_42 = lean_array_fget(x_36, x_37);
x_43 = lean_box(0);
x_44 = lean_array_fset(x_36, x_37, x_43);
x_45 = l_Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0___redArg(x_42, x_1, x_2);
x_46 = lean_array_fset(x_44, x_37, x_45);
lean_dec(x_37);
lean_ctor_set(x_3, 0, x_46);
return x_3;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_3);
x_47 = lean_array_fget(x_36, x_37);
x_48 = lean_box(0);
x_49 = lean_array_fset(x_36, x_37, x_48);
x_50 = l_Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0___redArg(x_47, x_1, x_2);
x_51 = lean_array_fset(x_49, x_37, x_50);
lean_dec(x_37);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1_spec__3___redArg(x_1, x_2, x_3, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; size_t x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 1);
x_9 = lean_ctor_get_usize(x_4, 4);
x_10 = lean_ctor_get(x_4, 3);
x_11 = lean_nat_dec_le(x_10, x_5);
if (x_11 == 0)
{
size_t x_12; lean_object* x_13; 
x_12 = lean_usize_of_nat(x_5);
x_13 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1_spec__3___redArg(x_1, x_2, x_7, x_12, x_9);
lean_ctor_set(x_4, 0, x_13);
return x_4;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_nat_sub(x_5, x_10);
x_15 = lean_array_get_size(x_8);
x_16 = lean_nat_dec_lt(x_14, x_15);
if (x_16 == 0)
{
lean_dec(x_14);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_array_fget(x_8, x_14);
x_18 = lean_box(0);
x_19 = lean_array_fset(x_8, x_14, x_18);
x_20 = l_Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0___redArg(x_17, x_1, x_2);
x_21 = lean_array_fset(x_19, x_14, x_20);
lean_dec(x_14);
lean_ctor_set(x_4, 1, x_21);
return x_4;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; lean_object* x_26; uint8_t x_27; 
x_22 = lean_ctor_get(x_4, 0);
x_23 = lean_ctor_get(x_4, 1);
x_24 = lean_ctor_get(x_4, 2);
x_25 = lean_ctor_get_usize(x_4, 4);
x_26 = lean_ctor_get(x_4, 3);
lean_inc(x_26);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_4);
x_27 = lean_nat_dec_le(x_26, x_5);
if (x_27 == 0)
{
size_t x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_usize_of_nat(x_5);
x_29 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1_spec__3___redArg(x_1, x_2, x_22, x_28, x_25);
x_30 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_23);
lean_ctor_set(x_30, 2, x_24);
lean_ctor_set(x_30, 3, x_26);
lean_ctor_set_usize(x_30, 4, x_25);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_nat_sub(x_5, x_26);
x_32 = lean_array_get_size(x_23);
x_33 = lean_nat_dec_lt(x_31, x_32);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_31);
lean_dec_ref(x_2);
lean_dec(x_1);
x_34 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_34, 0, x_22);
lean_ctor_set(x_34, 1, x_23);
lean_ctor_set(x_34, 2, x_24);
lean_ctor_set(x_34, 3, x_26);
lean_ctor_set_usize(x_34, 4, x_25);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_array_fget(x_23, x_31);
x_36 = lean_box(0);
x_37 = lean_array_fset(x_23, x_31, x_36);
x_38 = l_Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0___redArg(x_35, x_1, x_2);
x_39 = lean_array_fset(x_37, x_31, x_38);
lean_dec(x_31);
x_40 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_40, 0, x_22);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_40, 2, x_24);
lean_ctor_set(x_40, 3, x_26);
lean_ctor_set_usize(x_40, 4, x_25);
return x_40;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_5, 18);
x_8 = lean_ctor_get(x_5, 19);
lean_inc_ref(x_2);
lean_inc(x_1);
x_9 = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1(x_1, x_2, x_3, x_7, x_4);
x_10 = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1(x_4, x_2, x_3, x_8, x_1);
lean_dec(x_1);
lean_ctor_set(x_5, 19, x_10);
lean_ctor_set(x_5, 18, x_9);
return x_5;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_5, 1);
x_13 = lean_ctor_get(x_5, 2);
x_14 = lean_ctor_get(x_5, 3);
x_15 = lean_ctor_get(x_5, 4);
x_16 = lean_ctor_get(x_5, 5);
x_17 = lean_ctor_get(x_5, 6);
x_18 = lean_ctor_get(x_5, 7);
x_19 = lean_ctor_get(x_5, 8);
x_20 = lean_ctor_get(x_5, 9);
x_21 = lean_ctor_get_uint8(x_5, sizeof(void*)*22);
x_22 = lean_ctor_get(x_5, 10);
x_23 = lean_ctor_get(x_5, 11);
x_24 = lean_ctor_get(x_5, 12);
x_25 = lean_ctor_get(x_5, 13);
x_26 = lean_ctor_get(x_5, 14);
x_27 = lean_ctor_get(x_5, 15);
x_28 = lean_ctor_get(x_5, 16);
x_29 = lean_ctor_get(x_5, 17);
x_30 = lean_ctor_get(x_5, 18);
x_31 = lean_ctor_get(x_5, 19);
x_32 = lean_ctor_get(x_5, 20);
x_33 = lean_ctor_get(x_5, 21);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_5);
lean_inc_ref(x_2);
lean_inc(x_1);
x_34 = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1(x_1, x_2, x_3, x_30, x_4);
x_35 = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1(x_4, x_2, x_3, x_31, x_1);
lean_dec(x_1);
x_36 = lean_alloc_ctor(0, 22, 1);
lean_ctor_set(x_36, 0, x_11);
lean_ctor_set(x_36, 1, x_12);
lean_ctor_set(x_36, 2, x_13);
lean_ctor_set(x_36, 3, x_14);
lean_ctor_set(x_36, 4, x_15);
lean_ctor_set(x_36, 5, x_16);
lean_ctor_set(x_36, 6, x_17);
lean_ctor_set(x_36, 7, x_18);
lean_ctor_set(x_36, 8, x_19);
lean_ctor_set(x_36, 9, x_20);
lean_ctor_set(x_36, 10, x_22);
lean_ctor_set(x_36, 11, x_23);
lean_ctor_set(x_36, 12, x_24);
lean_ctor_set(x_36, 13, x_25);
lean_ctor_set(x_36, 14, x_26);
lean_ctor_set(x_36, 15, x_27);
lean_ctor_set(x_36, 16, x_28);
lean_ctor_set(x_36, 17, x_29);
lean_ctor_set(x_36, 18, x_34);
lean_ctor_set(x_36, 19, x_35);
lean_ctor_set(x_36, 20, x_32);
lean_ctor_set(x_36, 21, x_33);
lean_ctor_set_uint8(x_36, sizeof(void*)*22, x_21);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_box(0);
x_8 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist___redArg___lam__0___boxed), 5, 4);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_3);
lean_closure_set(x_8, 2, x_7);
lean_closure_set(x_8, 3, x_2);
x_9 = l_Lean_Meta_Grind_Order_modifyStruct___redArg(x_8, x_4, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist___redArg(x_1, x_2, x_3, x_4, x_5);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_AssocList_contains___at___00Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_AssocList_contains___at___00Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_contains___at___00Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_AssocList_contains___at___00Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_replace___at___00Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_AssocList_replace___at___00Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1_spec__3___redArg(x_1, x_2, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_9 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__1_spec__3(x_1, x_2, x_3, x_4, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_6; size_t x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_usize_shift_right(x_4, x_5);
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_array_get_size(x_6);
x_10 = lean_nat_dec_lt(x_8, x_9);
if (x_10 == 0)
{
lean_dec(x_8);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_11; 
lean_inc_ref(x_6);
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
lean_object* x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_12 = lean_ctor_get(x_3, 0);
lean_dec(x_12);
x_13 = 1;
x_14 = lean_usize_shift_left(x_13, x_5);
x_15 = lean_usize_sub(x_14, x_13);
x_16 = lean_usize_land(x_4, x_15);
x_17 = 5;
x_18 = lean_usize_sub(x_5, x_17);
x_19 = lean_array_fget(x_6, x_8);
x_20 = lean_box(0);
x_21 = lean_array_fset(x_6, x_8, x_20);
x_22 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof_spec__0_spec__0___redArg(x_1, x_2, x_19, x_16, x_18);
x_23 = lean_array_fset(x_21, x_8, x_22);
lean_dec(x_8);
lean_ctor_set(x_3, 0, x_23);
return x_3;
}
else
{
size_t x_24; size_t x_25; size_t x_26; size_t x_27; size_t x_28; size_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_3);
x_24 = 1;
x_25 = lean_usize_shift_left(x_24, x_5);
x_26 = lean_usize_sub(x_25, x_24);
x_27 = lean_usize_land(x_4, x_26);
x_28 = 5;
x_29 = lean_usize_sub(x_5, x_28);
x_30 = lean_array_fget(x_6, x_8);
x_31 = lean_box(0);
x_32 = lean_array_fset(x_6, x_8, x_31);
x_33 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof_spec__0_spec__0___redArg(x_1, x_2, x_30, x_27, x_29);
x_34 = lean_array_fset(x_32, x_8, x_33);
lean_dec(x_8);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_3, 0);
x_37 = lean_usize_to_nat(x_4);
x_38 = lean_array_get_size(x_36);
x_39 = lean_nat_dec_lt(x_37, x_38);
if (x_39 == 0)
{
lean_dec(x_37);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_40; 
lean_inc_ref(x_36);
x_40 = !lean_is_exclusive(x_3);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_3, 0);
lean_dec(x_41);
x_42 = lean_array_fget(x_36, x_37);
x_43 = lean_box(0);
x_44 = lean_array_fset(x_36, x_37, x_43);
x_45 = l_Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0___redArg(x_42, x_1, x_2);
x_46 = lean_array_fset(x_44, x_37, x_45);
lean_dec(x_37);
lean_ctor_set(x_3, 0, x_46);
return x_3;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_3);
x_47 = lean_array_fget(x_36, x_37);
x_48 = lean_box(0);
x_49 = lean_array_fset(x_36, x_37, x_48);
x_50 = l_Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0___redArg(x_47, x_1, x_2);
x_51 = lean_array_fset(x_49, x_37, x_50);
lean_dec(x_37);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof_spec__0_spec__0___redArg(x_1, x_2, x_3, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; size_t x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 1);
x_9 = lean_ctor_get_usize(x_4, 4);
x_10 = lean_ctor_get(x_4, 3);
x_11 = lean_nat_dec_le(x_10, x_5);
if (x_11 == 0)
{
size_t x_12; lean_object* x_13; 
x_12 = lean_usize_of_nat(x_5);
x_13 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof_spec__0_spec__0___redArg(x_1, x_2, x_7, x_12, x_9);
lean_ctor_set(x_4, 0, x_13);
return x_4;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_nat_sub(x_5, x_10);
x_15 = lean_array_get_size(x_8);
x_16 = lean_nat_dec_lt(x_14, x_15);
if (x_16 == 0)
{
lean_dec(x_14);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_array_fget(x_8, x_14);
x_18 = lean_box(0);
x_19 = lean_array_fset(x_8, x_14, x_18);
x_20 = l_Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0___redArg(x_17, x_1, x_2);
x_21 = lean_array_fset(x_19, x_14, x_20);
lean_dec(x_14);
lean_ctor_set(x_4, 1, x_21);
return x_4;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; lean_object* x_26; uint8_t x_27; 
x_22 = lean_ctor_get(x_4, 0);
x_23 = lean_ctor_get(x_4, 1);
x_24 = lean_ctor_get(x_4, 2);
x_25 = lean_ctor_get_usize(x_4, 4);
x_26 = lean_ctor_get(x_4, 3);
lean_inc(x_26);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_4);
x_27 = lean_nat_dec_le(x_26, x_5);
if (x_27 == 0)
{
size_t x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_usize_of_nat(x_5);
x_29 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof_spec__0_spec__0___redArg(x_1, x_2, x_22, x_28, x_25);
x_30 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_23);
lean_ctor_set(x_30, 2, x_24);
lean_ctor_set(x_30, 3, x_26);
lean_ctor_set_usize(x_30, 4, x_25);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_nat_sub(x_5, x_26);
x_32 = lean_array_get_size(x_23);
x_33 = lean_nat_dec_lt(x_31, x_32);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_31);
lean_dec_ref(x_2);
lean_dec(x_1);
x_34 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_34, 0, x_22);
lean_ctor_set(x_34, 1, x_23);
lean_ctor_set(x_34, 2, x_24);
lean_ctor_set(x_34, 3, x_26);
lean_ctor_set_usize(x_34, 4, x_25);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_array_fget(x_23, x_31);
x_36 = lean_box(0);
x_37 = lean_array_fset(x_23, x_31, x_36);
x_38 = l_Lean_AssocList_insert___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist_spec__0___redArg(x_35, x_1, x_2);
x_39 = lean_array_fset(x_37, x_31, x_38);
lean_dec(x_31);
x_40 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_40, 0, x_22);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_40, 2, x_24);
lean_ctor_set(x_40, 3, x_26);
lean_ctor_set_usize(x_40, 4, x_25);
return x_40;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 20);
x_8 = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof_spec__0(x_1, x_2, x_3, x_7, x_4);
lean_ctor_set(x_5, 20, x_8);
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_5, 1);
x_11 = lean_ctor_get(x_5, 2);
x_12 = lean_ctor_get(x_5, 3);
x_13 = lean_ctor_get(x_5, 4);
x_14 = lean_ctor_get(x_5, 5);
x_15 = lean_ctor_get(x_5, 6);
x_16 = lean_ctor_get(x_5, 7);
x_17 = lean_ctor_get(x_5, 8);
x_18 = lean_ctor_get(x_5, 9);
x_19 = lean_ctor_get_uint8(x_5, sizeof(void*)*22);
x_20 = lean_ctor_get(x_5, 10);
x_21 = lean_ctor_get(x_5, 11);
x_22 = lean_ctor_get(x_5, 12);
x_23 = lean_ctor_get(x_5, 13);
x_24 = lean_ctor_get(x_5, 14);
x_25 = lean_ctor_get(x_5, 15);
x_26 = lean_ctor_get(x_5, 16);
x_27 = lean_ctor_get(x_5, 17);
x_28 = lean_ctor_get(x_5, 18);
x_29 = lean_ctor_get(x_5, 19);
x_30 = lean_ctor_get(x_5, 20);
x_31 = lean_ctor_get(x_5, 21);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_5);
x_32 = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof_spec__0(x_1, x_2, x_3, x_30, x_4);
x_33 = lean_alloc_ctor(0, 22, 1);
lean_ctor_set(x_33, 0, x_9);
lean_ctor_set(x_33, 1, x_10);
lean_ctor_set(x_33, 2, x_11);
lean_ctor_set(x_33, 3, x_12);
lean_ctor_set(x_33, 4, x_13);
lean_ctor_set(x_33, 5, x_14);
lean_ctor_set(x_33, 6, x_15);
lean_ctor_set(x_33, 7, x_16);
lean_ctor_set(x_33, 8, x_17);
lean_ctor_set(x_33, 9, x_18);
lean_ctor_set(x_33, 10, x_20);
lean_ctor_set(x_33, 11, x_21);
lean_ctor_set(x_33, 12, x_22);
lean_ctor_set(x_33, 13, x_23);
lean_ctor_set(x_33, 14, x_24);
lean_ctor_set(x_33, 15, x_25);
lean_ctor_set(x_33, 16, x_26);
lean_ctor_set(x_33, 17, x_27);
lean_ctor_set(x_33, 18, x_28);
lean_ctor_set(x_33, 19, x_29);
lean_ctor_set(x_33, 20, x_32);
lean_ctor_set(x_33, 21, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*22, x_19);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_box(0);
x_8 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___redArg___lam__0___boxed), 5, 4);
lean_closure_set(x_8, 0, x_2);
lean_closure_set(x_8, 1, x_3);
lean_closure_set(x_8, 2, x_7);
lean_closure_set(x_8, 3, x_1);
x_9 = l_Lean_Meta_Grind_Order_modifyStruct___redArg(x_8, x_4, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___redArg(x_1, x_2, x_3, x_4, x_5);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof_spec__0_spec__0___redArg(x_1, x_2, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_9 = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof_spec__0_spec__0(x_1, x_2, x_3, x_4, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEST(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__0;
x_2 = l_ReaderT_instMonad___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; uint8_t x_16; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__1;
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_20 = lean_ctor_get(x_17, 0);
x_21 = lean_ctor_get(x_17, 2);
x_22 = lean_ctor_get(x_17, 3);
x_23 = lean_ctor_get(x_17, 4);
x_24 = lean_ctor_get(x_17, 1);
lean_dec(x_24);
x_25 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__2));
x_26 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__3));
lean_inc_ref(x_20);
x_27 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_27, 0, x_20);
x_28 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_28, 0, x_20);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_30, 0, x_23);
x_31 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_31, 0, x_22);
x_32 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_32, 0, x_21);
lean_ctor_set(x_17, 4, x_30);
lean_ctor_set(x_17, 3, x_31);
lean_ctor_set(x_17, 2, x_32);
lean_ctor_set(x_17, 1, x_25);
lean_ctor_set(x_17, 0, x_29);
lean_ctor_set(x_15, 1, x_26);
x_33 = l_ReaderT_instMonad___redArg(x_15);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_33, 1);
lean_dec(x_36);
x_37 = !lean_is_exclusive(x_35);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_38 = lean_ctor_get(x_35, 0);
x_39 = lean_ctor_get(x_35, 2);
x_40 = lean_ctor_get(x_35, 3);
x_41 = lean_ctor_get(x_35, 4);
x_42 = lean_ctor_get(x_35, 1);
lean_dec(x_42);
x_43 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__4));
x_44 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__5));
lean_inc_ref(x_38);
x_45 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_45, 0, x_38);
x_46 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_46, 0, x_38);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_48, 0, x_41);
x_49 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_49, 0, x_40);
x_50 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_50, 0, x_39);
lean_ctor_set(x_35, 4, x_48);
lean_ctor_set(x_35, 3, x_49);
lean_ctor_set(x_35, 2, x_50);
lean_ctor_set(x_35, 1, x_43);
lean_ctor_set(x_35, 0, x_47);
lean_ctor_set(x_33, 1, x_44);
x_51 = l_ReaderT_instMonad___redArg(x_33);
x_52 = l_ReaderT_instMonad___redArg(x_51);
x_53 = l_ReaderT_instMonad___redArg(x_52);
x_54 = l_ReaderT_instMonad___redArg(x_53);
x_55 = l_ReaderT_instMonad___redArg(x_54);
x_56 = l_ReaderT_instMonad___redArg(x_55);
x_57 = l_ReaderT_instMonad___redArg(x_56);
x_58 = l_Lean_Meta_Grind_Order_getStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
lean_dec_ref(x_58);
x_60 = lean_ctor_get(x_59, 18);
lean_inc_ref(x_60);
lean_dec(x_59);
x_61 = lean_ctor_get(x_60, 2);
x_62 = lean_box(0);
x_63 = lean_nat_dec_lt(x_1, x_61);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec_ref(x_60);
x_64 = l_outOfBounds___redArg(x_62);
x_65 = l_Lean_AssocList_forM___redArg(x_57, x_2, x_64);
x_66 = lean_apply_12(x_65, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, lean_box(0));
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = l_Lean_PersistentArray_get_x21___redArg(x_62, x_60, x_1);
x_68 = l_Lean_AssocList_forM___redArg(x_57, x_2, x_67);
x_69 = lean_apply_12(x_68, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, lean_box(0));
return x_69;
}
}
else
{
uint8_t x_70; 
lean_dec_ref(x_57);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_70 = !lean_is_exclusive(x_58);
if (x_70 == 0)
{
return x_58;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_58, 0);
lean_inc(x_71);
lean_dec(x_58);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_71);
return x_72;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_73 = lean_ctor_get(x_35, 0);
x_74 = lean_ctor_get(x_35, 2);
x_75 = lean_ctor_get(x_35, 3);
x_76 = lean_ctor_get(x_35, 4);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_35);
x_77 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__4));
x_78 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__5));
lean_inc_ref(x_73);
x_79 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_79, 0, x_73);
x_80 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_80, 0, x_73);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_82, 0, x_76);
x_83 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_83, 0, x_75);
x_84 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_84, 0, x_74);
x_85 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_85, 0, x_81);
lean_ctor_set(x_85, 1, x_77);
lean_ctor_set(x_85, 2, x_84);
lean_ctor_set(x_85, 3, x_83);
lean_ctor_set(x_85, 4, x_82);
lean_ctor_set(x_33, 1, x_78);
lean_ctor_set(x_33, 0, x_85);
x_86 = l_ReaderT_instMonad___redArg(x_33);
x_87 = l_ReaderT_instMonad___redArg(x_86);
x_88 = l_ReaderT_instMonad___redArg(x_87);
x_89 = l_ReaderT_instMonad___redArg(x_88);
x_90 = l_ReaderT_instMonad___redArg(x_89);
x_91 = l_ReaderT_instMonad___redArg(x_90);
x_92 = l_ReaderT_instMonad___redArg(x_91);
x_93 = l_Lean_Meta_Grind_Order_getStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
lean_dec_ref(x_93);
x_95 = lean_ctor_get(x_94, 18);
lean_inc_ref(x_95);
lean_dec(x_94);
x_96 = lean_ctor_get(x_95, 2);
x_97 = lean_box(0);
x_98 = lean_nat_dec_lt(x_1, x_96);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec_ref(x_95);
x_99 = l_outOfBounds___redArg(x_97);
x_100 = l_Lean_AssocList_forM___redArg(x_92, x_2, x_99);
x_101 = lean_apply_12(x_100, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, lean_box(0));
return x_101;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = l_Lean_PersistentArray_get_x21___redArg(x_97, x_95, x_1);
x_103 = l_Lean_AssocList_forM___redArg(x_92, x_2, x_102);
x_104 = lean_apply_12(x_103, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, lean_box(0));
return x_104;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec_ref(x_92);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_105 = lean_ctor_get(x_93, 0);
lean_inc(x_105);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 x_106 = x_93;
} else {
 lean_dec_ref(x_93);
 x_106 = lean_box(0);
}
if (lean_is_scalar(x_106)) {
 x_107 = lean_alloc_ctor(1, 1, 0);
} else {
 x_107 = x_106;
}
lean_ctor_set(x_107, 0, x_105);
return x_107;
}
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_108 = lean_ctor_get(x_33, 0);
lean_inc(x_108);
lean_dec(x_33);
x_109 = lean_ctor_get(x_108, 0);
lean_inc_ref(x_109);
x_110 = lean_ctor_get(x_108, 2);
lean_inc(x_110);
x_111 = lean_ctor_get(x_108, 3);
lean_inc(x_111);
x_112 = lean_ctor_get(x_108, 4);
lean_inc(x_112);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 lean_ctor_release(x_108, 2);
 lean_ctor_release(x_108, 3);
 lean_ctor_release(x_108, 4);
 x_113 = x_108;
} else {
 lean_dec_ref(x_108);
 x_113 = lean_box(0);
}
x_114 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__4));
x_115 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__5));
lean_inc_ref(x_109);
x_116 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_116, 0, x_109);
x_117 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_117, 0, x_109);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
x_119 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_119, 0, x_112);
x_120 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_120, 0, x_111);
x_121 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_121, 0, x_110);
if (lean_is_scalar(x_113)) {
 x_122 = lean_alloc_ctor(0, 5, 0);
} else {
 x_122 = x_113;
}
lean_ctor_set(x_122, 0, x_118);
lean_ctor_set(x_122, 1, x_114);
lean_ctor_set(x_122, 2, x_121);
lean_ctor_set(x_122, 3, x_120);
lean_ctor_set(x_122, 4, x_119);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_115);
x_124 = l_ReaderT_instMonad___redArg(x_123);
x_125 = l_ReaderT_instMonad___redArg(x_124);
x_126 = l_ReaderT_instMonad___redArg(x_125);
x_127 = l_ReaderT_instMonad___redArg(x_126);
x_128 = l_ReaderT_instMonad___redArg(x_127);
x_129 = l_ReaderT_instMonad___redArg(x_128);
x_130 = l_ReaderT_instMonad___redArg(x_129);
x_131 = l_Lean_Meta_Grind_Order_getStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
lean_dec_ref(x_131);
x_133 = lean_ctor_get(x_132, 18);
lean_inc_ref(x_133);
lean_dec(x_132);
x_134 = lean_ctor_get(x_133, 2);
x_135 = lean_box(0);
x_136 = lean_nat_dec_lt(x_1, x_134);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec_ref(x_133);
x_137 = l_outOfBounds___redArg(x_135);
x_138 = l_Lean_AssocList_forM___redArg(x_130, x_2, x_137);
x_139 = lean_apply_12(x_138, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, lean_box(0));
return x_139;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = l_Lean_PersistentArray_get_x21___redArg(x_135, x_133, x_1);
x_141 = l_Lean_AssocList_forM___redArg(x_130, x_2, x_140);
x_142 = lean_apply_12(x_141, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, lean_box(0));
return x_142;
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec_ref(x_130);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_143 = lean_ctor_get(x_131, 0);
lean_inc(x_143);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 x_144 = x_131;
} else {
 lean_dec_ref(x_131);
 x_144 = lean_box(0);
}
if (lean_is_scalar(x_144)) {
 x_145 = lean_alloc_ctor(1, 1, 0);
} else {
 x_145 = x_144;
}
lean_ctor_set(x_145, 0, x_143);
return x_145;
}
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_146 = lean_ctor_get(x_17, 0);
x_147 = lean_ctor_get(x_17, 2);
x_148 = lean_ctor_get(x_17, 3);
x_149 = lean_ctor_get(x_17, 4);
lean_inc(x_149);
lean_inc(x_148);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_17);
x_150 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__2));
x_151 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__3));
lean_inc_ref(x_146);
x_152 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_152, 0, x_146);
x_153 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_153, 0, x_146);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
x_155 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_155, 0, x_149);
x_156 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_156, 0, x_148);
x_157 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_157, 0, x_147);
x_158 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_158, 0, x_154);
lean_ctor_set(x_158, 1, x_150);
lean_ctor_set(x_158, 2, x_157);
lean_ctor_set(x_158, 3, x_156);
lean_ctor_set(x_158, 4, x_155);
lean_ctor_set(x_15, 1, x_151);
lean_ctor_set(x_15, 0, x_158);
x_159 = l_ReaderT_instMonad___redArg(x_15);
x_160 = lean_ctor_get(x_159, 0);
lean_inc_ref(x_160);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_161 = x_159;
} else {
 lean_dec_ref(x_159);
 x_161 = lean_box(0);
}
x_162 = lean_ctor_get(x_160, 0);
lean_inc_ref(x_162);
x_163 = lean_ctor_get(x_160, 2);
lean_inc(x_163);
x_164 = lean_ctor_get(x_160, 3);
lean_inc(x_164);
x_165 = lean_ctor_get(x_160, 4);
lean_inc(x_165);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 lean_ctor_release(x_160, 2);
 lean_ctor_release(x_160, 3);
 lean_ctor_release(x_160, 4);
 x_166 = x_160;
} else {
 lean_dec_ref(x_160);
 x_166 = lean_box(0);
}
x_167 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__4));
x_168 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__5));
lean_inc_ref(x_162);
x_169 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_169, 0, x_162);
x_170 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_170, 0, x_162);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_170);
x_172 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_172, 0, x_165);
x_173 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_173, 0, x_164);
x_174 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_174, 0, x_163);
if (lean_is_scalar(x_166)) {
 x_175 = lean_alloc_ctor(0, 5, 0);
} else {
 x_175 = x_166;
}
lean_ctor_set(x_175, 0, x_171);
lean_ctor_set(x_175, 1, x_167);
lean_ctor_set(x_175, 2, x_174);
lean_ctor_set(x_175, 3, x_173);
lean_ctor_set(x_175, 4, x_172);
if (lean_is_scalar(x_161)) {
 x_176 = lean_alloc_ctor(0, 2, 0);
} else {
 x_176 = x_161;
}
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_168);
x_177 = l_ReaderT_instMonad___redArg(x_176);
x_178 = l_ReaderT_instMonad___redArg(x_177);
x_179 = l_ReaderT_instMonad___redArg(x_178);
x_180 = l_ReaderT_instMonad___redArg(x_179);
x_181 = l_ReaderT_instMonad___redArg(x_180);
x_182 = l_ReaderT_instMonad___redArg(x_181);
x_183 = l_ReaderT_instMonad___redArg(x_182);
x_184 = l_Lean_Meta_Grind_Order_getStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; 
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
lean_dec_ref(x_184);
x_186 = lean_ctor_get(x_185, 18);
lean_inc_ref(x_186);
lean_dec(x_185);
x_187 = lean_ctor_get(x_186, 2);
x_188 = lean_box(0);
x_189 = lean_nat_dec_lt(x_1, x_187);
if (x_189 == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_dec_ref(x_186);
x_190 = l_outOfBounds___redArg(x_188);
x_191 = l_Lean_AssocList_forM___redArg(x_183, x_2, x_190);
x_192 = lean_apply_12(x_191, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, lean_box(0));
return x_192;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = l_Lean_PersistentArray_get_x21___redArg(x_188, x_186, x_1);
x_194 = l_Lean_AssocList_forM___redArg(x_183, x_2, x_193);
x_195 = lean_apply_12(x_194, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, lean_box(0));
return x_195;
}
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec_ref(x_183);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_196 = lean_ctor_get(x_184, 0);
lean_inc(x_196);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 x_197 = x_184;
} else {
 lean_dec_ref(x_184);
 x_197 = lean_box(0);
}
if (lean_is_scalar(x_197)) {
 x_198 = lean_alloc_ctor(1, 1, 0);
} else {
 x_198 = x_197;
}
lean_ctor_set(x_198, 0, x_196);
return x_198;
}
}
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_199 = lean_ctor_get(x_15, 0);
lean_inc(x_199);
lean_dec(x_15);
x_200 = lean_ctor_get(x_199, 0);
lean_inc_ref(x_200);
x_201 = lean_ctor_get(x_199, 2);
lean_inc(x_201);
x_202 = lean_ctor_get(x_199, 3);
lean_inc(x_202);
x_203 = lean_ctor_get(x_199, 4);
lean_inc(x_203);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 lean_ctor_release(x_199, 2);
 lean_ctor_release(x_199, 3);
 lean_ctor_release(x_199, 4);
 x_204 = x_199;
} else {
 lean_dec_ref(x_199);
 x_204 = lean_box(0);
}
x_205 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__2));
x_206 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__3));
lean_inc_ref(x_200);
x_207 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_207, 0, x_200);
x_208 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_208, 0, x_200);
x_209 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_208);
x_210 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_210, 0, x_203);
x_211 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_211, 0, x_202);
x_212 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_212, 0, x_201);
if (lean_is_scalar(x_204)) {
 x_213 = lean_alloc_ctor(0, 5, 0);
} else {
 x_213 = x_204;
}
lean_ctor_set(x_213, 0, x_209);
lean_ctor_set(x_213, 1, x_205);
lean_ctor_set(x_213, 2, x_212);
lean_ctor_set(x_213, 3, x_211);
lean_ctor_set(x_213, 4, x_210);
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_206);
x_215 = l_ReaderT_instMonad___redArg(x_214);
x_216 = lean_ctor_get(x_215, 0);
lean_inc_ref(x_216);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 lean_ctor_release(x_215, 1);
 x_217 = x_215;
} else {
 lean_dec_ref(x_215);
 x_217 = lean_box(0);
}
x_218 = lean_ctor_get(x_216, 0);
lean_inc_ref(x_218);
x_219 = lean_ctor_get(x_216, 2);
lean_inc(x_219);
x_220 = lean_ctor_get(x_216, 3);
lean_inc(x_220);
x_221 = lean_ctor_get(x_216, 4);
lean_inc(x_221);
if (lean_is_exclusive(x_216)) {
 lean_ctor_release(x_216, 0);
 lean_ctor_release(x_216, 1);
 lean_ctor_release(x_216, 2);
 lean_ctor_release(x_216, 3);
 lean_ctor_release(x_216, 4);
 x_222 = x_216;
} else {
 lean_dec_ref(x_216);
 x_222 = lean_box(0);
}
x_223 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__4));
x_224 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__5));
lean_inc_ref(x_218);
x_225 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_225, 0, x_218);
x_226 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_226, 0, x_218);
x_227 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_227, 0, x_225);
lean_ctor_set(x_227, 1, x_226);
x_228 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_228, 0, x_221);
x_229 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_229, 0, x_220);
x_230 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_230, 0, x_219);
if (lean_is_scalar(x_222)) {
 x_231 = lean_alloc_ctor(0, 5, 0);
} else {
 x_231 = x_222;
}
lean_ctor_set(x_231, 0, x_227);
lean_ctor_set(x_231, 1, x_223);
lean_ctor_set(x_231, 2, x_230);
lean_ctor_set(x_231, 3, x_229);
lean_ctor_set(x_231, 4, x_228);
if (lean_is_scalar(x_217)) {
 x_232 = lean_alloc_ctor(0, 2, 0);
} else {
 x_232 = x_217;
}
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_224);
x_233 = l_ReaderT_instMonad___redArg(x_232);
x_234 = l_ReaderT_instMonad___redArg(x_233);
x_235 = l_ReaderT_instMonad___redArg(x_234);
x_236 = l_ReaderT_instMonad___redArg(x_235);
x_237 = l_ReaderT_instMonad___redArg(x_236);
x_238 = l_ReaderT_instMonad___redArg(x_237);
x_239 = l_ReaderT_instMonad___redArg(x_238);
x_240 = l_Lean_Meta_Grind_Order_getStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_240) == 0)
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; uint8_t x_245; 
x_241 = lean_ctor_get(x_240, 0);
lean_inc(x_241);
lean_dec_ref(x_240);
x_242 = lean_ctor_get(x_241, 18);
lean_inc_ref(x_242);
lean_dec(x_241);
x_243 = lean_ctor_get(x_242, 2);
x_244 = lean_box(0);
x_245 = lean_nat_dec_lt(x_1, x_243);
if (x_245 == 0)
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec_ref(x_242);
x_246 = l_outOfBounds___redArg(x_244);
x_247 = l_Lean_AssocList_forM___redArg(x_239, x_2, x_246);
x_248 = lean_apply_12(x_247, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, lean_box(0));
return x_248;
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_249 = l_Lean_PersistentArray_get_x21___redArg(x_244, x_242, x_1);
x_250 = l_Lean_AssocList_forM___redArg(x_239, x_2, x_249);
x_251 = lean_apply_12(x_250, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, lean_box(0));
return x_251;
}
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; 
lean_dec_ref(x_239);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_252 = lean_ctor_get(x_240, 0);
lean_inc(x_252);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 x_253 = x_240;
} else {
 lean_dec_ref(x_240);
 x_253 = lean_box(0);
}
if (lean_is_scalar(x_253)) {
 x_254 = lean_alloc_ctor(1, 1, 0);
} else {
 x_254 = x_253;
}
lean_ctor_set(x_254, 0, x_252);
return x_254;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachTargetOf(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; uint8_t x_16; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__1;
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_20 = lean_ctor_get(x_17, 0);
x_21 = lean_ctor_get(x_17, 2);
x_22 = lean_ctor_get(x_17, 3);
x_23 = lean_ctor_get(x_17, 4);
x_24 = lean_ctor_get(x_17, 1);
lean_dec(x_24);
x_25 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__2));
x_26 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__3));
lean_inc_ref(x_20);
x_27 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_27, 0, x_20);
x_28 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_28, 0, x_20);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_30, 0, x_23);
x_31 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_31, 0, x_22);
x_32 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_32, 0, x_21);
lean_ctor_set(x_17, 4, x_30);
lean_ctor_set(x_17, 3, x_31);
lean_ctor_set(x_17, 2, x_32);
lean_ctor_set(x_17, 1, x_25);
lean_ctor_set(x_17, 0, x_29);
lean_ctor_set(x_15, 1, x_26);
x_33 = l_ReaderT_instMonad___redArg(x_15);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_33, 1);
lean_dec(x_36);
x_37 = !lean_is_exclusive(x_35);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_38 = lean_ctor_get(x_35, 0);
x_39 = lean_ctor_get(x_35, 2);
x_40 = lean_ctor_get(x_35, 3);
x_41 = lean_ctor_get(x_35, 4);
x_42 = lean_ctor_get(x_35, 1);
lean_dec(x_42);
x_43 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__4));
x_44 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__5));
lean_inc_ref(x_38);
x_45 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_45, 0, x_38);
x_46 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_46, 0, x_38);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_48, 0, x_41);
x_49 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_49, 0, x_40);
x_50 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_50, 0, x_39);
lean_ctor_set(x_35, 4, x_48);
lean_ctor_set(x_35, 3, x_49);
lean_ctor_set(x_35, 2, x_50);
lean_ctor_set(x_35, 1, x_43);
lean_ctor_set(x_35, 0, x_47);
lean_ctor_set(x_33, 1, x_44);
x_51 = l_ReaderT_instMonad___redArg(x_33);
x_52 = l_ReaderT_instMonad___redArg(x_51);
x_53 = l_ReaderT_instMonad___redArg(x_52);
x_54 = l_ReaderT_instMonad___redArg(x_53);
x_55 = l_ReaderT_instMonad___redArg(x_54);
x_56 = l_ReaderT_instMonad___redArg(x_55);
x_57 = l_ReaderT_instMonad___redArg(x_56);
x_58 = l_Lean_Meta_Grind_Order_getStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
lean_dec_ref(x_58);
x_60 = lean_ctor_get(x_59, 19);
lean_inc_ref(x_60);
lean_dec(x_59);
x_61 = lean_ctor_get(x_60, 2);
x_62 = lean_box(0);
x_63 = lean_nat_dec_lt(x_1, x_61);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec_ref(x_60);
x_64 = l_outOfBounds___redArg(x_62);
x_65 = l_Lean_AssocList_forM___redArg(x_57, x_2, x_64);
x_66 = lean_apply_12(x_65, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, lean_box(0));
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = l_Lean_PersistentArray_get_x21___redArg(x_62, x_60, x_1);
x_68 = l_Lean_AssocList_forM___redArg(x_57, x_2, x_67);
x_69 = lean_apply_12(x_68, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, lean_box(0));
return x_69;
}
}
else
{
uint8_t x_70; 
lean_dec_ref(x_57);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_70 = !lean_is_exclusive(x_58);
if (x_70 == 0)
{
return x_58;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_58, 0);
lean_inc(x_71);
lean_dec(x_58);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_71);
return x_72;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_73 = lean_ctor_get(x_35, 0);
x_74 = lean_ctor_get(x_35, 2);
x_75 = lean_ctor_get(x_35, 3);
x_76 = lean_ctor_get(x_35, 4);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_35);
x_77 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__4));
x_78 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__5));
lean_inc_ref(x_73);
x_79 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_79, 0, x_73);
x_80 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_80, 0, x_73);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_82, 0, x_76);
x_83 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_83, 0, x_75);
x_84 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_84, 0, x_74);
x_85 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_85, 0, x_81);
lean_ctor_set(x_85, 1, x_77);
lean_ctor_set(x_85, 2, x_84);
lean_ctor_set(x_85, 3, x_83);
lean_ctor_set(x_85, 4, x_82);
lean_ctor_set(x_33, 1, x_78);
lean_ctor_set(x_33, 0, x_85);
x_86 = l_ReaderT_instMonad___redArg(x_33);
x_87 = l_ReaderT_instMonad___redArg(x_86);
x_88 = l_ReaderT_instMonad___redArg(x_87);
x_89 = l_ReaderT_instMonad___redArg(x_88);
x_90 = l_ReaderT_instMonad___redArg(x_89);
x_91 = l_ReaderT_instMonad___redArg(x_90);
x_92 = l_ReaderT_instMonad___redArg(x_91);
x_93 = l_Lean_Meta_Grind_Order_getStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
lean_dec_ref(x_93);
x_95 = lean_ctor_get(x_94, 19);
lean_inc_ref(x_95);
lean_dec(x_94);
x_96 = lean_ctor_get(x_95, 2);
x_97 = lean_box(0);
x_98 = lean_nat_dec_lt(x_1, x_96);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec_ref(x_95);
x_99 = l_outOfBounds___redArg(x_97);
x_100 = l_Lean_AssocList_forM___redArg(x_92, x_2, x_99);
x_101 = lean_apply_12(x_100, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, lean_box(0));
return x_101;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = l_Lean_PersistentArray_get_x21___redArg(x_97, x_95, x_1);
x_103 = l_Lean_AssocList_forM___redArg(x_92, x_2, x_102);
x_104 = lean_apply_12(x_103, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, lean_box(0));
return x_104;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec_ref(x_92);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_105 = lean_ctor_get(x_93, 0);
lean_inc(x_105);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 x_106 = x_93;
} else {
 lean_dec_ref(x_93);
 x_106 = lean_box(0);
}
if (lean_is_scalar(x_106)) {
 x_107 = lean_alloc_ctor(1, 1, 0);
} else {
 x_107 = x_106;
}
lean_ctor_set(x_107, 0, x_105);
return x_107;
}
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_108 = lean_ctor_get(x_33, 0);
lean_inc(x_108);
lean_dec(x_33);
x_109 = lean_ctor_get(x_108, 0);
lean_inc_ref(x_109);
x_110 = lean_ctor_get(x_108, 2);
lean_inc(x_110);
x_111 = lean_ctor_get(x_108, 3);
lean_inc(x_111);
x_112 = lean_ctor_get(x_108, 4);
lean_inc(x_112);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 lean_ctor_release(x_108, 2);
 lean_ctor_release(x_108, 3);
 lean_ctor_release(x_108, 4);
 x_113 = x_108;
} else {
 lean_dec_ref(x_108);
 x_113 = lean_box(0);
}
x_114 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__4));
x_115 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__5));
lean_inc_ref(x_109);
x_116 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_116, 0, x_109);
x_117 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_117, 0, x_109);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
x_119 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_119, 0, x_112);
x_120 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_120, 0, x_111);
x_121 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_121, 0, x_110);
if (lean_is_scalar(x_113)) {
 x_122 = lean_alloc_ctor(0, 5, 0);
} else {
 x_122 = x_113;
}
lean_ctor_set(x_122, 0, x_118);
lean_ctor_set(x_122, 1, x_114);
lean_ctor_set(x_122, 2, x_121);
lean_ctor_set(x_122, 3, x_120);
lean_ctor_set(x_122, 4, x_119);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_115);
x_124 = l_ReaderT_instMonad___redArg(x_123);
x_125 = l_ReaderT_instMonad___redArg(x_124);
x_126 = l_ReaderT_instMonad___redArg(x_125);
x_127 = l_ReaderT_instMonad___redArg(x_126);
x_128 = l_ReaderT_instMonad___redArg(x_127);
x_129 = l_ReaderT_instMonad___redArg(x_128);
x_130 = l_ReaderT_instMonad___redArg(x_129);
x_131 = l_Lean_Meta_Grind_Order_getStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
lean_dec_ref(x_131);
x_133 = lean_ctor_get(x_132, 19);
lean_inc_ref(x_133);
lean_dec(x_132);
x_134 = lean_ctor_get(x_133, 2);
x_135 = lean_box(0);
x_136 = lean_nat_dec_lt(x_1, x_134);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec_ref(x_133);
x_137 = l_outOfBounds___redArg(x_135);
x_138 = l_Lean_AssocList_forM___redArg(x_130, x_2, x_137);
x_139 = lean_apply_12(x_138, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, lean_box(0));
return x_139;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = l_Lean_PersistentArray_get_x21___redArg(x_135, x_133, x_1);
x_141 = l_Lean_AssocList_forM___redArg(x_130, x_2, x_140);
x_142 = lean_apply_12(x_141, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, lean_box(0));
return x_142;
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec_ref(x_130);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_143 = lean_ctor_get(x_131, 0);
lean_inc(x_143);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 x_144 = x_131;
} else {
 lean_dec_ref(x_131);
 x_144 = lean_box(0);
}
if (lean_is_scalar(x_144)) {
 x_145 = lean_alloc_ctor(1, 1, 0);
} else {
 x_145 = x_144;
}
lean_ctor_set(x_145, 0, x_143);
return x_145;
}
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_146 = lean_ctor_get(x_17, 0);
x_147 = lean_ctor_get(x_17, 2);
x_148 = lean_ctor_get(x_17, 3);
x_149 = lean_ctor_get(x_17, 4);
lean_inc(x_149);
lean_inc(x_148);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_17);
x_150 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__2));
x_151 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__3));
lean_inc_ref(x_146);
x_152 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_152, 0, x_146);
x_153 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_153, 0, x_146);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
x_155 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_155, 0, x_149);
x_156 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_156, 0, x_148);
x_157 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_157, 0, x_147);
x_158 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_158, 0, x_154);
lean_ctor_set(x_158, 1, x_150);
lean_ctor_set(x_158, 2, x_157);
lean_ctor_set(x_158, 3, x_156);
lean_ctor_set(x_158, 4, x_155);
lean_ctor_set(x_15, 1, x_151);
lean_ctor_set(x_15, 0, x_158);
x_159 = l_ReaderT_instMonad___redArg(x_15);
x_160 = lean_ctor_get(x_159, 0);
lean_inc_ref(x_160);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_161 = x_159;
} else {
 lean_dec_ref(x_159);
 x_161 = lean_box(0);
}
x_162 = lean_ctor_get(x_160, 0);
lean_inc_ref(x_162);
x_163 = lean_ctor_get(x_160, 2);
lean_inc(x_163);
x_164 = lean_ctor_get(x_160, 3);
lean_inc(x_164);
x_165 = lean_ctor_get(x_160, 4);
lean_inc(x_165);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 lean_ctor_release(x_160, 2);
 lean_ctor_release(x_160, 3);
 lean_ctor_release(x_160, 4);
 x_166 = x_160;
} else {
 lean_dec_ref(x_160);
 x_166 = lean_box(0);
}
x_167 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__4));
x_168 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__5));
lean_inc_ref(x_162);
x_169 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_169, 0, x_162);
x_170 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_170, 0, x_162);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_170);
x_172 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_172, 0, x_165);
x_173 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_173, 0, x_164);
x_174 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_174, 0, x_163);
if (lean_is_scalar(x_166)) {
 x_175 = lean_alloc_ctor(0, 5, 0);
} else {
 x_175 = x_166;
}
lean_ctor_set(x_175, 0, x_171);
lean_ctor_set(x_175, 1, x_167);
lean_ctor_set(x_175, 2, x_174);
lean_ctor_set(x_175, 3, x_173);
lean_ctor_set(x_175, 4, x_172);
if (lean_is_scalar(x_161)) {
 x_176 = lean_alloc_ctor(0, 2, 0);
} else {
 x_176 = x_161;
}
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_168);
x_177 = l_ReaderT_instMonad___redArg(x_176);
x_178 = l_ReaderT_instMonad___redArg(x_177);
x_179 = l_ReaderT_instMonad___redArg(x_178);
x_180 = l_ReaderT_instMonad___redArg(x_179);
x_181 = l_ReaderT_instMonad___redArg(x_180);
x_182 = l_ReaderT_instMonad___redArg(x_181);
x_183 = l_ReaderT_instMonad___redArg(x_182);
x_184 = l_Lean_Meta_Grind_Order_getStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; 
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
lean_dec_ref(x_184);
x_186 = lean_ctor_get(x_185, 19);
lean_inc_ref(x_186);
lean_dec(x_185);
x_187 = lean_ctor_get(x_186, 2);
x_188 = lean_box(0);
x_189 = lean_nat_dec_lt(x_1, x_187);
if (x_189 == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_dec_ref(x_186);
x_190 = l_outOfBounds___redArg(x_188);
x_191 = l_Lean_AssocList_forM___redArg(x_183, x_2, x_190);
x_192 = lean_apply_12(x_191, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, lean_box(0));
return x_192;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = l_Lean_PersistentArray_get_x21___redArg(x_188, x_186, x_1);
x_194 = l_Lean_AssocList_forM___redArg(x_183, x_2, x_193);
x_195 = lean_apply_12(x_194, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, lean_box(0));
return x_195;
}
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec_ref(x_183);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_196 = lean_ctor_get(x_184, 0);
lean_inc(x_196);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 x_197 = x_184;
} else {
 lean_dec_ref(x_184);
 x_197 = lean_box(0);
}
if (lean_is_scalar(x_197)) {
 x_198 = lean_alloc_ctor(1, 1, 0);
} else {
 x_198 = x_197;
}
lean_ctor_set(x_198, 0, x_196);
return x_198;
}
}
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_199 = lean_ctor_get(x_15, 0);
lean_inc(x_199);
lean_dec(x_15);
x_200 = lean_ctor_get(x_199, 0);
lean_inc_ref(x_200);
x_201 = lean_ctor_get(x_199, 2);
lean_inc(x_201);
x_202 = lean_ctor_get(x_199, 3);
lean_inc(x_202);
x_203 = lean_ctor_get(x_199, 4);
lean_inc(x_203);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 lean_ctor_release(x_199, 2);
 lean_ctor_release(x_199, 3);
 lean_ctor_release(x_199, 4);
 x_204 = x_199;
} else {
 lean_dec_ref(x_199);
 x_204 = lean_box(0);
}
x_205 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__2));
x_206 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__3));
lean_inc_ref(x_200);
x_207 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_207, 0, x_200);
x_208 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_208, 0, x_200);
x_209 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_208);
x_210 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_210, 0, x_203);
x_211 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_211, 0, x_202);
x_212 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_212, 0, x_201);
if (lean_is_scalar(x_204)) {
 x_213 = lean_alloc_ctor(0, 5, 0);
} else {
 x_213 = x_204;
}
lean_ctor_set(x_213, 0, x_209);
lean_ctor_set(x_213, 1, x_205);
lean_ctor_set(x_213, 2, x_212);
lean_ctor_set(x_213, 3, x_211);
lean_ctor_set(x_213, 4, x_210);
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_206);
x_215 = l_ReaderT_instMonad___redArg(x_214);
x_216 = lean_ctor_get(x_215, 0);
lean_inc_ref(x_216);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 lean_ctor_release(x_215, 1);
 x_217 = x_215;
} else {
 lean_dec_ref(x_215);
 x_217 = lean_box(0);
}
x_218 = lean_ctor_get(x_216, 0);
lean_inc_ref(x_218);
x_219 = lean_ctor_get(x_216, 2);
lean_inc(x_219);
x_220 = lean_ctor_get(x_216, 3);
lean_inc(x_220);
x_221 = lean_ctor_get(x_216, 4);
lean_inc(x_221);
if (lean_is_exclusive(x_216)) {
 lean_ctor_release(x_216, 0);
 lean_ctor_release(x_216, 1);
 lean_ctor_release(x_216, 2);
 lean_ctor_release(x_216, 3);
 lean_ctor_release(x_216, 4);
 x_222 = x_216;
} else {
 lean_dec_ref(x_216);
 x_222 = lean_box(0);
}
x_223 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__4));
x_224 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__5));
lean_inc_ref(x_218);
x_225 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_225, 0, x_218);
x_226 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_226, 0, x_218);
x_227 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_227, 0, x_225);
lean_ctor_set(x_227, 1, x_226);
x_228 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_228, 0, x_221);
x_229 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_229, 0, x_220);
x_230 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_230, 0, x_219);
if (lean_is_scalar(x_222)) {
 x_231 = lean_alloc_ctor(0, 5, 0);
} else {
 x_231 = x_222;
}
lean_ctor_set(x_231, 0, x_227);
lean_ctor_set(x_231, 1, x_223);
lean_ctor_set(x_231, 2, x_230);
lean_ctor_set(x_231, 3, x_229);
lean_ctor_set(x_231, 4, x_228);
if (lean_is_scalar(x_217)) {
 x_232 = lean_alloc_ctor(0, 2, 0);
} else {
 x_232 = x_217;
}
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_224);
x_233 = l_ReaderT_instMonad___redArg(x_232);
x_234 = l_ReaderT_instMonad___redArg(x_233);
x_235 = l_ReaderT_instMonad___redArg(x_234);
x_236 = l_ReaderT_instMonad___redArg(x_235);
x_237 = l_ReaderT_instMonad___redArg(x_236);
x_238 = l_ReaderT_instMonad___redArg(x_237);
x_239 = l_ReaderT_instMonad___redArg(x_238);
x_240 = l_Lean_Meta_Grind_Order_getStruct(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_240) == 0)
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; uint8_t x_245; 
x_241 = lean_ctor_get(x_240, 0);
lean_inc(x_241);
lean_dec_ref(x_240);
x_242 = lean_ctor_get(x_241, 19);
lean_inc_ref(x_242);
lean_dec(x_241);
x_243 = lean_ctor_get(x_242, 2);
x_244 = lean_box(0);
x_245 = lean_nat_dec_lt(x_1, x_243);
if (x_245 == 0)
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec_ref(x_242);
x_246 = l_outOfBounds___redArg(x_244);
x_247 = l_Lean_AssocList_forM___redArg(x_239, x_2, x_246);
x_248 = lean_apply_12(x_247, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, lean_box(0));
return x_248;
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_249 = l_Lean_PersistentArray_get_x21___redArg(x_244, x_242, x_1);
x_250 = l_Lean_AssocList_forM___redArg(x_239, x_2, x_249);
x_251 = lean_apply_12(x_250, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, lean_box(0));
return x_251;
}
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; 
lean_dec_ref(x_239);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_252 = lean_ctor_get(x_240, 0);
lean_inc(x_252);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 x_253 = x_240;
} else {
 lean_dec_ref(x_240);
 x_253 = lean_box(0);
}
if (lean_is_scalar(x_253)) {
 x_254 = lean_alloc_ctor(1, 1, 0);
} else {
 x_254 = x_253;
}
lean_ctor_set(x_254, 0, x_252);
return x_254;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachTargetOf___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachTargetOf(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isShorter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Meta_Grind_Order_getDist_x3f(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
if (lean_obj_tag(x_18) == 1)
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = l_Lean_Meta_Grind_Order_instDecidableLTWeight(x_3, x_19);
lean_dec(x_19);
x_21 = lean_box(x_20);
lean_ctor_set(x_16, 0, x_21);
return x_16;
}
else
{
uint8_t x_22; lean_object* x_23; 
lean_dec(x_18);
x_22 = 1;
x_23 = lean_box(x_22);
lean_ctor_set(x_16, 0, x_23);
return x_16;
}
}
else
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_16, 0);
lean_inc(x_24);
lean_dec(x_16);
if (lean_obj_tag(x_24) == 1)
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
x_26 = l_Lean_Meta_Grind_Order_instDecidableLTWeight(x_3, x_25);
lean_dec(x_25);
x_27 = lean_box(x_26);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
else
{
uint8_t x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_24);
x_29 = 1;
x_30 = lean_box(x_29);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_16);
if (x_32 == 0)
{
return x_16;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_16, 0);
lean_inc(x_33);
lean_dec(x_16);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isShorter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isShorter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_2, 13);
x_9 = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg___closed__1));
x_10 = l_Lean_Name_append(x_9, x_1);
x_11 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(x_8, x_4, x_10);
lean_dec(x_10);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(x_1, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 21);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set(x_2, 21, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_ctor_get(x_2, 3);
x_10 = lean_ctor_get(x_2, 4);
x_11 = lean_ctor_get(x_2, 5);
x_12 = lean_ctor_get(x_2, 6);
x_13 = lean_ctor_get(x_2, 7);
x_14 = lean_ctor_get(x_2, 8);
x_15 = lean_ctor_get(x_2, 9);
x_16 = lean_ctor_get_uint8(x_2, sizeof(void*)*22);
x_17 = lean_ctor_get(x_2, 10);
x_18 = lean_ctor_get(x_2, 11);
x_19 = lean_ctor_get(x_2, 12);
x_20 = lean_ctor_get(x_2, 13);
x_21 = lean_ctor_get(x_2, 14);
x_22 = lean_ctor_get(x_2, 15);
x_23 = lean_ctor_get(x_2, 16);
x_24 = lean_ctor_get(x_2, 17);
x_25 = lean_ctor_get(x_2, 18);
x_26 = lean_ctor_get(x_2, 19);
x_27 = lean_ctor_get(x_2, 20);
x_28 = lean_ctor_get(x_2, 21);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_1);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(0, 22, 1);
lean_ctor_set(x_30, 0, x_6);
lean_ctor_set(x_30, 1, x_7);
lean_ctor_set(x_30, 2, x_8);
lean_ctor_set(x_30, 3, x_9);
lean_ctor_set(x_30, 4, x_10);
lean_ctor_set(x_30, 5, x_11);
lean_ctor_set(x_30, 6, x_12);
lean_ctor_set(x_30, 7, x_13);
lean_ctor_set(x_30, 8, x_14);
lean_ctor_set(x_30, 9, x_15);
lean_ctor_set(x_30, 10, x_17);
lean_ctor_set(x_30, 11, x_18);
lean_ctor_set(x_30, 12, x_19);
lean_ctor_set(x_30, 13, x_20);
lean_ctor_set(x_30, 14, x_21);
lean_ctor_set(x_30, 15, x_22);
lean_ctor_set(x_30, 16, x_23);
lean_ctor_set(x_30, 17, x_24);
lean_ctor_set(x_30, 18, x_25);
lean_ctor_set(x_30, 19, x_26);
lean_ctor_set(x_30, 20, x_27);
lean_ctor_set(x_30, 21, x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*22, x_16);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_st_ref_get(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_12);
lean_inc_ref(x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_11);
lean_ctor_set(x_13, 3, x_12);
x_14 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___redArg___closed__0() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1_spec__1(x_2, x_3, x_4, x_5, x_6);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_st_ref_take(x_6);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_12, 4);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; double x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___redArg___closed__0;
x_18 = 0;
x_19 = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___redArg___closed__1));
x_20 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set_float(x_20, sizeof(void*)*2, x_17);
lean_ctor_set_float(x_20, sizeof(void*)*2 + 8, x_17);
lean_ctor_set_uint8(x_20, sizeof(void*)*2 + 16, x_18);
x_21 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___redArg___closed__2;
x_22 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_11);
lean_ctor_set(x_22, 2, x_21);
lean_inc(x_8);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_8);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_PersistentArray_push___redArg(x_16, x_23);
lean_ctor_set(x_14, 0, x_24);
x_25 = lean_st_ref_set(x_6, x_12);
x_26 = lean_box(0);
lean_ctor_set(x_9, 0, x_26);
return x_9;
}
else
{
uint64_t x_27; lean_object* x_28; double x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_27 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_28 = lean_ctor_get(x_14, 0);
lean_inc(x_28);
lean_dec(x_14);
x_29 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___redArg___closed__0;
x_30 = 0;
x_31 = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___redArg___closed__1));
x_32 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set_float(x_32, sizeof(void*)*2, x_29);
lean_ctor_set_float(x_32, sizeof(void*)*2 + 8, x_29);
lean_ctor_set_uint8(x_32, sizeof(void*)*2 + 16, x_30);
x_33 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___redArg___closed__2;
x_34 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_11);
lean_ctor_set(x_34, 2, x_33);
lean_inc(x_8);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_8);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_PersistentArray_push___redArg(x_28, x_35);
x_37 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set_uint64(x_37, sizeof(void*)*1, x_27);
lean_ctor_set(x_12, 4, x_37);
x_38 = lean_st_ref_set(x_6, x_12);
x_39 = lean_box(0);
lean_ctor_set(x_9, 0, x_39);
return x_9;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint64_t x_49; lean_object* x_50; lean_object* x_51; double x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_40 = lean_ctor_get(x_12, 4);
x_41 = lean_ctor_get(x_12, 0);
x_42 = lean_ctor_get(x_12, 1);
x_43 = lean_ctor_get(x_12, 2);
x_44 = lean_ctor_get(x_12, 3);
x_45 = lean_ctor_get(x_12, 5);
x_46 = lean_ctor_get(x_12, 6);
x_47 = lean_ctor_get(x_12, 7);
x_48 = lean_ctor_get(x_12, 8);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_40);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_12);
x_49 = lean_ctor_get_uint64(x_40, sizeof(void*)*1);
x_50 = lean_ctor_get(x_40, 0);
lean_inc_ref(x_50);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 x_51 = x_40;
} else {
 lean_dec_ref(x_40);
 x_51 = lean_box(0);
}
x_52 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___redArg___closed__0;
x_53 = 0;
x_54 = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___redArg___closed__1));
x_55 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set_float(x_55, sizeof(void*)*2, x_52);
lean_ctor_set_float(x_55, sizeof(void*)*2 + 8, x_52);
lean_ctor_set_uint8(x_55, sizeof(void*)*2 + 16, x_53);
x_56 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___redArg___closed__2;
x_57 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_11);
lean_ctor_set(x_57, 2, x_56);
lean_inc(x_8);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_8);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_PersistentArray_push___redArg(x_50, x_58);
if (lean_is_scalar(x_51)) {
 x_60 = lean_alloc_ctor(0, 1, 8);
} else {
 x_60 = x_51;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set_uint64(x_60, sizeof(void*)*1, x_49);
x_61 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_61, 0, x_41);
lean_ctor_set(x_61, 1, x_42);
lean_ctor_set(x_61, 2, x_43);
lean_ctor_set(x_61, 3, x_44);
lean_ctor_set(x_61, 4, x_60);
lean_ctor_set(x_61, 5, x_45);
lean_ctor_set(x_61, 6, x_46);
lean_ctor_set(x_61, 7, x_47);
lean_ctor_set(x_61, 8, x_48);
x_62 = lean_st_ref_set(x_6, x_61);
x_63 = lean_box(0);
lean_ctor_set(x_9, 0, x_63);
return x_9;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint64_t x_76; lean_object* x_77; lean_object* x_78; double x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_64 = lean_ctor_get(x_9, 0);
lean_inc(x_64);
lean_dec(x_9);
x_65 = lean_st_ref_take(x_6);
x_66 = lean_ctor_get(x_65, 4);
lean_inc_ref(x_66);
x_67 = lean_ctor_get(x_65, 0);
lean_inc_ref(x_67);
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_65, 2);
lean_inc_ref(x_69);
x_70 = lean_ctor_get(x_65, 3);
lean_inc_ref(x_70);
x_71 = lean_ctor_get(x_65, 5);
lean_inc_ref(x_71);
x_72 = lean_ctor_get(x_65, 6);
lean_inc_ref(x_72);
x_73 = lean_ctor_get(x_65, 7);
lean_inc_ref(x_73);
x_74 = lean_ctor_get(x_65, 8);
lean_inc_ref(x_74);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 lean_ctor_release(x_65, 2);
 lean_ctor_release(x_65, 3);
 lean_ctor_release(x_65, 4);
 lean_ctor_release(x_65, 5);
 lean_ctor_release(x_65, 6);
 lean_ctor_release(x_65, 7);
 lean_ctor_release(x_65, 8);
 x_75 = x_65;
} else {
 lean_dec_ref(x_65);
 x_75 = lean_box(0);
}
x_76 = lean_ctor_get_uint64(x_66, sizeof(void*)*1);
x_77 = lean_ctor_get(x_66, 0);
lean_inc_ref(x_77);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 x_78 = x_66;
} else {
 lean_dec_ref(x_66);
 x_78 = lean_box(0);
}
x_79 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___redArg___closed__0;
x_80 = 0;
x_81 = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___redArg___closed__1));
x_82 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_82, 0, x_1);
lean_ctor_set(x_82, 1, x_81);
lean_ctor_set_float(x_82, sizeof(void*)*2, x_79);
lean_ctor_set_float(x_82, sizeof(void*)*2 + 8, x_79);
lean_ctor_set_uint8(x_82, sizeof(void*)*2 + 16, x_80);
x_83 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___redArg___closed__2;
x_84 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_64);
lean_ctor_set(x_84, 2, x_83);
lean_inc(x_8);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_8);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_Lean_PersistentArray_push___redArg(x_77, x_85);
if (lean_is_scalar(x_78)) {
 x_87 = lean_alloc_ctor(0, 1, 8);
} else {
 x_87 = x_78;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set_uint64(x_87, sizeof(void*)*1, x_76);
if (lean_is_scalar(x_75)) {
 x_88 = lean_alloc_ctor(0, 9, 0);
} else {
 x_88 = x_75;
}
lean_ctor_set(x_88, 0, x_67);
lean_ctor_set(x_88, 1, x_68);
lean_ctor_set(x_88, 2, x_69);
lean_ctor_set(x_88, 3, x_70);
lean_ctor_set(x_88, 4, x_87);
lean_ctor_set(x_88, 5, x_71);
lean_ctor_set(x_88, 6, x_72);
lean_ctor_set(x_88, 7, x_73);
lean_ctor_set(x_88, 8, x_74);
x_89 = lean_st_ref_set(x_6, x_88);
x_90 = lean_box(0);
x_91 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_91, 0, x_90);
return x_91;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___closed__4));
x_15 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(x_14, x_11);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
lean_inc_ref(x_1);
x_17 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___lam__0), 2, 1);
lean_closure_set(x_17, 0, x_1);
x_18 = lean_unbox(x_16);
lean_dec(x_16);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec_ref(x_1);
x_19 = l_Lean_Meta_Grind_Order_modifyStruct___redArg(x_17, x_2, x_3);
return x_19;
}
else
{
lean_object* x_20; 
x_20 = l_Lean_Meta_Grind_Order_ToPropagate_pp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___redArg(x_14, x_21, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
lean_dec_ref(x_22);
x_23 = l_Lean_Meta_Grind_Order_modifyStruct___redArg(x_17, x_2, x_3);
return x_23;
}
else
{
lean_dec_ref(x_17);
lean_dec(x_2);
return x_22;
}
}
else
{
uint8_t x_24; 
lean_dec_ref(x_17);
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_20);
if (x_24 == 0)
{
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_20, 0);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___redArg(x_1, x_2, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_fget_borrowed(x_1, x_3);
x_9 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_4, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
x_3 = x_11;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_fget_borrowed(x_2, x_3);
lean_dec(x_3);
lean_inc(x_13);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0_spec__1___redArg(x_1, x_2, x_3, x_4);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg___closed__0() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 5;
x_2 = 1;
x_3 = lean_usize_shift_left(x_2, x_1);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg___closed__0;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_box(2);
x_7 = 5;
x_8 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg___closed__1;
x_9 = lean_usize_land(x_2, x_8);
x_10 = lean_usize_to_nat(x_9);
x_11 = lean_array_get(x_6, x_5, x_10);
lean_dec(x_10);
lean_dec_ref(x_5);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_3, x_12);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_13);
lean_free_object(x_1);
x_15 = lean_box(0);
return x_15;
}
else
{
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
}
case 1:
{
lean_object* x_16; size_t x_17; 
lean_free_object(x_1);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec_ref(x_11);
x_17 = lean_usize_shift_right(x_2, x_7);
x_1 = x_16;
x_2 = x_17;
goto _start;
}
default: 
{
lean_object* x_19; 
lean_free_object(x_1);
x_19 = lean_box(0);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; size_t x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_box(2);
x_22 = 5;
x_23 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg___closed__1;
x_24 = lean_usize_land(x_2, x_23);
x_25 = lean_usize_to_nat(x_24);
x_26 = lean_array_get(x_21, x_20, x_25);
lean_dec(x_25);
lean_dec_ref(x_20);
switch (lean_obj_tag(x_26)) {
case 0:
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec_ref(x_26);
x_29 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_3, x_27);
lean_dec(x_27);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_28);
x_30 = lean_box(0);
return x_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_28);
return x_31;
}
}
case 1:
{
lean_object* x_32; size_t x_33; 
x_32 = lean_ctor_get(x_26, 0);
lean_inc(x_32);
lean_dec_ref(x_26);
x_33 = lean_usize_shift_right(x_2, x_22);
x_1 = x_32;
x_2 = x_33;
goto _start;
}
default: 
{
lean_object* x_35; 
x_35 = lean_box(0);
return x_35;
}
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_36);
x_37 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_37);
lean_dec_ref(x_1);
x_38 = lean_unsigned_to_nat(0u);
x_39 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0_spec__1___redArg(x_36, x_37, x_38, x_3);
lean_dec_ref(x_37);
lean_dec_ref(x_36);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg(x_1, x_4, x_3);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; lean_object* x_5; 
x_3 = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_Order_propagateEqTrue___closed__4));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateEqTrue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_43; 
x_43 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath(x_3, x_4, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec_ref(x_43);
x_45 = l_Lean_Meta_Grind_Order_getExpr(x_3, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec_ref(x_45);
x_47 = l_Lean_Meta_Grind_Order_getExpr(x_4, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec_ref(x_47);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc_ref(x_12);
lean_inc_ref(x_10);
lean_inc(x_8);
x_49 = l_Lean_Meta_Grind_Order_mkPropagateEqTrueProof(x_46, x_48, x_5, x_44, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_1, 4);
lean_inc(x_50);
if (lean_obj_tag(x_50) == 1)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
lean_dec_ref(x_49);
x_52 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_52);
lean_dec_ref(x_1);
x_53 = lean_ctor_get(x_50, 0);
lean_inc(x_53);
lean_dec_ref(x_50);
x_54 = l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5;
lean_inc_ref(x_2);
x_55 = l_Lean_mkApp4(x_54, x_2, x_52, x_53, x_51);
x_19 = x_55;
x_20 = x_8;
x_21 = x_10;
x_22 = x_12;
x_23 = x_14;
x_24 = x_15;
x_25 = x_16;
x_26 = x_17;
x_27 = lean_box(0);
goto block_42;
}
else
{
lean_object* x_56; 
lean_dec(x_50);
lean_dec_ref(x_1);
x_56 = lean_ctor_get(x_49, 0);
lean_inc(x_56);
lean_dec_ref(x_49);
x_19 = x_56;
x_20 = x_8;
x_21 = x_10;
x_22 = x_12;
x_23 = x_14;
x_24 = x_15;
x_25 = x_16;
x_26 = x_17;
x_27 = lean_box(0);
goto block_42;
}
}
else
{
uint8_t x_57; 
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_12);
lean_dec_ref(x_10);
lean_dec(x_8);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_57 = !lean_is_exclusive(x_49);
if (x_57 == 0)
{
return x_49;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_49, 0);
lean_inc(x_58);
lean_dec(x_49);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_46);
lean_dec(x_44);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_60 = !lean_is_exclusive(x_47);
if (x_60 == 0)
{
return x_47;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_47, 0);
lean_inc(x_61);
lean_dec(x_47);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
return x_62;
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_44);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_63 = !lean_is_exclusive(x_45);
if (x_63 == 0)
{
return x_45;
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_45, 0);
lean_inc(x_64);
lean_dec(x_45);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
return x_65;
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_66 = !lean_is_exclusive(x_43);
if (x_66 == 0)
{
return x_43;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_43, 0);
lean_inc(x_67);
lean_dec(x_43);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_67);
return x_68;
}
}
block_42:
{
lean_object* x_28; 
x_28 = l_Lean_Meta_Grind_Order_get_x27___redArg(x_20, x_25);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = lean_ctor_get(x_29, 4);
lean_inc_ref(x_30);
lean_dec(x_29);
x_31 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(x_30, x_2);
if (lean_obj_tag(x_31) == 1)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec_ref(x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5;
lean_inc(x_33);
x_36 = l_Lean_mkApp4(x_35, x_33, x_2, x_34, x_19);
x_37 = l_Lean_Meta_Grind_pushEqTrue___redArg(x_33, x_36, x_20, x_21, x_22, x_23, x_24, x_25, x_26);
lean_dec_ref(x_22);
lean_dec_ref(x_21);
lean_dec(x_20);
return x_37;
}
else
{
lean_object* x_38; 
lean_dec(x_31);
x_38 = l_Lean_Meta_Grind_pushEqTrue___redArg(x_2, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26);
lean_dec_ref(x_22);
lean_dec_ref(x_21);
lean_dec(x_20);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_26);
lean_dec_ref(x_25);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec_ref(x_22);
lean_dec_ref(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec_ref(x_2);
x_39 = !lean_is_exclusive(x_28);
if (x_39 == 0)
{
return x_28;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_28, 0);
lean_inc(x_40);
lean_dec(x_28);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateEqTrue___boxed(lean_object** _args) {
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
x_19 = l_Lean_Meta_Grind_Order_propagateEqTrue(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0(x_1, x_2, x_5, x_4);
lean_dec_ref(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0_spec__1___redArg(x_2, x_3, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0___closed__0;
x_15 = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_15, 0, x_14);
x_16 = lean_panic_fn(x_15, x_1);
x_17 = lean_apply_12(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, lean_box(0));
return x_17;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__2));
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_unsigned_to_nat(86u);
x_4 = ((lean_object*)(l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__1));
x_5 = ((lean_object*)(l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateSelfEqTrue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
x_17 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_17);
x_18 = lean_ctor_get(x_1, 4);
lean_inc(x_18);
x_19 = l_Lean_Meta_Grind_Order_getExpr(x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = lean_nat_dec_eq(x_15, x_16);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_20);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_22 = l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__3;
x_23 = l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0(x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(x_1);
lean_dec_ref(x_1);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_8);
lean_inc_ref(x_6);
lean_inc(x_4);
x_25 = l_Lean_Meta_Grind_Order_mkPropagateSelfEqTrueProof(x_20, x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
if (lean_obj_tag(x_18) == 1)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_18, 0);
lean_inc(x_50);
lean_dec_ref(x_18);
x_51 = l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5;
lean_inc_ref(x_2);
x_52 = l_Lean_mkApp4(x_51, x_2, x_17, x_50, x_26);
x_27 = x_52;
x_28 = x_4;
x_29 = x_6;
x_30 = x_8;
x_31 = x_10;
x_32 = x_11;
x_33 = x_12;
x_34 = x_13;
goto block_49;
}
else
{
lean_dec(x_18);
lean_dec_ref(x_17);
x_27 = x_26;
x_28 = x_4;
x_29 = x_6;
x_30 = x_8;
x_31 = x_10;
x_32 = x_11;
x_33 = x_12;
x_34 = x_13;
goto block_49;
}
block_49:
{
lean_object* x_35; 
x_35 = l_Lean_Meta_Grind_Order_get_x27___redArg(x_28, x_33);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec_ref(x_35);
x_37 = lean_ctor_get(x_36, 4);
lean_inc_ref(x_37);
lean_dec(x_36);
x_38 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(x_37, x_2);
if (lean_obj_tag(x_38) == 1)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec_ref(x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5;
lean_inc(x_40);
x_43 = l_Lean_mkApp4(x_42, x_40, x_2, x_41, x_27);
x_44 = l_Lean_Meta_Grind_pushEqTrue___redArg(x_40, x_43, x_28, x_29, x_30, x_31, x_32, x_33, x_34);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
return x_44;
}
else
{
lean_object* x_45; 
lean_dec(x_38);
x_45 = l_Lean_Meta_Grind_pushEqTrue___redArg(x_2, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_34);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
return x_45;
}
}
else
{
uint8_t x_46; 
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec_ref(x_2);
x_46 = !lean_is_exclusive(x_35);
if (x_46 == 0)
{
return x_35;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_35, 0);
lean_inc(x_47);
lean_dec(x_35);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec_ref(x_2);
x_53 = !lean_is_exclusive(x_25);
if (x_53 == 0)
{
return x_25;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_25, 0);
lean_inc(x_54);
lean_dec(x_25);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_56 = !lean_is_exclusive(x_19);
if (x_56 == 0)
{
return x_19;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_19, 0);
lean_inc(x_57);
lean_dec(x_19);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateSelfEqTrue___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Grind_Order_propagateSelfEqTrue(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_Order_propagateEqFalse___closed__1));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateEqFalse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_43; 
x_43 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath(x_3, x_4, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec_ref(x_43);
x_45 = l_Lean_Meta_Grind_Order_getExpr(x_3, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec_ref(x_45);
x_47 = l_Lean_Meta_Grind_Order_getExpr(x_4, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec_ref(x_47);
x_49 = l_Lean_Meta_Grind_Order_mkPropagateEqFalseProof(x_46, x_48, x_5, x_44, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_1, 4);
lean_inc(x_50);
if (lean_obj_tag(x_50) == 1)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
lean_dec_ref(x_49);
x_52 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_52);
lean_dec_ref(x_1);
x_53 = lean_ctor_get(x_50, 0);
lean_inc(x_53);
lean_dec_ref(x_50);
x_54 = l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2;
lean_inc_ref(x_2);
x_55 = l_Lean_mkApp4(x_54, x_2, x_52, x_53, x_51);
x_19 = x_55;
x_20 = x_8;
x_21 = x_10;
x_22 = x_12;
x_23 = x_14;
x_24 = x_15;
x_25 = x_16;
x_26 = x_17;
x_27 = lean_box(0);
goto block_42;
}
else
{
lean_object* x_56; 
lean_dec(x_50);
lean_dec_ref(x_1);
x_56 = lean_ctor_get(x_49, 0);
lean_inc(x_56);
lean_dec_ref(x_49);
x_19 = x_56;
x_20 = x_8;
x_21 = x_10;
x_22 = x_12;
x_23 = x_14;
x_24 = x_15;
x_25 = x_16;
x_26 = x_17;
x_27 = lean_box(0);
goto block_42;
}
}
else
{
uint8_t x_57; 
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_57 = !lean_is_exclusive(x_49);
if (x_57 == 0)
{
return x_49;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_49, 0);
lean_inc(x_58);
lean_dec(x_49);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_46);
lean_dec(x_44);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_60 = !lean_is_exclusive(x_47);
if (x_60 == 0)
{
return x_47;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_47, 0);
lean_inc(x_61);
lean_dec(x_47);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
return x_62;
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_44);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_63 = !lean_is_exclusive(x_45);
if (x_63 == 0)
{
return x_45;
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_45, 0);
lean_inc(x_64);
lean_dec(x_45);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
return x_65;
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_66 = !lean_is_exclusive(x_43);
if (x_66 == 0)
{
return x_43;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_43, 0);
lean_inc(x_67);
lean_dec(x_43);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_67);
return x_68;
}
}
block_42:
{
lean_object* x_28; 
x_28 = l_Lean_Meta_Grind_Order_get_x27___redArg(x_20, x_25);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = lean_ctor_get(x_29, 4);
lean_inc_ref(x_30);
lean_dec(x_29);
x_31 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(x_30, x_2);
if (lean_obj_tag(x_31) == 1)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec_ref(x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2;
lean_inc(x_33);
x_36 = l_Lean_mkApp4(x_35, x_33, x_2, x_34, x_19);
x_37 = l_Lean_Meta_Grind_pushEqFalse___redArg(x_33, x_36, x_20, x_21, x_22, x_23, x_24, x_25, x_26);
return x_37;
}
else
{
lean_object* x_38; 
lean_dec(x_31);
x_38 = l_Lean_Meta_Grind_pushEqFalse___redArg(x_2, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_26);
lean_dec_ref(x_25);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec_ref(x_19);
lean_dec_ref(x_2);
x_39 = !lean_is_exclusive(x_28);
if (x_39 == 0)
{
return x_28;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_28, 0);
lean_inc(x_40);
lean_dec(x_28);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateEqFalse___boxed(lean_object** _args) {
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
x_19 = l_Lean_Meta_Grind_Order_propagateEqFalse(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_19;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_propagateSelfEqFalse___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__2));
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_unsigned_to_nat(111u);
x_4 = ((lean_object*)(l_Lean_Meta_Grind_Order_propagateSelfEqFalse___closed__0));
x_5 = ((lean_object*)(l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateSelfEqFalse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
x_17 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_17);
x_18 = lean_ctor_get(x_1, 4);
lean_inc(x_18);
x_19 = l_Lean_Meta_Grind_Order_getExpr(x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = lean_nat_dec_eq(x_15, x_16);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_20);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_22 = l_Lean_Meta_Grind_Order_propagateSelfEqFalse___closed__1;
x_23 = l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0(x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(x_1);
lean_dec_ref(x_1);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_8);
lean_inc_ref(x_6);
lean_inc(x_4);
x_25 = l_Lean_Meta_Grind_Order_mkPropagateSelfEqFalseProof(x_20, x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
if (lean_obj_tag(x_18) == 1)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_18, 0);
lean_inc(x_50);
lean_dec_ref(x_18);
x_51 = l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2;
lean_inc_ref(x_2);
x_52 = l_Lean_mkApp4(x_51, x_2, x_17, x_50, x_26);
x_27 = x_52;
x_28 = x_4;
x_29 = x_6;
x_30 = x_8;
x_31 = x_10;
x_32 = x_11;
x_33 = x_12;
x_34 = x_13;
goto block_49;
}
else
{
lean_dec(x_18);
lean_dec_ref(x_17);
x_27 = x_26;
x_28 = x_4;
x_29 = x_6;
x_30 = x_8;
x_31 = x_10;
x_32 = x_11;
x_33 = x_12;
x_34 = x_13;
goto block_49;
}
block_49:
{
lean_object* x_35; 
x_35 = l_Lean_Meta_Grind_Order_get_x27___redArg(x_28, x_33);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec_ref(x_35);
x_37 = lean_ctor_get(x_36, 4);
lean_inc_ref(x_37);
lean_dec(x_36);
x_38 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(x_37, x_2);
if (lean_obj_tag(x_38) == 1)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec_ref(x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2;
lean_inc(x_40);
x_43 = l_Lean_mkApp4(x_42, x_40, x_2, x_41, x_27);
x_44 = l_Lean_Meta_Grind_pushEqFalse___redArg(x_40, x_43, x_28, x_29, x_30, x_31, x_32, x_33, x_34);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
return x_44;
}
else
{
lean_object* x_45; 
lean_dec(x_38);
x_45 = l_Lean_Meta_Grind_pushEqFalse___redArg(x_2, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_34);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
return x_45;
}
}
else
{
uint8_t x_46; 
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec_ref(x_2);
x_46 = !lean_is_exclusive(x_35);
if (x_46 == 0)
{
return x_35;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_35, 0);
lean_inc(x_47);
lean_dec(x_35);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec_ref(x_2);
x_53 = !lean_is_exclusive(x_25);
if (x_53 == 0)
{
return x_25;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_25, 0);
lean_inc(x_54);
lean_dec(x_25);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_56 = !lean_is_exclusive(x_19);
if (x_56 == 0)
{
return x_19;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_19, 0);
lean_inc(x_57);
lean_dec(x_19);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_propagateSelfEqFalse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Grind_Order_propagateSelfEqFalse(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_Order_get_x27___redArg(x_2, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 4);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(x_8, x_1);
lean_ctor_set(x_5, 0, x_9);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_ctor_get(x_10, 4);
lean_inc_ref(x_11);
lean_dec(x_10);
x_12 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(x_11, x_1);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
return x_5;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_5, 0);
lean_inc(x_15);
lean_dec(x_5);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f___redArg(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f___redArg(x_1, x_2, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending___lam__0(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 21);
lean_dec(x_3);
x_4 = lean_box(0);
lean_ctor_set(x_1, 21, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_1, 2);
x_8 = lean_ctor_get(x_1, 3);
x_9 = lean_ctor_get(x_1, 4);
x_10 = lean_ctor_get(x_1, 5);
x_11 = lean_ctor_get(x_1, 6);
x_12 = lean_ctor_get(x_1, 7);
x_13 = lean_ctor_get(x_1, 8);
x_14 = lean_ctor_get(x_1, 9);
x_15 = lean_ctor_get_uint8(x_1, sizeof(void*)*22);
x_16 = lean_ctor_get(x_1, 10);
x_17 = lean_ctor_get(x_1, 11);
x_18 = lean_ctor_get(x_1, 12);
x_19 = lean_ctor_get(x_1, 13);
x_20 = lean_ctor_get(x_1, 14);
x_21 = lean_ctor_get(x_1, 15);
x_22 = lean_ctor_get(x_1, 16);
x_23 = lean_ctor_get(x_1, 17);
x_24 = lean_ctor_get(x_1, 18);
x_25 = lean_ctor_get(x_1, 19);
x_26 = lean_ctor_get(x_1, 20);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 22, 1);
lean_ctor_set(x_28, 0, x_5);
lean_ctor_set(x_28, 1, x_6);
lean_ctor_set(x_28, 2, x_7);
lean_ctor_set(x_28, 3, x_8);
lean_ctor_set(x_28, 4, x_9);
lean_ctor_set(x_28, 5, x_10);
lean_ctor_set(x_28, 6, x_11);
lean_ctor_set(x_28, 7, x_12);
lean_ctor_set(x_28, 8, x_13);
lean_ctor_set(x_28, 9, x_14);
lean_ctor_set(x_28, 10, x_16);
lean_ctor_set(x_28, 11, x_17);
lean_ctor_set(x_28, 12, x_18);
lean_ctor_set(x_28, 13, x_19);
lean_ctor_set(x_28, 14, x_20);
lean_ctor_set(x_28, 15, x_21);
lean_ctor_set(x_28, 16, x_22);
lean_ctor_set(x_28, 17, x_23);
lean_ctor_set(x_28, 18, x_24);
lean_ctor_set(x_28, 19, x_25);
lean_ctor_set(x_28, 20, x_26);
lean_ctor_set(x_28, 21, x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*22, x_15);
return x_28;
}
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg___closed__1));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_15; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_2);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_dec_ref(x_1);
x_18 = lean_box(0);
switch (lean_obj_tag(x_16)) {
case 0:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_16, 0);
lean_inc_ref(x_19);
x_20 = lean_ctor_get(x_16, 1);
lean_inc_ref(x_20);
x_21 = lean_ctor_get(x_16, 2);
lean_inc(x_21);
x_22 = lean_ctor_get(x_16, 3);
lean_inc(x_22);
x_23 = lean_ctor_get(x_16, 4);
lean_inc_ref(x_23);
x_24 = lean_ctor_get(x_16, 5);
lean_inc_ref(x_24);
lean_dec_ref(x_16);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_25 = l_Lean_Meta_Grind_Order_propagateEqTrue(x_19, x_20, x_21, x_22, x_23, x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec(x_21);
if (lean_obj_tag(x_25) == 0)
{
lean_dec_ref(x_25);
x_1 = x_17;
x_2 = x_18;
goto _start;
}
else
{
lean_dec(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_25;
}
}
case 1:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_16, 0);
lean_inc_ref(x_27);
x_28 = lean_ctor_get(x_16, 1);
lean_inc_ref(x_28);
x_29 = lean_ctor_get(x_16, 2);
lean_inc(x_29);
x_30 = lean_ctor_get(x_16, 3);
lean_inc(x_30);
x_31 = lean_ctor_get(x_16, 4);
lean_inc_ref(x_31);
x_32 = lean_ctor_get(x_16, 5);
lean_inc_ref(x_32);
lean_dec_ref(x_16);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
x_33 = l_Lean_Meta_Grind_Order_propagateEqFalse(x_27, x_28, x_29, x_30, x_31, x_32, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec(x_29);
if (lean_obj_tag(x_33) == 0)
{
lean_dec_ref(x_33);
x_1 = x_17;
x_2 = x_18;
goto _start;
}
else
{
lean_dec(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_33;
}
}
default: 
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_16, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_16, 1);
lean_inc(x_36);
lean_dec_ref(x_16);
x_37 = l_Lean_Meta_Grind_Order_getExpr(x_35, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
x_39 = l_Lean_Meta_Grind_Order_getExpr(x_36, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_126; lean_object* x_156; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec_ref(x_39);
x_156 = l_Lean_Meta_Grind_alreadyInternalized___redArg(x_38, x_4);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; uint8_t x_158; 
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_unbox(x_157);
lean_dec(x_157);
if (x_158 == 0)
{
x_126 = x_156;
goto block_155;
}
else
{
lean_object* x_159; 
lean_dec_ref(x_156);
x_159 = l_Lean_Meta_Grind_alreadyInternalized___redArg(x_40, x_4);
x_126 = x_159;
goto block_155;
}
}
else
{
x_126 = x_156;
goto block_155;
}
block_90:
{
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_dec_ref(x_56);
x_58 = lean_unbox(x_57);
lean_dec(x_57);
if (x_58 == 0)
{
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec_ref(x_47);
lean_dec_ref(x_46);
lean_dec_ref(x_45);
lean_dec_ref(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_35);
x_1 = x_17;
x_2 = x_18;
goto _start;
}
else
{
lean_object* x_60; 
x_60 = l_Lean_Meta_Grind_isEqv___redArg(x_45, x_55, x_52);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
lean_dec_ref(x_60);
x_62 = lean_unbox(x_61);
if (x_62 == 0)
{
lean_object* x_63; 
x_63 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath(x_35, x_36, x_42, x_52, x_54, x_46, x_53, x_44, x_48, x_47, x_49, x_51, x_43);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
lean_dec_ref(x_63);
x_65 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath(x_36, x_35, x_42, x_52, x_54, x_46, x_53, x_44, x_48, x_47, x_49, x_51, x_43);
lean_dec(x_35);
lean_dec(x_36);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
lean_dec_ref(x_65);
lean_inc(x_40);
lean_inc(x_38);
x_67 = l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLe(x_38, x_40, x_64, x_66, x_42, x_52, x_54, x_46, x_53, x_44, x_48, x_47, x_49, x_51, x_43);
lean_dec(x_48);
lean_dec_ref(x_44);
lean_dec(x_53);
lean_dec(x_54);
lean_dec(x_42);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
lean_dec_ref(x_67);
x_69 = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg___closed__2;
lean_inc_ref(x_55);
lean_inc_ref(x_45);
x_70 = l_Lean_mkApp7(x_69, x_45, x_55, x_38, x_40, x_50, x_41, x_68);
x_71 = lean_unbox(x_61);
lean_dec(x_61);
x_72 = l_Lean_Meta_Grind_pushEqCore___redArg(x_45, x_55, x_70, x_71, x_52, x_46, x_47, x_49, x_51, x_43);
lean_dec_ref(x_46);
lean_dec(x_52);
if (lean_obj_tag(x_72) == 0)
{
lean_dec_ref(x_72);
x_1 = x_17;
x_2 = x_18;
goto _start;
}
else
{
lean_dec(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_72;
}
}
else
{
uint8_t x_74; 
lean_dec(x_61);
lean_dec_ref(x_55);
lean_dec(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_50);
lean_dec(x_49);
lean_dec_ref(x_47);
lean_dec_ref(x_46);
lean_dec_ref(x_45);
lean_dec(x_43);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_74 = !lean_is_exclusive(x_67);
if (x_74 == 0)
{
return x_67;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_67, 0);
lean_inc(x_75);
lean_dec(x_67);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_75);
return x_76;
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_64);
lean_dec(x_61);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec_ref(x_47);
lean_dec_ref(x_46);
lean_dec_ref(x_45);
lean_dec_ref(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_77 = !lean_is_exclusive(x_65);
if (x_77 == 0)
{
return x_65;
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_65, 0);
lean_inc(x_78);
lean_dec(x_65);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_78);
return x_79;
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_61);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec_ref(x_47);
lean_dec_ref(x_46);
lean_dec_ref(x_45);
lean_dec_ref(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_80 = !lean_is_exclusive(x_63);
if (x_80 == 0)
{
return x_63;
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_63, 0);
lean_inc(x_81);
lean_dec(x_63);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_81);
return x_82;
}
}
}
else
{
lean_dec(x_61);
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec_ref(x_47);
lean_dec_ref(x_46);
lean_dec_ref(x_45);
lean_dec_ref(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_35);
x_1 = x_17;
x_2 = x_18;
goto _start;
}
}
else
{
uint8_t x_84; 
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec_ref(x_47);
lean_dec_ref(x_46);
lean_dec_ref(x_45);
lean_dec_ref(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_84 = !lean_is_exclusive(x_60);
if (x_84 == 0)
{
return x_60;
}
else
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_60, 0);
lean_inc(x_85);
lean_dec(x_60);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_85);
return x_86;
}
}
}
}
else
{
uint8_t x_87; 
lean_dec_ref(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec_ref(x_47);
lean_dec_ref(x_46);
lean_dec_ref(x_45);
lean_dec_ref(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_87 = !lean_is_exclusive(x_56);
if (x_87 == 0)
{
return x_56;
}
else
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_56, 0);
lean_inc(x_88);
lean_dec(x_56);
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_88);
return x_89;
}
}
}
block_125:
{
lean_object* x_103; 
x_103 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f___redArg(x_38, x_92, x_100);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
lean_dec_ref(x_103);
if (lean_obj_tag(x_104) == 1)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
lean_dec_ref(x_104);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_getOriginal_x3f___redArg(x_40, x_92, x_100);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
lean_dec_ref(x_108);
if (lean_obj_tag(x_109) == 1)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
lean_dec_ref(x_109);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
x_113 = l_Lean_Meta_Grind_alreadyInternalized___redArg(x_106, x_92);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; uint8_t x_115; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_unbox(x_114);
lean_dec(x_114);
if (x_115 == 0)
{
x_41 = x_112;
x_42 = x_91;
x_43 = x_101;
x_44 = x_96;
x_45 = x_106;
x_46 = x_94;
x_47 = x_98;
x_48 = x_97;
x_49 = x_99;
x_50 = x_107;
x_51 = x_100;
x_52 = x_92;
x_53 = x_95;
x_54 = x_93;
x_55 = x_111;
x_56 = x_113;
goto block_90;
}
else
{
lean_object* x_116; 
lean_dec_ref(x_113);
x_116 = l_Lean_Meta_Grind_alreadyInternalized___redArg(x_111, x_92);
x_41 = x_112;
x_42 = x_91;
x_43 = x_101;
x_44 = x_96;
x_45 = x_106;
x_46 = x_94;
x_47 = x_98;
x_48 = x_97;
x_49 = x_99;
x_50 = x_107;
x_51 = x_100;
x_52 = x_92;
x_53 = x_95;
x_54 = x_93;
x_55 = x_111;
x_56 = x_116;
goto block_90;
}
}
else
{
x_41 = x_112;
x_42 = x_91;
x_43 = x_101;
x_44 = x_96;
x_45 = x_106;
x_46 = x_94;
x_47 = x_98;
x_48 = x_97;
x_49 = x_99;
x_50 = x_107;
x_51 = x_100;
x_52 = x_92;
x_53 = x_95;
x_54 = x_93;
x_55 = x_111;
x_56 = x_113;
goto block_90;
}
}
else
{
lean_dec(x_109);
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_101);
lean_dec_ref(x_100);
lean_dec(x_99);
lean_dec_ref(x_98);
lean_dec(x_97);
lean_dec_ref(x_96);
lean_dec(x_95);
lean_dec_ref(x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_35);
x_1 = x_17;
x_2 = x_18;
goto _start;
}
}
else
{
uint8_t x_118; 
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_101);
lean_dec_ref(x_100);
lean_dec(x_99);
lean_dec_ref(x_98);
lean_dec(x_97);
lean_dec_ref(x_96);
lean_dec(x_95);
lean_dec_ref(x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_118 = !lean_is_exclusive(x_108);
if (x_118 == 0)
{
return x_108;
}
else
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_108, 0);
lean_inc(x_119);
lean_dec(x_108);
x_120 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_120, 0, x_119);
return x_120;
}
}
}
else
{
lean_dec(x_104);
lean_dec(x_101);
lean_dec_ref(x_100);
lean_dec(x_99);
lean_dec_ref(x_98);
lean_dec(x_97);
lean_dec_ref(x_96);
lean_dec(x_95);
lean_dec_ref(x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_35);
x_1 = x_17;
x_2 = x_18;
goto _start;
}
}
else
{
uint8_t x_122; 
lean_dec(x_101);
lean_dec_ref(x_100);
lean_dec(x_99);
lean_dec_ref(x_98);
lean_dec(x_97);
lean_dec_ref(x_96);
lean_dec(x_95);
lean_dec_ref(x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_122 = !lean_is_exclusive(x_103);
if (x_122 == 0)
{
return x_103;
}
else
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_ctor_get(x_103, 0);
lean_inc(x_123);
lean_dec(x_103);
x_124 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_124, 0, x_123);
return x_124;
}
}
}
block_155:
{
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; uint8_t x_128; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
lean_dec_ref(x_126);
x_128 = lean_unbox(x_127);
lean_dec(x_127);
if (x_128 == 0)
{
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_91 = x_3;
x_92 = x_4;
x_93 = x_5;
x_94 = x_6;
x_95 = x_7;
x_96 = x_8;
x_97 = x_9;
x_98 = x_10;
x_99 = x_11;
x_100 = x_12;
x_101 = x_13;
x_102 = lean_box(0);
goto block_125;
}
else
{
lean_object* x_129; 
x_129 = l_Lean_Meta_Grind_isEqv___redArg(x_38, x_40, x_4);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; uint8_t x_131; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
lean_dec_ref(x_129);
x_131 = lean_unbox(x_130);
if (x_131 == 0)
{
lean_object* x_132; 
x_132 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath(x_35, x_36, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
lean_dec_ref(x_132);
x_134 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_mkProofForPath(x_36, x_35, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
lean_dec_ref(x_134);
lean_inc(x_40);
lean_inc(x_38);
x_136 = l_Lean_Meta_Grind_Order_mkEqProofOfLeOfLe(x_38, x_40, x_133, x_135, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; uint8_t x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
lean_dec_ref(x_136);
x_138 = lean_unbox(x_130);
lean_dec(x_130);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_40);
lean_inc(x_38);
x_139 = l_Lean_Meta_Grind_pushEqCore___redArg(x_38, x_40, x_137, x_138, x_4, x_6, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_139) == 0)
{
lean_dec_ref(x_139);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_91 = x_3;
x_92 = x_4;
x_93 = x_5;
x_94 = x_6;
x_95 = x_7;
x_96 = x_8;
x_97 = x_9;
x_98 = x_10;
x_99 = x_11;
x_100 = x_12;
x_101 = x_13;
x_102 = lean_box(0);
goto block_125;
}
else
{
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_139;
}
}
else
{
uint8_t x_140; 
lean_dec(x_130);
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_140 = !lean_is_exclusive(x_136);
if (x_140 == 0)
{
return x_136;
}
else
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_ctor_get(x_136, 0);
lean_inc(x_141);
lean_dec(x_136);
x_142 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_142, 0, x_141);
return x_142;
}
}
}
else
{
uint8_t x_143; 
lean_dec(x_133);
lean_dec(x_130);
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_143 = !lean_is_exclusive(x_134);
if (x_143 == 0)
{
return x_134;
}
else
{
lean_object* x_144; lean_object* x_145; 
x_144 = lean_ctor_get(x_134, 0);
lean_inc(x_144);
lean_dec(x_134);
x_145 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_145, 0, x_144);
return x_145;
}
}
}
else
{
uint8_t x_146; 
lean_dec(x_130);
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_146 = !lean_is_exclusive(x_132);
if (x_146 == 0)
{
return x_132;
}
else
{
lean_object* x_147; lean_object* x_148; 
x_147 = lean_ctor_get(x_132, 0);
lean_inc(x_147);
lean_dec(x_132);
x_148 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_148, 0, x_147);
return x_148;
}
}
}
else
{
lean_dec(x_130);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_91 = x_3;
x_92 = x_4;
x_93 = x_5;
x_94 = x_6;
x_95 = x_7;
x_96 = x_8;
x_97 = x_9;
x_98 = x_10;
x_99 = x_11;
x_100 = x_12;
x_101 = x_13;
x_102 = lean_box(0);
goto block_125;
}
}
else
{
uint8_t x_149; 
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_149 = !lean_is_exclusive(x_129);
if (x_149 == 0)
{
return x_129;
}
else
{
lean_object* x_150; lean_object* x_151; 
x_150 = lean_ctor_get(x_129, 0);
lean_inc(x_150);
lean_dec(x_129);
x_151 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_151, 0, x_150);
return x_151;
}
}
}
}
else
{
uint8_t x_152; 
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_152 = !lean_is_exclusive(x_126);
if (x_152 == 0)
{
return x_126;
}
else
{
lean_object* x_153; lean_object* x_154; 
x_153 = lean_ctor_get(x_126, 0);
lean_inc(x_153);
lean_dec(x_126);
x_154 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_154, 0, x_153);
return x_154;
}
}
}
}
else
{
uint8_t x_160; 
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_160 = !lean_is_exclusive(x_39);
if (x_160 == 0)
{
return x_39;
}
else
{
lean_object* x_161; lean_object* x_162; 
x_161 = lean_ctor_get(x_39, 0);
lean_inc(x_161);
lean_dec(x_39);
x_162 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_162, 0, x_161);
return x_162;
}
}
}
else
{
uint8_t x_163; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_163 = !lean_is_exclusive(x_37);
if (x_163 == 0)
{
return x_37;
}
else
{
lean_object* x_164; lean_object* x_165; 
x_164 = lean_ctor_get(x_37, 0);
lean_inc(x_164);
lean_dec(x_37);
x_165 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_165, 0, x_164);
return x_165;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Order_getStruct(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending___closed__0));
lean_inc(x_1);
x_16 = l_Lean_Meta_Grind_Order_modifyStruct___redArg(x_15, x_1, x_2);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec_ref(x_16);
x_17 = lean_ctor_get(x_14, 21);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_box(0);
x_19 = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg(x_17, x_18, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
else
{
lean_object* x_22; 
lean_dec(x_19);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_18);
return x_22;
}
}
else
{
return x_19;
}
}
else
{
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
else
{
uint8_t x_23; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_13);
if (x_23 == 0)
{
return x_13;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_13, 0);
lean_inc(x_24);
lean_dec(x_13);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; 
x_17 = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg(x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_17;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Grind_Order_get_x27___redArg(x_2, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = lean_ctor_get(x_10, 4);
lean_inc_ref(x_11);
lean_dec(x_10);
x_12 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(x_11, x_1);
if (lean_obj_tag(x_12) == 1)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec_ref(x_1);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_Meta_Grind_alreadyInternalized___redArg(x_14, x_2);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_dec(x_14);
return x_15;
}
else
{
lean_object* x_18; 
lean_dec_ref(x_15);
x_18 = l_Lean_Meta_Grind_isEqTrue___redArg(x_14, x_2, x_3, x_4, x_5, x_6, x_7);
return x_18;
}
}
else
{
lean_dec(x_14);
return x_15;
}
}
else
{
lean_object* x_19; 
lean_dec(x_12);
x_19 = l_Lean_Meta_Grind_alreadyInternalized___redArg(x_1, x_2);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_dec_ref(x_1);
return x_19;
}
else
{
lean_object* x_22; 
lean_dec_ref(x_19);
x_22 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_22;
}
}
else
{
lean_dec_ref(x_1);
return x_19;
}
}
}
else
{
uint8_t x_23; 
lean_dec_ref(x_1);
x_23 = !lean_is_exclusive(x_9);
if (x_23 == 0)
{
return x_9;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_9, 0);
lean_inc(x_24);
lean_dec(x_9);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue___redArg(x_1, x_3, x_7, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_18; 
lean_inc_ref(x_5);
x_18 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyTrue___redArg(x_5, x_7, x_11, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_45; 
lean_free_object(x_18);
x_22 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__1));
x_23 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(x_22, x_15);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 x_25 = x_23;
} else {
 lean_dec_ref(x_23);
 x_25 = lean_box(0);
}
x_26 = l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(x_4);
x_27 = l_Lean_Meta_Grind_Order_instDecidableLEWeight(x_3, x_26);
x_45 = lean_unbox(x_24);
lean_dec(x_24);
if (x_45 == 0)
{
x_28 = x_6;
x_29 = x_7;
x_30 = x_8;
x_31 = x_9;
x_32 = x_10;
x_33 = x_11;
x_34 = x_12;
x_35 = x_13;
x_36 = x_14;
x_37 = x_15;
x_38 = x_16;
x_39 = lean_box(0);
goto block_44;
}
else
{
lean_object* x_46; 
x_46 = l_Lean_Meta_Grind_Order_getExpr(x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec_ref(x_46);
x_48 = l_Lean_Meta_Grind_Order_getExpr(x_2, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec_ref(x_48);
x_50 = l_Lean_Meta_Grind_Order_Cnstr_pp(x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_65; lean_object* x_66; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_104; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_dec_ref(x_50);
x_52 = lean_ctor_get(x_3, 0);
x_53 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
x_54 = l_Lean_MessageData_ofExpr(x_47);
x_55 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__3;
x_70 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_70, 0, x_54);
lean_ctor_set(x_70, 1, x_55);
x_71 = l_Lean_MessageData_ofExpr(x_49);
x_72 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_55);
if (x_53 == 0)
{
lean_object* x_108; uint8_t x_109; 
x_108 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5;
x_109 = lean_int_dec_lt(x_52, x_108);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_nat_abs(x_52);
x_111 = l_Nat_reprFast(x_110);
x_74 = x_111;
goto block_103;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_112 = lean_nat_abs(x_52);
x_113 = lean_unsigned_to_nat(1u);
x_114 = lean_nat_sub(x_112, x_113);
lean_dec(x_112);
x_115 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__6));
x_116 = lean_nat_add(x_114, x_113);
lean_dec(x_114);
x_117 = l_Nat_reprFast(x_116);
x_118 = lean_string_append(x_115, x_117);
lean_dec_ref(x_117);
x_74 = x_118;
goto block_103;
}
}
else
{
lean_object* x_119; uint8_t x_120; 
x_119 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5;
x_120 = lean_int_dec_lt(x_52, x_119);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; 
x_121 = lean_nat_abs(x_52);
x_122 = l_Nat_reprFast(x_121);
x_104 = x_122;
goto block_107;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_123 = lean_nat_abs(x_52);
x_124 = lean_unsigned_to_nat(1u);
x_125 = lean_nat_sub(x_123, x_124);
lean_dec(x_123);
x_126 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__6));
x_127 = lean_nat_add(x_125, x_124);
lean_dec(x_125);
x_128 = l_Nat_reprFast(x_127);
x_129 = lean_string_append(x_126, x_128);
lean_dec_ref(x_128);
x_104 = x_129;
goto block_107;
}
}
block_64:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_58 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_58, 0, x_57);
x_59 = l_Lean_MessageData_ofFormat(x_58);
x_60 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_60, 0, x_56);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_55);
x_62 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_51);
x_63 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___redArg(x_22, x_62, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_63) == 0)
{
lean_dec_ref(x_63);
x_28 = x_6;
x_29 = x_7;
x_30 = x_8;
x_31 = x_9;
x_32 = x_10;
x_33 = x_11;
x_34 = x_12;
x_35 = x_13;
x_36 = x_14;
x_37 = x_15;
x_38 = x_16;
x_39 = lean_box(0);
goto block_44;
}
else
{
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_63;
}
}
block_69:
{
lean_object* x_67; lean_object* x_68; 
x_67 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4));
x_68 = lean_string_append(x_66, x_67);
x_56 = x_65;
x_57 = x_68;
goto block_64;
}
block_103:
{
lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_75 = lean_ctor_get(x_26, 0);
lean_inc(x_75);
x_76 = lean_ctor_get_uint8(x_26, sizeof(void*)*1);
x_77 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_77, 0, x_74);
x_78 = l_Lean_MessageData_ofFormat(x_77);
x_79 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_79, 0, x_73);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_55);
if (x_76 == 0)
{
lean_object* x_81; uint8_t x_82; 
x_81 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5;
x_82 = lean_int_dec_lt(x_75, x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_nat_abs(x_75);
lean_dec(x_75);
x_84 = l_Nat_reprFast(x_83);
x_56 = x_80;
x_57 = x_84;
goto block_64;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_85 = lean_nat_abs(x_75);
lean_dec(x_75);
x_86 = lean_unsigned_to_nat(1u);
x_87 = lean_nat_sub(x_85, x_86);
lean_dec(x_85);
x_88 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__6));
x_89 = lean_nat_add(x_87, x_86);
lean_dec(x_87);
x_90 = l_Nat_reprFast(x_89);
x_91 = lean_string_append(x_88, x_90);
lean_dec_ref(x_90);
x_56 = x_80;
x_57 = x_91;
goto block_64;
}
}
else
{
lean_object* x_92; uint8_t x_93; 
x_92 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5;
x_93 = lean_int_dec_lt(x_75, x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_nat_abs(x_75);
lean_dec(x_75);
x_95 = l_Nat_reprFast(x_94);
x_65 = x_80;
x_66 = x_95;
goto block_69;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_96 = lean_nat_abs(x_75);
lean_dec(x_75);
x_97 = lean_unsigned_to_nat(1u);
x_98 = lean_nat_sub(x_96, x_97);
lean_dec(x_96);
x_99 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__6));
x_100 = lean_nat_add(x_98, x_97);
lean_dec(x_98);
x_101 = l_Nat_reprFast(x_100);
x_102 = lean_string_append(x_99, x_101);
lean_dec_ref(x_101);
x_65 = x_80;
x_66 = x_102;
goto block_69;
}
}
}
block_107:
{
lean_object* x_105; lean_object* x_106; 
x_105 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4));
x_106 = lean_string_append(x_104, x_105);
x_74 = x_106;
goto block_103;
}
}
else
{
uint8_t x_130; 
lean_dec(x_49);
lean_dec(x_47);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_130 = !lean_is_exclusive(x_50);
if (x_130 == 0)
{
return x_50;
}
else
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_50, 0);
lean_inc(x_131);
lean_dec(x_50);
x_132 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_132, 0, x_131);
return x_132;
}
}
}
else
{
uint8_t x_133; 
lean_dec(x_47);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_133 = !lean_is_exclusive(x_48);
if (x_133 == 0)
{
return x_48;
}
else
{
lean_object* x_134; lean_object* x_135; 
x_134 = lean_ctor_get(x_48, 0);
lean_inc(x_134);
lean_dec(x_48);
x_135 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_135, 0, x_134);
return x_135;
}
}
}
else
{
uint8_t x_136; 
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_136 = !lean_is_exclusive(x_46);
if (x_136 == 0)
{
return x_46;
}
else
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_46, 0);
lean_inc(x_137);
lean_dec(x_46);
x_138 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_138, 0, x_137);
return x_138;
}
}
}
block_44:
{
if (x_27 == 0)
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_28);
lean_dec_ref(x_26);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = lean_box(0);
if (lean_is_scalar(x_25)) {
 x_41 = lean_alloc_ctor(0, 1, 0);
} else {
 x_41 = x_25;
}
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_25);
x_42 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_42, 0, x_4);
lean_ctor_set(x_42, 1, x_5);
lean_ctor_set(x_42, 2, x_1);
lean_ctor_set(x_42, 3, x_2);
lean_ctor_set(x_42, 4, x_3);
lean_ctor_set(x_42, 5, x_26);
x_43 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate(x_42, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_36, x_37, x_38);
return x_43;
}
}
}
else
{
lean_object* x_139; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_139 = lean_box(0);
lean_ctor_set(x_18, 0, x_139);
return x_18;
}
}
else
{
lean_object* x_140; uint8_t x_141; 
x_140 = lean_ctor_get(x_18, 0);
lean_inc(x_140);
lean_dec(x_18);
x_141 = lean_unbox(x_140);
lean_dec(x_140);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_165; 
x_142 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__1));
x_143 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(x_142, x_15);
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 x_145 = x_143;
} else {
 lean_dec_ref(x_143);
 x_145 = lean_box(0);
}
x_146 = l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(x_4);
x_147 = l_Lean_Meta_Grind_Order_instDecidableLEWeight(x_3, x_146);
x_165 = lean_unbox(x_144);
lean_dec(x_144);
if (x_165 == 0)
{
x_148 = x_6;
x_149 = x_7;
x_150 = x_8;
x_151 = x_9;
x_152 = x_10;
x_153 = x_11;
x_154 = x_12;
x_155 = x_13;
x_156 = x_14;
x_157 = x_15;
x_158 = x_16;
x_159 = lean_box(0);
goto block_164;
}
else
{
lean_object* x_166; 
x_166 = l_Lean_Meta_Grind_Order_getExpr(x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; 
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
lean_dec_ref(x_166);
x_168 = l_Lean_Meta_Grind_Order_getExpr(x_2, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; lean_object* x_170; 
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
lean_dec_ref(x_168);
x_170 = l_Lean_Meta_Grind_Order_Cnstr_pp(x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; uint8_t x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_185; lean_object* x_186; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_224; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
lean_dec_ref(x_170);
x_172 = lean_ctor_get(x_3, 0);
x_173 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
x_174 = l_Lean_MessageData_ofExpr(x_167);
x_175 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__3;
x_190 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_190, 0, x_174);
lean_ctor_set(x_190, 1, x_175);
x_191 = l_Lean_MessageData_ofExpr(x_169);
x_192 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
x_193 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_175);
if (x_173 == 0)
{
lean_object* x_228; uint8_t x_229; 
x_228 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5;
x_229 = lean_int_dec_lt(x_172, x_228);
if (x_229 == 0)
{
lean_object* x_230; lean_object* x_231; 
x_230 = lean_nat_abs(x_172);
x_231 = l_Nat_reprFast(x_230);
x_194 = x_231;
goto block_223;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_232 = lean_nat_abs(x_172);
x_233 = lean_unsigned_to_nat(1u);
x_234 = lean_nat_sub(x_232, x_233);
lean_dec(x_232);
x_235 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__6));
x_236 = lean_nat_add(x_234, x_233);
lean_dec(x_234);
x_237 = l_Nat_reprFast(x_236);
x_238 = lean_string_append(x_235, x_237);
lean_dec_ref(x_237);
x_194 = x_238;
goto block_223;
}
}
else
{
lean_object* x_239; uint8_t x_240; 
x_239 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5;
x_240 = lean_int_dec_lt(x_172, x_239);
if (x_240 == 0)
{
lean_object* x_241; lean_object* x_242; 
x_241 = lean_nat_abs(x_172);
x_242 = l_Nat_reprFast(x_241);
x_224 = x_242;
goto block_227;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_243 = lean_nat_abs(x_172);
x_244 = lean_unsigned_to_nat(1u);
x_245 = lean_nat_sub(x_243, x_244);
lean_dec(x_243);
x_246 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__6));
x_247 = lean_nat_add(x_245, x_244);
lean_dec(x_245);
x_248 = l_Nat_reprFast(x_247);
x_249 = lean_string_append(x_246, x_248);
lean_dec_ref(x_248);
x_224 = x_249;
goto block_227;
}
}
block_184:
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_178 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_178, 0, x_177);
x_179 = l_Lean_MessageData_ofFormat(x_178);
x_180 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_180, 0, x_176);
lean_ctor_set(x_180, 1, x_179);
x_181 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_175);
x_182 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_171);
x_183 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___redArg(x_142, x_182, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_183) == 0)
{
lean_dec_ref(x_183);
x_148 = x_6;
x_149 = x_7;
x_150 = x_8;
x_151 = x_9;
x_152 = x_10;
x_153 = x_11;
x_154 = x_12;
x_155 = x_13;
x_156 = x_14;
x_157 = x_15;
x_158 = x_16;
x_159 = lean_box(0);
goto block_164;
}
else
{
lean_dec_ref(x_146);
lean_dec(x_145);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_183;
}
}
block_189:
{
lean_object* x_187; lean_object* x_188; 
x_187 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4));
x_188 = lean_string_append(x_186, x_187);
x_176 = x_185;
x_177 = x_188;
goto block_184;
}
block_223:
{
lean_object* x_195; uint8_t x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_195 = lean_ctor_get(x_146, 0);
lean_inc(x_195);
x_196 = lean_ctor_get_uint8(x_146, sizeof(void*)*1);
x_197 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_197, 0, x_194);
x_198 = l_Lean_MessageData_ofFormat(x_197);
x_199 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_199, 0, x_193);
lean_ctor_set(x_199, 1, x_198);
x_200 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_175);
if (x_196 == 0)
{
lean_object* x_201; uint8_t x_202; 
x_201 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5;
x_202 = lean_int_dec_lt(x_195, x_201);
if (x_202 == 0)
{
lean_object* x_203; lean_object* x_204; 
x_203 = lean_nat_abs(x_195);
lean_dec(x_195);
x_204 = l_Nat_reprFast(x_203);
x_176 = x_200;
x_177 = x_204;
goto block_184;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_205 = lean_nat_abs(x_195);
lean_dec(x_195);
x_206 = lean_unsigned_to_nat(1u);
x_207 = lean_nat_sub(x_205, x_206);
lean_dec(x_205);
x_208 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__6));
x_209 = lean_nat_add(x_207, x_206);
lean_dec(x_207);
x_210 = l_Nat_reprFast(x_209);
x_211 = lean_string_append(x_208, x_210);
lean_dec_ref(x_210);
x_176 = x_200;
x_177 = x_211;
goto block_184;
}
}
else
{
lean_object* x_212; uint8_t x_213; 
x_212 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5;
x_213 = lean_int_dec_lt(x_195, x_212);
if (x_213 == 0)
{
lean_object* x_214; lean_object* x_215; 
x_214 = lean_nat_abs(x_195);
lean_dec(x_195);
x_215 = l_Nat_reprFast(x_214);
x_185 = x_200;
x_186 = x_215;
goto block_189;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_216 = lean_nat_abs(x_195);
lean_dec(x_195);
x_217 = lean_unsigned_to_nat(1u);
x_218 = lean_nat_sub(x_216, x_217);
lean_dec(x_216);
x_219 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__6));
x_220 = lean_nat_add(x_218, x_217);
lean_dec(x_218);
x_221 = l_Nat_reprFast(x_220);
x_222 = lean_string_append(x_219, x_221);
lean_dec_ref(x_221);
x_185 = x_200;
x_186 = x_222;
goto block_189;
}
}
}
block_227:
{
lean_object* x_225; lean_object* x_226; 
x_225 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4));
x_226 = lean_string_append(x_224, x_225);
x_194 = x_226;
goto block_223;
}
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; 
lean_dec(x_169);
lean_dec(x_167);
lean_dec_ref(x_146);
lean_dec(x_145);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_250 = lean_ctor_get(x_170, 0);
lean_inc(x_250);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 x_251 = x_170;
} else {
 lean_dec_ref(x_170);
 x_251 = lean_box(0);
}
if (lean_is_scalar(x_251)) {
 x_252 = lean_alloc_ctor(1, 1, 0);
} else {
 x_252 = x_251;
}
lean_ctor_set(x_252, 0, x_250);
return x_252;
}
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; 
lean_dec(x_167);
lean_dec_ref(x_146);
lean_dec(x_145);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_253 = lean_ctor_get(x_168, 0);
lean_inc(x_253);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 x_254 = x_168;
} else {
 lean_dec_ref(x_168);
 x_254 = lean_box(0);
}
if (lean_is_scalar(x_254)) {
 x_255 = lean_alloc_ctor(1, 1, 0);
} else {
 x_255 = x_254;
}
lean_ctor_set(x_255, 0, x_253);
return x_255;
}
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; 
lean_dec_ref(x_146);
lean_dec(x_145);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_256 = lean_ctor_get(x_166, 0);
lean_inc(x_256);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 x_257 = x_166;
} else {
 lean_dec_ref(x_166);
 x_257 = lean_box(0);
}
if (lean_is_scalar(x_257)) {
 x_258 = lean_alloc_ctor(1, 1, 0);
} else {
 x_258 = x_257;
}
lean_ctor_set(x_258, 0, x_256);
return x_258;
}
}
block_164:
{
if (x_147 == 0)
{
lean_object* x_160; lean_object* x_161; 
lean_dec(x_148);
lean_dec_ref(x_146);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_160 = lean_box(0);
if (lean_is_scalar(x_145)) {
 x_161 = lean_alloc_ctor(0, 1, 0);
} else {
 x_161 = x_145;
}
lean_ctor_set(x_161, 0, x_160);
return x_161;
}
else
{
lean_object* x_162; lean_object* x_163; 
lean_dec(x_145);
x_162 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_162, 0, x_4);
lean_ctor_set(x_162, 1, x_5);
lean_ctor_set(x_162, 2, x_1);
lean_ctor_set(x_162, 3, x_2);
lean_ctor_set(x_162, 4, x_3);
lean_ctor_set(x_162, 5, x_146);
x_163 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate(x_162, x_148, x_149, x_150, x_151, x_152, x_153, x_154, x_155, x_156, x_157, x_158);
return x_163;
}
}
}
else
{
lean_object* x_259; lean_object* x_260; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_259 = lean_box(0);
x_260 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_260, 0, x_259);
return x_260;
}
}
}
else
{
uint8_t x_261; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_261 = !lean_is_exclusive(x_18);
if (x_261 == 0)
{
return x_18;
}
else
{
lean_object* x_262; lean_object* x_263; 
x_262 = lean_ctor_get(x_18, 0);
lean_inc(x_262);
lean_dec(x_18);
x_263 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_263, 0, x_262);
return x_263;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___boxed(lean_object** _args) {
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
x_18 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_18;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Grind_Order_get_x27___redArg(x_2, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = lean_ctor_get(x_10, 4);
lean_inc_ref(x_11);
lean_dec(x_10);
x_12 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(x_11, x_1);
if (lean_obj_tag(x_12) == 1)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec_ref(x_1);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_Meta_Grind_alreadyInternalized___redArg(x_14, x_2);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_dec(x_14);
return x_15;
}
else
{
lean_object* x_18; 
lean_dec_ref(x_15);
x_18 = l_Lean_Meta_Grind_isEqFalse___redArg(x_14, x_2, x_3, x_4, x_5, x_6, x_7);
return x_18;
}
}
else
{
lean_dec(x_14);
return x_15;
}
}
else
{
lean_object* x_19; 
lean_dec(x_12);
x_19 = l_Lean_Meta_Grind_alreadyInternalized___redArg(x_1, x_2);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_dec_ref(x_1);
return x_19;
}
else
{
lean_object* x_22; 
lean_dec_ref(x_19);
x_22 = l_Lean_Meta_Grind_isEqFalse___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_22;
}
}
else
{
lean_dec_ref(x_1);
return x_19;
}
}
}
else
{
uint8_t x_23; 
lean_dec_ref(x_1);
x_23 = !lean_is_exclusive(x_9);
if (x_23 == 0)
{
return x_9;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_9, 0);
lean_inc(x_24);
lean_dec(x_9);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse___redArg(x_1, x_3, x_7, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_18; 
lean_inc_ref(x_5);
x_18 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isAlreadyFalse___redArg(x_5, x_7, x_11, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_46; 
lean_free_object(x_18);
x_22 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__1));
x_23 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(x_22, x_15);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 x_25 = x_23;
} else {
 lean_dec_ref(x_23);
 x_25 = lean_box(0);
}
x_26 = l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(x_4);
x_46 = lean_unbox(x_24);
lean_dec(x_24);
if (x_46 == 0)
{
x_27 = x_6;
x_28 = x_7;
x_29 = x_8;
x_30 = x_9;
x_31 = x_10;
x_32 = x_11;
x_33 = x_12;
x_34 = x_13;
x_35 = x_14;
x_36 = x_15;
x_37 = x_16;
x_38 = lean_box(0);
goto block_45;
}
else
{
lean_object* x_47; 
x_47 = l_Lean_Meta_Grind_Order_getExpr(x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec_ref(x_47);
x_49 = l_Lean_Meta_Grind_Order_getExpr(x_2, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec_ref(x_49);
x_51 = l_Lean_Meta_Grind_Order_Cnstr_pp(x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_63; lean_object* x_64; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_106; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec_ref(x_51);
x_68 = lean_ctor_get(x_3, 0);
x_69 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
x_70 = l_Lean_MessageData_ofExpr(x_48);
x_71 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__3;
x_72 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
x_73 = l_Lean_MessageData_ofExpr(x_50);
x_74 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_71);
if (x_69 == 0)
{
lean_object* x_110; uint8_t x_111; 
x_110 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5;
x_111 = lean_int_dec_lt(x_68, x_110);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_nat_abs(x_68);
x_113 = l_Nat_reprFast(x_112);
x_76 = x_113;
goto block_105;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_114 = lean_nat_abs(x_68);
x_115 = lean_unsigned_to_nat(1u);
x_116 = lean_nat_sub(x_114, x_115);
lean_dec(x_114);
x_117 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__6));
x_118 = lean_nat_add(x_116, x_115);
lean_dec(x_116);
x_119 = l_Nat_reprFast(x_118);
x_120 = lean_string_append(x_117, x_119);
lean_dec_ref(x_119);
x_76 = x_120;
goto block_105;
}
}
else
{
lean_object* x_121; uint8_t x_122; 
x_121 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5;
x_122 = lean_int_dec_lt(x_68, x_121);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_nat_abs(x_68);
x_124 = l_Nat_reprFast(x_123);
x_106 = x_124;
goto block_109;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_125 = lean_nat_abs(x_68);
x_126 = lean_unsigned_to_nat(1u);
x_127 = lean_nat_sub(x_125, x_126);
lean_dec(x_125);
x_128 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__6));
x_129 = lean_nat_add(x_127, x_126);
lean_dec(x_127);
x_130 = l_Nat_reprFast(x_129);
x_131 = lean_string_append(x_128, x_130);
lean_dec_ref(x_130);
x_106 = x_131;
goto block_109;
}
}
block_62:
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_55 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_56 = l_Lean_MessageData_ofFormat(x_55);
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_53);
lean_ctor_set(x_57, 1, x_56);
x_58 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__3;
x_59 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_52);
x_61 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___redArg(x_22, x_60, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_61) == 0)
{
lean_dec_ref(x_61);
x_27 = x_6;
x_28 = x_7;
x_29 = x_8;
x_30 = x_9;
x_31 = x_10;
x_32 = x_11;
x_33 = x_12;
x_34 = x_13;
x_35 = x_14;
x_36 = x_15;
x_37 = x_16;
x_38 = lean_box(0);
goto block_45;
}
else
{
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_61;
}
}
block_67:
{
lean_object* x_65; lean_object* x_66; 
x_65 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4));
x_66 = lean_string_append(x_64, x_65);
x_53 = x_63;
x_54 = x_66;
goto block_62;
}
block_105:
{
lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_77 = lean_ctor_get(x_26, 0);
lean_inc(x_77);
x_78 = lean_ctor_get_uint8(x_26, sizeof(void*)*1);
x_79 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_79, 0, x_76);
x_80 = l_Lean_MessageData_ofFormat(x_79);
x_81 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_81, 0, x_75);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_71);
if (x_78 == 0)
{
lean_object* x_83; uint8_t x_84; 
x_83 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5;
x_84 = lean_int_dec_lt(x_77, x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_nat_abs(x_77);
lean_dec(x_77);
x_86 = l_Nat_reprFast(x_85);
x_53 = x_82;
x_54 = x_86;
goto block_62;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_87 = lean_nat_abs(x_77);
lean_dec(x_77);
x_88 = lean_unsigned_to_nat(1u);
x_89 = lean_nat_sub(x_87, x_88);
lean_dec(x_87);
x_90 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__6));
x_91 = lean_nat_add(x_89, x_88);
lean_dec(x_89);
x_92 = l_Nat_reprFast(x_91);
x_93 = lean_string_append(x_90, x_92);
lean_dec_ref(x_92);
x_53 = x_82;
x_54 = x_93;
goto block_62;
}
}
else
{
lean_object* x_94; uint8_t x_95; 
x_94 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5;
x_95 = lean_int_dec_lt(x_77, x_94);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_nat_abs(x_77);
lean_dec(x_77);
x_97 = l_Nat_reprFast(x_96);
x_63 = x_82;
x_64 = x_97;
goto block_67;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_98 = lean_nat_abs(x_77);
lean_dec(x_77);
x_99 = lean_unsigned_to_nat(1u);
x_100 = lean_nat_sub(x_98, x_99);
lean_dec(x_98);
x_101 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__6));
x_102 = lean_nat_add(x_100, x_99);
lean_dec(x_100);
x_103 = l_Nat_reprFast(x_102);
x_104 = lean_string_append(x_101, x_103);
lean_dec_ref(x_103);
x_63 = x_82;
x_64 = x_104;
goto block_67;
}
}
}
block_109:
{
lean_object* x_107; lean_object* x_108; 
x_107 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4));
x_108 = lean_string_append(x_106, x_107);
x_76 = x_108;
goto block_105;
}
}
else
{
uint8_t x_132; 
lean_dec(x_50);
lean_dec(x_48);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_132 = !lean_is_exclusive(x_51);
if (x_132 == 0)
{
return x_51;
}
else
{
lean_object* x_133; lean_object* x_134; 
x_133 = lean_ctor_get(x_51, 0);
lean_inc(x_133);
lean_dec(x_51);
x_134 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_134, 0, x_133);
return x_134;
}
}
}
else
{
uint8_t x_135; 
lean_dec(x_48);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_135 = !lean_is_exclusive(x_49);
if (x_135 == 0)
{
return x_49;
}
else
{
lean_object* x_136; lean_object* x_137; 
x_136 = lean_ctor_get(x_49, 0);
lean_inc(x_136);
lean_dec(x_49);
x_137 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_137, 0, x_136);
return x_137;
}
}
}
else
{
uint8_t x_138; 
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_138 = !lean_is_exclusive(x_47);
if (x_138 == 0)
{
return x_47;
}
else
{
lean_object* x_139; lean_object* x_140; 
x_139 = lean_ctor_get(x_47, 0);
lean_inc(x_139);
lean_dec(x_47);
x_140 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_140, 0, x_139);
return x_140;
}
}
}
block_45:
{
lean_object* x_39; uint8_t x_40; 
lean_inc_ref(x_26);
x_39 = l_Lean_Meta_Grind_Order_Weight_add(x_3, x_26);
x_40 = l_Lean_Meta_Grind_Order_Weight_isNeg(x_39);
lean_dec_ref(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_41 = lean_box(0);
if (lean_is_scalar(x_25)) {
 x_42 = lean_alloc_ctor(0, 1, 0);
} else {
 x_42 = x_25;
}
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_25);
x_43 = lean_alloc_ctor(1, 6, 0);
lean_ctor_set(x_43, 0, x_4);
lean_ctor_set(x_43, 1, x_5);
lean_ctor_set(x_43, 2, x_1);
lean_ctor_set(x_43, 3, x_2);
lean_ctor_set(x_43, 4, x_3);
lean_ctor_set(x_43, 5, x_26);
x_44 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate(x_43, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_36, x_37);
return x_44;
}
}
}
else
{
lean_object* x_141; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_141 = lean_box(0);
lean_ctor_set(x_18, 0, x_141);
return x_18;
}
}
else
{
lean_object* x_142; uint8_t x_143; 
x_142 = lean_ctor_get(x_18, 0);
lean_inc(x_142);
lean_dec(x_18);
x_143 = lean_unbox(x_142);
lean_dec(x_142);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_168; 
x_144 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__1));
x_145 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(x_144, x_15);
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 x_147 = x_145;
} else {
 lean_dec_ref(x_145);
 x_147 = lean_box(0);
}
x_148 = l_Lean_Meta_Grind_Order_Cnstr_getWeight___redArg(x_4);
x_168 = lean_unbox(x_146);
lean_dec(x_146);
if (x_168 == 0)
{
x_149 = x_6;
x_150 = x_7;
x_151 = x_8;
x_152 = x_9;
x_153 = x_10;
x_154 = x_11;
x_155 = x_12;
x_156 = x_13;
x_157 = x_14;
x_158 = x_15;
x_159 = x_16;
x_160 = lean_box(0);
goto block_167;
}
else
{
lean_object* x_169; 
x_169 = l_Lean_Meta_Grind_Order_getExpr(x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; lean_object* x_171; 
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
lean_dec_ref(x_169);
x_171 = l_Lean_Meta_Grind_Order_getExpr(x_2, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
lean_dec_ref(x_171);
x_173 = l_Lean_Meta_Grind_Order_Cnstr_pp(x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_185; lean_object* x_186; lean_object* x_190; uint8_t x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_228; 
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
lean_dec_ref(x_173);
x_190 = lean_ctor_get(x_3, 0);
x_191 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
x_192 = l_Lean_MessageData_ofExpr(x_170);
x_193 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__3;
x_194 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_194, 1, x_193);
x_195 = l_Lean_MessageData_ofExpr(x_172);
x_196 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_196, 0, x_194);
lean_ctor_set(x_196, 1, x_195);
x_197 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_193);
if (x_191 == 0)
{
lean_object* x_232; uint8_t x_233; 
x_232 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5;
x_233 = lean_int_dec_lt(x_190, x_232);
if (x_233 == 0)
{
lean_object* x_234; lean_object* x_235; 
x_234 = lean_nat_abs(x_190);
x_235 = l_Nat_reprFast(x_234);
x_198 = x_235;
goto block_227;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_236 = lean_nat_abs(x_190);
x_237 = lean_unsigned_to_nat(1u);
x_238 = lean_nat_sub(x_236, x_237);
lean_dec(x_236);
x_239 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__6));
x_240 = lean_nat_add(x_238, x_237);
lean_dec(x_238);
x_241 = l_Nat_reprFast(x_240);
x_242 = lean_string_append(x_239, x_241);
lean_dec_ref(x_241);
x_198 = x_242;
goto block_227;
}
}
else
{
lean_object* x_243; uint8_t x_244; 
x_243 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5;
x_244 = lean_int_dec_lt(x_190, x_243);
if (x_244 == 0)
{
lean_object* x_245; lean_object* x_246; 
x_245 = lean_nat_abs(x_190);
x_246 = l_Nat_reprFast(x_245);
x_228 = x_246;
goto block_231;
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_247 = lean_nat_abs(x_190);
x_248 = lean_unsigned_to_nat(1u);
x_249 = lean_nat_sub(x_247, x_248);
lean_dec(x_247);
x_250 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__6));
x_251 = lean_nat_add(x_249, x_248);
lean_dec(x_249);
x_252 = l_Nat_reprFast(x_251);
x_253 = lean_string_append(x_250, x_252);
lean_dec_ref(x_252);
x_228 = x_253;
goto block_231;
}
}
block_184:
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_177 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_177, 0, x_176);
x_178 = l_Lean_MessageData_ofFormat(x_177);
x_179 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_179, 0, x_175);
lean_ctor_set(x_179, 1, x_178);
x_180 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__3;
x_181 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_180);
x_182 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_174);
x_183 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___redArg(x_144, x_182, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_183) == 0)
{
lean_dec_ref(x_183);
x_149 = x_6;
x_150 = x_7;
x_151 = x_8;
x_152 = x_9;
x_153 = x_10;
x_154 = x_11;
x_155 = x_12;
x_156 = x_13;
x_157 = x_14;
x_158 = x_15;
x_159 = x_16;
x_160 = lean_box(0);
goto block_167;
}
else
{
lean_dec_ref(x_148);
lean_dec(x_147);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_183;
}
}
block_189:
{
lean_object* x_187; lean_object* x_188; 
x_187 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4));
x_188 = lean_string_append(x_186, x_187);
x_175 = x_185;
x_176 = x_188;
goto block_184;
}
block_227:
{
lean_object* x_199; uint8_t x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_199 = lean_ctor_get(x_148, 0);
lean_inc(x_199);
x_200 = lean_ctor_get_uint8(x_148, sizeof(void*)*1);
x_201 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_201, 0, x_198);
x_202 = l_Lean_MessageData_ofFormat(x_201);
x_203 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_203, 0, x_197);
lean_ctor_set(x_203, 1, x_202);
x_204 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_193);
if (x_200 == 0)
{
lean_object* x_205; uint8_t x_206; 
x_205 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5;
x_206 = lean_int_dec_lt(x_199, x_205);
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; 
x_207 = lean_nat_abs(x_199);
lean_dec(x_199);
x_208 = l_Nat_reprFast(x_207);
x_175 = x_204;
x_176 = x_208;
goto block_184;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_209 = lean_nat_abs(x_199);
lean_dec(x_199);
x_210 = lean_unsigned_to_nat(1u);
x_211 = lean_nat_sub(x_209, x_210);
lean_dec(x_209);
x_212 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__6));
x_213 = lean_nat_add(x_211, x_210);
lean_dec(x_211);
x_214 = l_Nat_reprFast(x_213);
x_215 = lean_string_append(x_212, x_214);
lean_dec_ref(x_214);
x_175 = x_204;
x_176 = x_215;
goto block_184;
}
}
else
{
lean_object* x_216; uint8_t x_217; 
x_216 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5;
x_217 = lean_int_dec_lt(x_199, x_216);
if (x_217 == 0)
{
lean_object* x_218; lean_object* x_219; 
x_218 = lean_nat_abs(x_199);
lean_dec(x_199);
x_219 = l_Nat_reprFast(x_218);
x_185 = x_204;
x_186 = x_219;
goto block_189;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_220 = lean_nat_abs(x_199);
lean_dec(x_199);
x_221 = lean_unsigned_to_nat(1u);
x_222 = lean_nat_sub(x_220, x_221);
lean_dec(x_220);
x_223 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__6));
x_224 = lean_nat_add(x_222, x_221);
lean_dec(x_222);
x_225 = l_Nat_reprFast(x_224);
x_226 = lean_string_append(x_223, x_225);
lean_dec_ref(x_225);
x_185 = x_204;
x_186 = x_226;
goto block_189;
}
}
}
block_231:
{
lean_object* x_229; lean_object* x_230; 
x_229 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4));
x_230 = lean_string_append(x_228, x_229);
x_198 = x_230;
goto block_227;
}
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; 
lean_dec(x_172);
lean_dec(x_170);
lean_dec_ref(x_148);
lean_dec(x_147);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_254 = lean_ctor_get(x_173, 0);
lean_inc(x_254);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 x_255 = x_173;
} else {
 lean_dec_ref(x_173);
 x_255 = lean_box(0);
}
if (lean_is_scalar(x_255)) {
 x_256 = lean_alloc_ctor(1, 1, 0);
} else {
 x_256 = x_255;
}
lean_ctor_set(x_256, 0, x_254);
return x_256;
}
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; 
lean_dec(x_170);
lean_dec_ref(x_148);
lean_dec(x_147);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_257 = lean_ctor_get(x_171, 0);
lean_inc(x_257);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 x_258 = x_171;
} else {
 lean_dec_ref(x_171);
 x_258 = lean_box(0);
}
if (lean_is_scalar(x_258)) {
 x_259 = lean_alloc_ctor(1, 1, 0);
} else {
 x_259 = x_258;
}
lean_ctor_set(x_259, 0, x_257);
return x_259;
}
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; 
lean_dec_ref(x_148);
lean_dec(x_147);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_260 = lean_ctor_get(x_169, 0);
lean_inc(x_260);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 x_261 = x_169;
} else {
 lean_dec_ref(x_169);
 x_261 = lean_box(0);
}
if (lean_is_scalar(x_261)) {
 x_262 = lean_alloc_ctor(1, 1, 0);
} else {
 x_262 = x_261;
}
lean_ctor_set(x_262, 0, x_260);
return x_262;
}
}
block_167:
{
lean_object* x_161; uint8_t x_162; 
lean_inc_ref(x_148);
x_161 = l_Lean_Meta_Grind_Order_Weight_add(x_3, x_148);
x_162 = l_Lean_Meta_Grind_Order_Weight_isNeg(x_161);
lean_dec_ref(x_161);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; 
lean_dec(x_149);
lean_dec_ref(x_148);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_163 = lean_box(0);
if (lean_is_scalar(x_147)) {
 x_164 = lean_alloc_ctor(0, 1, 0);
} else {
 x_164 = x_147;
}
lean_ctor_set(x_164, 0, x_163);
return x_164;
}
else
{
lean_object* x_165; lean_object* x_166; 
lean_dec(x_147);
x_165 = lean_alloc_ctor(1, 6, 0);
lean_ctor_set(x_165, 0, x_4);
lean_ctor_set(x_165, 1, x_5);
lean_ctor_set(x_165, 2, x_1);
lean_ctor_set(x_165, 3, x_2);
lean_ctor_set(x_165, 4, x_3);
lean_ctor_set(x_165, 5, x_148);
x_166 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate(x_165, x_149, x_150, x_151, x_152, x_153, x_154, x_155, x_156, x_157, x_158, x_159);
return x_166;
}
}
}
else
{
lean_object* x_263; lean_object* x_264; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_263 = lean_box(0);
x_264 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_264, 0, x_263);
return x_264;
}
}
}
else
{
uint8_t x_265; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_265 = !lean_is_exclusive(x_18);
if (x_265 == 0)
{
return x_18;
}
else
{
lean_object* x_266; lean_object* x_267; 
x_266 = lean_ctor_get(x_18, 0);
lean_inc(x_266);
lean_dec(x_18);
x_267 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_267, 0, x_266);
return x_267;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___boxed(lean_object** _args) {
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
x_18 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_18;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 1);
lean_inc(x_16);
lean_dec_ref(x_2);
x_17 = lean_apply_14(x_1, x_15, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, lean_box(0));
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__0));
x_2 = lean_alloc_closure((void*)(l_instHashableProd___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_2, 0, x_1);
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
x_2 = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__2;
x_2 = lean_alloc_closure((void*)(l_instBEqProd___redArg___lam__0___boxed), 4, 2);
lean_closure_set(x_2, 0, x_1);
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; uint8_t x_17; 
x_16 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__1;
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_21 = lean_ctor_get(x_18, 0);
x_22 = lean_ctor_get(x_18, 2);
x_23 = lean_ctor_get(x_18, 3);
x_24 = lean_ctor_get(x_18, 4);
x_25 = lean_ctor_get(x_18, 1);
lean_dec(x_25);
x_26 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__2));
x_27 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__3));
lean_inc_ref(x_21);
x_28 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_28, 0, x_21);
x_29 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_29, 0, x_21);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_31, 0, x_24);
x_32 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_32, 0, x_23);
x_33 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_33, 0, x_22);
lean_ctor_set(x_18, 4, x_31);
lean_ctor_set(x_18, 3, x_32);
lean_ctor_set(x_18, 2, x_33);
lean_ctor_set(x_18, 1, x_26);
lean_ctor_set(x_18, 0, x_30);
lean_ctor_set(x_16, 1, x_27);
x_34 = l_ReaderT_instMonad___redArg(x_16);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_ctor_get(x_34, 1);
lean_dec(x_37);
x_38 = !lean_is_exclusive(x_36);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_39 = lean_ctor_get(x_36, 0);
x_40 = lean_ctor_get(x_36, 2);
x_41 = lean_ctor_get(x_36, 3);
x_42 = lean_ctor_get(x_36, 4);
x_43 = lean_ctor_get(x_36, 1);
lean_dec(x_43);
x_44 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__4));
x_45 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__5));
lean_inc_ref(x_39);
x_46 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_46, 0, x_39);
x_47 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_47, 0, x_39);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_49, 0, x_42);
x_50 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_50, 0, x_41);
x_51 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_51, 0, x_40);
lean_ctor_set(x_36, 4, x_49);
lean_ctor_set(x_36, 3, x_50);
lean_ctor_set(x_36, 2, x_51);
lean_ctor_set(x_36, 1, x_44);
lean_ctor_set(x_36, 0, x_48);
lean_ctor_set(x_34, 1, x_45);
x_52 = l_ReaderT_instMonad___redArg(x_34);
x_53 = l_ReaderT_instMonad___redArg(x_52);
x_54 = l_ReaderT_instMonad___redArg(x_53);
x_55 = l_ReaderT_instMonad___redArg(x_54);
x_56 = l_ReaderT_instMonad___redArg(x_55);
x_57 = l_ReaderT_instMonad___redArg(x_56);
x_58 = l_ReaderT_instMonad___redArg(x_57);
x_59 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__1;
x_60 = l_Lean_Meta_Grind_Order_getStruct(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_60) == 0)
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_62 = lean_ctor_get(x_60, 0);
x_63 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__3;
x_64 = lean_ctor_get(x_62, 17);
lean_inc_ref(x_64);
lean_dec(x_62);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_1);
lean_ctor_set(x_65, 1, x_2);
x_66 = l_Lean_PersistentHashMap_find_x3f___redArg(x_63, x_59, x_64, x_65);
if (lean_obj_tag(x_66) == 1)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_free_object(x_60);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
lean_dec_ref(x_66);
x_68 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___lam__0___boxed), 14, 1);
lean_closure_set(x_68, 0, x_3);
x_69 = l_List_forM___redArg(x_58, x_67, x_68);
x_70 = lean_apply_12(x_69, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, lean_box(0));
return x_70;
}
else
{
lean_object* x_71; 
lean_dec(x_66);
lean_dec_ref(x_58);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_71 = lean_box(0);
lean_ctor_set(x_60, 0, x_71);
return x_60;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_72 = lean_ctor_get(x_60, 0);
lean_inc(x_72);
lean_dec(x_60);
x_73 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__3;
x_74 = lean_ctor_get(x_72, 17);
lean_inc_ref(x_74);
lean_dec(x_72);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_1);
lean_ctor_set(x_75, 1, x_2);
x_76 = l_Lean_PersistentHashMap_find_x3f___redArg(x_73, x_59, x_74, x_75);
if (lean_obj_tag(x_76) == 1)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
lean_dec_ref(x_76);
x_78 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___lam__0___boxed), 14, 1);
lean_closure_set(x_78, 0, x_3);
x_79 = l_List_forM___redArg(x_58, x_77, x_78);
x_80 = lean_apply_12(x_79, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, lean_box(0));
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_76);
lean_dec_ref(x_58);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_81 = lean_box(0);
x_82 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_82, 0, x_81);
return x_82;
}
}
}
else
{
uint8_t x_83; 
lean_dec_ref(x_58);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_83 = !lean_is_exclusive(x_60);
if (x_83 == 0)
{
return x_60;
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_60, 0);
lean_inc(x_84);
lean_dec(x_60);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_84);
return x_85;
}
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_86 = lean_ctor_get(x_36, 0);
x_87 = lean_ctor_get(x_36, 2);
x_88 = lean_ctor_get(x_36, 3);
x_89 = lean_ctor_get(x_36, 4);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_36);
x_90 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__4));
x_91 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__5));
lean_inc_ref(x_86);
x_92 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_92, 0, x_86);
x_93 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_93, 0, x_86);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
x_95 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_95, 0, x_89);
x_96 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_96, 0, x_88);
x_97 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_97, 0, x_87);
x_98 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_98, 0, x_94);
lean_ctor_set(x_98, 1, x_90);
lean_ctor_set(x_98, 2, x_97);
lean_ctor_set(x_98, 3, x_96);
lean_ctor_set(x_98, 4, x_95);
lean_ctor_set(x_34, 1, x_91);
lean_ctor_set(x_34, 0, x_98);
x_99 = l_ReaderT_instMonad___redArg(x_34);
x_100 = l_ReaderT_instMonad___redArg(x_99);
x_101 = l_ReaderT_instMonad___redArg(x_100);
x_102 = l_ReaderT_instMonad___redArg(x_101);
x_103 = l_ReaderT_instMonad___redArg(x_102);
x_104 = l_ReaderT_instMonad___redArg(x_103);
x_105 = l_ReaderT_instMonad___redArg(x_104);
x_106 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__1;
x_107 = l_Lean_Meta_Grind_Order_getStruct(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 x_109 = x_107;
} else {
 lean_dec_ref(x_107);
 x_109 = lean_box(0);
}
x_110 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__3;
x_111 = lean_ctor_get(x_108, 17);
lean_inc_ref(x_111);
lean_dec(x_108);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_1);
lean_ctor_set(x_112, 1, x_2);
x_113 = l_Lean_PersistentHashMap_find_x3f___redArg(x_110, x_106, x_111, x_112);
if (lean_obj_tag(x_113) == 1)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_109);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
lean_dec_ref(x_113);
x_115 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___lam__0___boxed), 14, 1);
lean_closure_set(x_115, 0, x_3);
x_116 = l_List_forM___redArg(x_105, x_114, x_115);
x_117 = lean_apply_12(x_116, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, lean_box(0));
return x_117;
}
else
{
lean_object* x_118; lean_object* x_119; 
lean_dec(x_113);
lean_dec_ref(x_105);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_118 = lean_box(0);
if (lean_is_scalar(x_109)) {
 x_119 = lean_alloc_ctor(0, 1, 0);
} else {
 x_119 = x_109;
}
lean_ctor_set(x_119, 0, x_118);
return x_119;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec_ref(x_105);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_120 = lean_ctor_get(x_107, 0);
lean_inc(x_120);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 x_121 = x_107;
} else {
 lean_dec_ref(x_107);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(1, 1, 0);
} else {
 x_122 = x_121;
}
lean_ctor_set(x_122, 0, x_120);
return x_122;
}
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_123 = lean_ctor_get(x_34, 0);
lean_inc(x_123);
lean_dec(x_34);
x_124 = lean_ctor_get(x_123, 0);
lean_inc_ref(x_124);
x_125 = lean_ctor_get(x_123, 2);
lean_inc(x_125);
x_126 = lean_ctor_get(x_123, 3);
lean_inc(x_126);
x_127 = lean_ctor_get(x_123, 4);
lean_inc(x_127);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 lean_ctor_release(x_123, 2);
 lean_ctor_release(x_123, 3);
 lean_ctor_release(x_123, 4);
 x_128 = x_123;
} else {
 lean_dec_ref(x_123);
 x_128 = lean_box(0);
}
x_129 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__4));
x_130 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__5));
lean_inc_ref(x_124);
x_131 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_131, 0, x_124);
x_132 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_132, 0, x_124);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
x_134 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_134, 0, x_127);
x_135 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_135, 0, x_126);
x_136 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_136, 0, x_125);
if (lean_is_scalar(x_128)) {
 x_137 = lean_alloc_ctor(0, 5, 0);
} else {
 x_137 = x_128;
}
lean_ctor_set(x_137, 0, x_133);
lean_ctor_set(x_137, 1, x_129);
lean_ctor_set(x_137, 2, x_136);
lean_ctor_set(x_137, 3, x_135);
lean_ctor_set(x_137, 4, x_134);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_130);
x_139 = l_ReaderT_instMonad___redArg(x_138);
x_140 = l_ReaderT_instMonad___redArg(x_139);
x_141 = l_ReaderT_instMonad___redArg(x_140);
x_142 = l_ReaderT_instMonad___redArg(x_141);
x_143 = l_ReaderT_instMonad___redArg(x_142);
x_144 = l_ReaderT_instMonad___redArg(x_143);
x_145 = l_ReaderT_instMonad___redArg(x_144);
x_146 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__1;
x_147 = l_Lean_Meta_Grind_Order_getStruct(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 x_149 = x_147;
} else {
 lean_dec_ref(x_147);
 x_149 = lean_box(0);
}
x_150 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__3;
x_151 = lean_ctor_get(x_148, 17);
lean_inc_ref(x_151);
lean_dec(x_148);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_1);
lean_ctor_set(x_152, 1, x_2);
x_153 = l_Lean_PersistentHashMap_find_x3f___redArg(x_150, x_146, x_151, x_152);
if (lean_obj_tag(x_153) == 1)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_149);
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
lean_dec_ref(x_153);
x_155 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___lam__0___boxed), 14, 1);
lean_closure_set(x_155, 0, x_3);
x_156 = l_List_forM___redArg(x_145, x_154, x_155);
x_157 = lean_apply_12(x_156, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, lean_box(0));
return x_157;
}
else
{
lean_object* x_158; lean_object* x_159; 
lean_dec(x_153);
lean_dec_ref(x_145);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_158 = lean_box(0);
if (lean_is_scalar(x_149)) {
 x_159 = lean_alloc_ctor(0, 1, 0);
} else {
 x_159 = x_149;
}
lean_ctor_set(x_159, 0, x_158);
return x_159;
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec_ref(x_145);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_160 = lean_ctor_get(x_147, 0);
lean_inc(x_160);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 x_161 = x_147;
} else {
 lean_dec_ref(x_147);
 x_161 = lean_box(0);
}
if (lean_is_scalar(x_161)) {
 x_162 = lean_alloc_ctor(1, 1, 0);
} else {
 x_162 = x_161;
}
lean_ctor_set(x_162, 0, x_160);
return x_162;
}
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_163 = lean_ctor_get(x_18, 0);
x_164 = lean_ctor_get(x_18, 2);
x_165 = lean_ctor_get(x_18, 3);
x_166 = lean_ctor_get(x_18, 4);
lean_inc(x_166);
lean_inc(x_165);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_18);
x_167 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__2));
x_168 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__3));
lean_inc_ref(x_163);
x_169 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_169, 0, x_163);
x_170 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_170, 0, x_163);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_170);
x_172 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_172, 0, x_166);
x_173 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_173, 0, x_165);
x_174 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_174, 0, x_164);
x_175 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_175, 0, x_171);
lean_ctor_set(x_175, 1, x_167);
lean_ctor_set(x_175, 2, x_174);
lean_ctor_set(x_175, 3, x_173);
lean_ctor_set(x_175, 4, x_172);
lean_ctor_set(x_16, 1, x_168);
lean_ctor_set(x_16, 0, x_175);
x_176 = l_ReaderT_instMonad___redArg(x_16);
x_177 = lean_ctor_get(x_176, 0);
lean_inc_ref(x_177);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 lean_ctor_release(x_176, 1);
 x_178 = x_176;
} else {
 lean_dec_ref(x_176);
 x_178 = lean_box(0);
}
x_179 = lean_ctor_get(x_177, 0);
lean_inc_ref(x_179);
x_180 = lean_ctor_get(x_177, 2);
lean_inc(x_180);
x_181 = lean_ctor_get(x_177, 3);
lean_inc(x_181);
x_182 = lean_ctor_get(x_177, 4);
lean_inc(x_182);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 lean_ctor_release(x_177, 2);
 lean_ctor_release(x_177, 3);
 lean_ctor_release(x_177, 4);
 x_183 = x_177;
} else {
 lean_dec_ref(x_177);
 x_183 = lean_box(0);
}
x_184 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__4));
x_185 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__5));
lean_inc_ref(x_179);
x_186 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_186, 0, x_179);
x_187 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_187, 0, x_179);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set(x_188, 1, x_187);
x_189 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_189, 0, x_182);
x_190 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_190, 0, x_181);
x_191 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_191, 0, x_180);
if (lean_is_scalar(x_183)) {
 x_192 = lean_alloc_ctor(0, 5, 0);
} else {
 x_192 = x_183;
}
lean_ctor_set(x_192, 0, x_188);
lean_ctor_set(x_192, 1, x_184);
lean_ctor_set(x_192, 2, x_191);
lean_ctor_set(x_192, 3, x_190);
lean_ctor_set(x_192, 4, x_189);
if (lean_is_scalar(x_178)) {
 x_193 = lean_alloc_ctor(0, 2, 0);
} else {
 x_193 = x_178;
}
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_185);
x_194 = l_ReaderT_instMonad___redArg(x_193);
x_195 = l_ReaderT_instMonad___redArg(x_194);
x_196 = l_ReaderT_instMonad___redArg(x_195);
x_197 = l_ReaderT_instMonad___redArg(x_196);
x_198 = l_ReaderT_instMonad___redArg(x_197);
x_199 = l_ReaderT_instMonad___redArg(x_198);
x_200 = l_ReaderT_instMonad___redArg(x_199);
x_201 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__1;
x_202 = l_Lean_Meta_Grind_Order_getStruct(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_202) == 0)
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 x_204 = x_202;
} else {
 lean_dec_ref(x_202);
 x_204 = lean_box(0);
}
x_205 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__3;
x_206 = lean_ctor_get(x_203, 17);
lean_inc_ref(x_206);
lean_dec(x_203);
x_207 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_207, 0, x_1);
lean_ctor_set(x_207, 1, x_2);
x_208 = l_Lean_PersistentHashMap_find_x3f___redArg(x_205, x_201, x_206, x_207);
if (lean_obj_tag(x_208) == 1)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
lean_dec(x_204);
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
lean_dec_ref(x_208);
x_210 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___lam__0___boxed), 14, 1);
lean_closure_set(x_210, 0, x_3);
x_211 = l_List_forM___redArg(x_200, x_209, x_210);
x_212 = lean_apply_12(x_211, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, lean_box(0));
return x_212;
}
else
{
lean_object* x_213; lean_object* x_214; 
lean_dec(x_208);
lean_dec_ref(x_200);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_213 = lean_box(0);
if (lean_is_scalar(x_204)) {
 x_214 = lean_alloc_ctor(0, 1, 0);
} else {
 x_214 = x_204;
}
lean_ctor_set(x_214, 0, x_213);
return x_214;
}
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
lean_dec_ref(x_200);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_215 = lean_ctor_get(x_202, 0);
lean_inc(x_215);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 x_216 = x_202;
} else {
 lean_dec_ref(x_202);
 x_216 = lean_box(0);
}
if (lean_is_scalar(x_216)) {
 x_217 = lean_alloc_ctor(1, 1, 0);
} else {
 x_217 = x_216;
}
lean_ctor_set(x_217, 0, x_215);
return x_217;
}
}
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_218 = lean_ctor_get(x_16, 0);
lean_inc(x_218);
lean_dec(x_16);
x_219 = lean_ctor_get(x_218, 0);
lean_inc_ref(x_219);
x_220 = lean_ctor_get(x_218, 2);
lean_inc(x_220);
x_221 = lean_ctor_get(x_218, 3);
lean_inc(x_221);
x_222 = lean_ctor_get(x_218, 4);
lean_inc(x_222);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 lean_ctor_release(x_218, 1);
 lean_ctor_release(x_218, 2);
 lean_ctor_release(x_218, 3);
 lean_ctor_release(x_218, 4);
 x_223 = x_218;
} else {
 lean_dec_ref(x_218);
 x_223 = lean_box(0);
}
x_224 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__2));
x_225 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__3));
lean_inc_ref(x_219);
x_226 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_226, 0, x_219);
x_227 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_227, 0, x_219);
x_228 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_228, 0, x_226);
lean_ctor_set(x_228, 1, x_227);
x_229 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_229, 0, x_222);
x_230 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_230, 0, x_221);
x_231 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_231, 0, x_220);
if (lean_is_scalar(x_223)) {
 x_232 = lean_alloc_ctor(0, 5, 0);
} else {
 x_232 = x_223;
}
lean_ctor_set(x_232, 0, x_228);
lean_ctor_set(x_232, 1, x_224);
lean_ctor_set(x_232, 2, x_231);
lean_ctor_set(x_232, 3, x_230);
lean_ctor_set(x_232, 4, x_229);
x_233 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_225);
x_234 = l_ReaderT_instMonad___redArg(x_233);
x_235 = lean_ctor_get(x_234, 0);
lean_inc_ref(x_235);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 x_236 = x_234;
} else {
 lean_dec_ref(x_234);
 x_236 = lean_box(0);
}
x_237 = lean_ctor_get(x_235, 0);
lean_inc_ref(x_237);
x_238 = lean_ctor_get(x_235, 2);
lean_inc(x_238);
x_239 = lean_ctor_get(x_235, 3);
lean_inc(x_239);
x_240 = lean_ctor_get(x_235, 4);
lean_inc(x_240);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 lean_ctor_release(x_235, 2);
 lean_ctor_release(x_235, 3);
 lean_ctor_release(x_235, 4);
 x_241 = x_235;
} else {
 lean_dec_ref(x_235);
 x_241 = lean_box(0);
}
x_242 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__4));
x_243 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__5));
lean_inc_ref(x_237);
x_244 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_244, 0, x_237);
x_245 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_245, 0, x_237);
x_246 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_246, 0, x_244);
lean_ctor_set(x_246, 1, x_245);
x_247 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_247, 0, x_240);
x_248 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_248, 0, x_239);
x_249 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_249, 0, x_238);
if (lean_is_scalar(x_241)) {
 x_250 = lean_alloc_ctor(0, 5, 0);
} else {
 x_250 = x_241;
}
lean_ctor_set(x_250, 0, x_246);
lean_ctor_set(x_250, 1, x_242);
lean_ctor_set(x_250, 2, x_249);
lean_ctor_set(x_250, 3, x_248);
lean_ctor_set(x_250, 4, x_247);
if (lean_is_scalar(x_236)) {
 x_251 = lean_alloc_ctor(0, 2, 0);
} else {
 x_251 = x_236;
}
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set(x_251, 1, x_243);
x_252 = l_ReaderT_instMonad___redArg(x_251);
x_253 = l_ReaderT_instMonad___redArg(x_252);
x_254 = l_ReaderT_instMonad___redArg(x_253);
x_255 = l_ReaderT_instMonad___redArg(x_254);
x_256 = l_ReaderT_instMonad___redArg(x_255);
x_257 = l_ReaderT_instMonad___redArg(x_256);
x_258 = l_ReaderT_instMonad___redArg(x_257);
x_259 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__1;
x_260 = l_Lean_Meta_Grind_Order_getStruct(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_260) == 0)
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_261 = lean_ctor_get(x_260, 0);
lean_inc(x_261);
if (lean_is_exclusive(x_260)) {
 lean_ctor_release(x_260, 0);
 x_262 = x_260;
} else {
 lean_dec_ref(x_260);
 x_262 = lean_box(0);
}
x_263 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__3;
x_264 = lean_ctor_get(x_261, 17);
lean_inc_ref(x_264);
lean_dec(x_261);
x_265 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_265, 0, x_1);
lean_ctor_set(x_265, 1, x_2);
x_266 = l_Lean_PersistentHashMap_find_x3f___redArg(x_263, x_259, x_264, x_265);
if (lean_obj_tag(x_266) == 1)
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
lean_dec(x_262);
x_267 = lean_ctor_get(x_266, 0);
lean_inc(x_267);
lean_dec_ref(x_266);
x_268 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___lam__0___boxed), 14, 1);
lean_closure_set(x_268, 0, x_3);
x_269 = l_List_forM___redArg(x_258, x_267, x_268);
x_270 = lean_apply_12(x_269, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, lean_box(0));
return x_270;
}
else
{
lean_object* x_271; lean_object* x_272; 
lean_dec(x_266);
lean_dec_ref(x_258);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_271 = lean_box(0);
if (lean_is_scalar(x_262)) {
 x_272 = lean_alloc_ctor(0, 1, 0);
} else {
 x_272 = x_262;
}
lean_ctor_set(x_272, 0, x_271);
return x_272;
}
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; 
lean_dec_ref(x_258);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_273 = lean_ctor_get(x_260, 0);
lean_inc(x_273);
if (lean_is_exclusive(x_260)) {
 lean_ctor_release(x_260, 0);
 x_274 = x_260;
} else {
 lean_dec_ref(x_260);
 x_274 = lean_box(0);
}
if (lean_is_scalar(x_274)) {
 x_275 = lean_alloc_ctor(1, 1, 0);
} else {
 x_275 = x_274;
}
lean_ctor_set(x_275, 0, x_273);
return x_275;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_Order_get_x27___redArg(x_2, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 4);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(x_8, x_1);
if (lean_obj_tag(x_9) == 1)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
lean_ctor_set(x_9, 0, x_12);
lean_ctor_set(x_5, 0, x_9);
return x_5;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_5, 0, x_15);
return x_5;
}
}
else
{
lean_object* x_16; 
lean_dec(x_9);
x_16 = lean_box(0);
lean_ctor_set(x_5, 0, x_16);
return x_5;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_5, 0);
lean_inc(x_17);
lean_dec(x_5);
x_18 = lean_ctor_get(x_17, 4);
lean_inc_ref(x_18);
lean_dec(x_17);
x_19 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(x_18, x_1);
if (lean_obj_tag(x_19) == 1)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_21 = x_19;
} else {
 lean_dec_ref(x_19);
 x_21 = lean_box(0);
}
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
if (lean_is_scalar(x_21)) {
 x_23 = lean_alloc_ctor(1, 1, 0);
} else {
 x_23 = x_21;
}
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_19);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_5);
if (x_27 == 0)
{
return x_5;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_5, 0);
lean_inc(x_28);
lean_dec(x_5);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___redArg(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___redArg(x_1, x_2, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_58; 
x_58 = lean_nat_dec_eq(x_1, x_2);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = l_Lean_Meta_Grind_Order_isPartialOrder(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; uint8_t x_65; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 x_61 = x_59;
} else {
 lean_dec_ref(x_59);
 x_61 = lean_box(0);
}
x_65 = lean_unbox(x_60);
lean_dec(x_60);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_61);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_66 = lean_box(0);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
else
{
uint8_t x_68; 
x_68 = l_Lean_Meta_Grind_Order_Weight_isZero(x_3);
if (x_68 == 0)
{
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
goto block_64;
}
else
{
if (x_58 == 0)
{
lean_object* x_69; 
lean_dec(x_61);
x_69 = l_Lean_Meta_Grind_Order_getDist_x3f(x_2, x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_69) == 0)
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_69, 0);
if (lean_obj_tag(x_71) == 1)
{
lean_object* x_72; uint8_t x_73; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
lean_dec_ref(x_71);
x_73 = l_Lean_Meta_Grind_Order_Weight_isZero(x_72);
lean_dec(x_72);
if (x_73 == 0)
{
lean_object* x_74; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_74 = lean_box(0);
lean_ctor_set(x_69, 0, x_74);
return x_69;
}
else
{
lean_object* x_75; 
lean_free_object(x_69);
x_75 = l_Lean_Meta_Grind_Order_getExpr(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
lean_dec_ref(x_75);
x_77 = l_Lean_Meta_Grind_Order_getExpr(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_147; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
lean_dec_ref(x_77);
x_147 = l_Lean_Meta_Grind_alreadyInternalized___redArg(x_76, x_5);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; uint8_t x_149; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_unbox(x_148);
lean_dec(x_148);
if (x_149 == 0)
{
x_79 = x_147;
goto block_146;
}
else
{
lean_object* x_150; 
lean_dec_ref(x_147);
x_150 = l_Lean_Meta_Grind_alreadyInternalized___redArg(x_78, x_5);
x_79 = x_150;
goto block_146;
}
}
else
{
x_79 = x_147;
goto block_146;
}
block_146:
{
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; uint8_t x_81; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
lean_dec_ref(x_79);
x_81 = lean_unbox(x_80);
lean_dec(x_80);
if (x_81 == 0)
{
lean_object* x_82; 
x_82 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___redArg(x_76, x_5, x_13);
lean_dec(x_76);
if (lean_obj_tag(x_82) == 0)
{
uint8_t x_83; 
x_83 = !lean_is_exclusive(x_82);
if (x_83 == 0)
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_82, 0);
if (lean_obj_tag(x_84) == 1)
{
lean_object* x_85; lean_object* x_86; 
lean_free_object(x_82);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
lean_dec_ref(x_84);
x_86 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___redArg(x_78, x_5, x_13);
lean_dec(x_78);
if (lean_obj_tag(x_86) == 0)
{
uint8_t x_87; 
x_87 = !lean_is_exclusive(x_86);
if (x_87 == 0)
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_86, 0);
if (lean_obj_tag(x_88) == 1)
{
lean_object* x_89; lean_object* x_90; 
lean_free_object(x_86);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
lean_dec_ref(x_88);
x_90 = l_Lean_Meta_Grind_alreadyInternalized___redArg(x_85, x_5);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; uint8_t x_92; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_unbox(x_91);
lean_dec(x_91);
if (x_92 == 0)
{
x_16 = x_89;
x_17 = x_85;
x_18 = x_90;
goto block_57;
}
else
{
lean_object* x_93; 
lean_dec_ref(x_90);
x_93 = l_Lean_Meta_Grind_alreadyInternalized___redArg(x_89, x_5);
x_16 = x_89;
x_17 = x_85;
x_18 = x_93;
goto block_57;
}
}
else
{
x_16 = x_89;
x_17 = x_85;
x_18 = x_90;
goto block_57;
}
}
else
{
lean_object* x_94; 
lean_dec(x_88);
lean_dec(x_85);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_94 = lean_box(0);
lean_ctor_set(x_86, 0, x_94);
return x_86;
}
}
else
{
lean_object* x_95; 
x_95 = lean_ctor_get(x_86, 0);
lean_inc(x_95);
lean_dec(x_86);
if (lean_obj_tag(x_95) == 1)
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
lean_dec_ref(x_95);
x_97 = l_Lean_Meta_Grind_alreadyInternalized___redArg(x_85, x_5);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; uint8_t x_99; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_unbox(x_98);
lean_dec(x_98);
if (x_99 == 0)
{
x_16 = x_96;
x_17 = x_85;
x_18 = x_97;
goto block_57;
}
else
{
lean_object* x_100; 
lean_dec_ref(x_97);
x_100 = l_Lean_Meta_Grind_alreadyInternalized___redArg(x_96, x_5);
x_16 = x_96;
x_17 = x_85;
x_18 = x_100;
goto block_57;
}
}
else
{
x_16 = x_96;
x_17 = x_85;
x_18 = x_97;
goto block_57;
}
}
else
{
lean_object* x_101; lean_object* x_102; 
lean_dec(x_95);
lean_dec(x_85);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_101 = lean_box(0);
x_102 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_102, 0, x_101);
return x_102;
}
}
}
else
{
uint8_t x_103; 
lean_dec(x_85);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_103 = !lean_is_exclusive(x_86);
if (x_103 == 0)
{
return x_86;
}
else
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_86, 0);
lean_inc(x_104);
lean_dec(x_86);
x_105 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_105, 0, x_104);
return x_105;
}
}
}
else
{
lean_object* x_106; 
lean_dec(x_84);
lean_dec(x_78);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_106 = lean_box(0);
lean_ctor_set(x_82, 0, x_106);
return x_82;
}
}
else
{
lean_object* x_107; 
x_107 = lean_ctor_get(x_82, 0);
lean_inc(x_107);
lean_dec(x_82);
if (lean_obj_tag(x_107) == 1)
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
lean_dec_ref(x_107);
x_109 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___redArg(x_78, x_5, x_13);
lean_dec(x_78);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 x_111 = x_109;
} else {
 lean_dec_ref(x_109);
 x_111 = lean_box(0);
}
if (lean_obj_tag(x_110) == 1)
{
lean_object* x_112; lean_object* x_113; 
lean_dec(x_111);
x_112 = lean_ctor_get(x_110, 0);
lean_inc(x_112);
lean_dec_ref(x_110);
x_113 = l_Lean_Meta_Grind_alreadyInternalized___redArg(x_108, x_5);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; uint8_t x_115; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_unbox(x_114);
lean_dec(x_114);
if (x_115 == 0)
{
x_16 = x_112;
x_17 = x_108;
x_18 = x_113;
goto block_57;
}
else
{
lean_object* x_116; 
lean_dec_ref(x_113);
x_116 = l_Lean_Meta_Grind_alreadyInternalized___redArg(x_112, x_5);
x_16 = x_112;
x_17 = x_108;
x_18 = x_116;
goto block_57;
}
}
else
{
x_16 = x_112;
x_17 = x_108;
x_18 = x_113;
goto block_57;
}
}
else
{
lean_object* x_117; lean_object* x_118; 
lean_dec(x_110);
lean_dec(x_108);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_117 = lean_box(0);
if (lean_is_scalar(x_111)) {
 x_118 = lean_alloc_ctor(0, 1, 0);
} else {
 x_118 = x_111;
}
lean_ctor_set(x_118, 0, x_117);
return x_118;
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_108);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_119 = lean_ctor_get(x_109, 0);
lean_inc(x_119);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 x_120 = x_109;
} else {
 lean_dec_ref(x_109);
 x_120 = lean_box(0);
}
if (lean_is_scalar(x_120)) {
 x_121 = lean_alloc_ctor(1, 1, 0);
} else {
 x_121 = x_120;
}
lean_ctor_set(x_121, 0, x_119);
return x_121;
}
}
else
{
lean_object* x_122; lean_object* x_123; 
lean_dec(x_107);
lean_dec(x_78);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_122 = lean_box(0);
x_123 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_123, 0, x_122);
return x_123;
}
}
}
else
{
uint8_t x_124; 
lean_dec(x_78);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_124 = !lean_is_exclusive(x_82);
if (x_124 == 0)
{
return x_82;
}
else
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_82, 0);
lean_inc(x_125);
lean_dec(x_82);
x_126 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_126, 0, x_125);
return x_126;
}
}
}
else
{
lean_object* x_127; 
x_127 = l_Lean_Meta_Grind_isEqv___redArg(x_76, x_78, x_5);
lean_dec(x_78);
lean_dec(x_76);
if (lean_obj_tag(x_127) == 0)
{
uint8_t x_128; 
x_128 = !lean_is_exclusive(x_127);
if (x_128 == 0)
{
lean_object* x_129; uint8_t x_130; 
x_129 = lean_ctor_get(x_127, 0);
x_130 = lean_unbox(x_129);
lean_dec(x_129);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; 
lean_free_object(x_127);
x_131 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_131, 0, x_1);
lean_ctor_set(x_131, 1, x_2);
x_132 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate(x_131, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_132;
}
else
{
lean_object* x_133; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_133 = lean_box(0);
lean_ctor_set(x_127, 0, x_133);
return x_127;
}
}
else
{
lean_object* x_134; uint8_t x_135; 
x_134 = lean_ctor_get(x_127, 0);
lean_inc(x_134);
lean_dec(x_127);
x_135 = lean_unbox(x_134);
lean_dec(x_134);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; 
x_136 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_136, 0, x_1);
lean_ctor_set(x_136, 1, x_2);
x_137 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate(x_136, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_137;
}
else
{
lean_object* x_138; lean_object* x_139; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_138 = lean_box(0);
x_139 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_139, 0, x_138);
return x_139;
}
}
}
else
{
uint8_t x_140; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_140 = !lean_is_exclusive(x_127);
if (x_140 == 0)
{
return x_127;
}
else
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_ctor_get(x_127, 0);
lean_inc(x_141);
lean_dec(x_127);
x_142 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_142, 0, x_141);
return x_142;
}
}
}
}
else
{
uint8_t x_143; 
lean_dec(x_78);
lean_dec(x_76);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_143 = !lean_is_exclusive(x_79);
if (x_143 == 0)
{
return x_79;
}
else
{
lean_object* x_144; lean_object* x_145; 
x_144 = lean_ctor_get(x_79, 0);
lean_inc(x_144);
lean_dec(x_79);
x_145 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_145, 0, x_144);
return x_145;
}
}
}
}
else
{
uint8_t x_151; 
lean_dec(x_76);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_151 = !lean_is_exclusive(x_77);
if (x_151 == 0)
{
return x_77;
}
else
{
lean_object* x_152; lean_object* x_153; 
x_152 = lean_ctor_get(x_77, 0);
lean_inc(x_152);
lean_dec(x_77);
x_153 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_153, 0, x_152);
return x_153;
}
}
}
else
{
uint8_t x_154; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_154 = !lean_is_exclusive(x_75);
if (x_154 == 0)
{
return x_75;
}
else
{
lean_object* x_155; lean_object* x_156; 
x_155 = lean_ctor_get(x_75, 0);
lean_inc(x_155);
lean_dec(x_75);
x_156 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_156, 0, x_155);
return x_156;
}
}
}
}
else
{
lean_object* x_157; 
lean_dec(x_71);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_157 = lean_box(0);
lean_ctor_set(x_69, 0, x_157);
return x_69;
}
}
else
{
lean_object* x_158; 
x_158 = lean_ctor_get(x_69, 0);
lean_inc(x_158);
lean_dec(x_69);
if (lean_obj_tag(x_158) == 1)
{
lean_object* x_159; uint8_t x_160; 
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
lean_dec_ref(x_158);
x_160 = l_Lean_Meta_Grind_Order_Weight_isZero(x_159);
lean_dec(x_159);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_161 = lean_box(0);
x_162 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_162, 0, x_161);
return x_162;
}
else
{
lean_object* x_163; 
x_163 = l_Lean_Meta_Grind_Order_getExpr(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
lean_dec_ref(x_163);
x_165 = l_Lean_Meta_Grind_Order_getExpr(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_207; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
lean_dec_ref(x_165);
x_207 = l_Lean_Meta_Grind_alreadyInternalized___redArg(x_164, x_5);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; uint8_t x_209; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
x_209 = lean_unbox(x_208);
lean_dec(x_208);
if (x_209 == 0)
{
x_167 = x_207;
goto block_206;
}
else
{
lean_object* x_210; 
lean_dec_ref(x_207);
x_210 = l_Lean_Meta_Grind_alreadyInternalized___redArg(x_166, x_5);
x_167 = x_210;
goto block_206;
}
}
else
{
x_167 = x_207;
goto block_206;
}
block_206:
{
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; uint8_t x_169; 
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
lean_dec_ref(x_167);
x_169 = lean_unbox(x_168);
lean_dec(x_168);
if (x_169 == 0)
{
lean_object* x_170; 
x_170 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___redArg(x_164, x_5, x_13);
lean_dec(x_164);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 x_172 = x_170;
} else {
 lean_dec_ref(x_170);
 x_172 = lean_box(0);
}
if (lean_obj_tag(x_171) == 1)
{
lean_object* x_173; lean_object* x_174; 
lean_dec(x_172);
x_173 = lean_ctor_get(x_171, 0);
lean_inc(x_173);
lean_dec_ref(x_171);
x_174 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq_getOriginal_x3f___redArg(x_166, x_5, x_13);
lean_dec(x_166);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; lean_object* x_176; 
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 x_176 = x_174;
} else {
 lean_dec_ref(x_174);
 x_176 = lean_box(0);
}
if (lean_obj_tag(x_175) == 1)
{
lean_object* x_177; lean_object* x_178; 
lean_dec(x_176);
x_177 = lean_ctor_get(x_175, 0);
lean_inc(x_177);
lean_dec_ref(x_175);
x_178 = l_Lean_Meta_Grind_alreadyInternalized___redArg(x_173, x_5);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; uint8_t x_180; 
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_unbox(x_179);
lean_dec(x_179);
if (x_180 == 0)
{
x_16 = x_177;
x_17 = x_173;
x_18 = x_178;
goto block_57;
}
else
{
lean_object* x_181; 
lean_dec_ref(x_178);
x_181 = l_Lean_Meta_Grind_alreadyInternalized___redArg(x_177, x_5);
x_16 = x_177;
x_17 = x_173;
x_18 = x_181;
goto block_57;
}
}
else
{
x_16 = x_177;
x_17 = x_173;
x_18 = x_178;
goto block_57;
}
}
else
{
lean_object* x_182; lean_object* x_183; 
lean_dec(x_175);
lean_dec(x_173);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_182 = lean_box(0);
if (lean_is_scalar(x_176)) {
 x_183 = lean_alloc_ctor(0, 1, 0);
} else {
 x_183 = x_176;
}
lean_ctor_set(x_183, 0, x_182);
return x_183;
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_173);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_184 = lean_ctor_get(x_174, 0);
lean_inc(x_184);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 x_185 = x_174;
} else {
 lean_dec_ref(x_174);
 x_185 = lean_box(0);
}
if (lean_is_scalar(x_185)) {
 x_186 = lean_alloc_ctor(1, 1, 0);
} else {
 x_186 = x_185;
}
lean_ctor_set(x_186, 0, x_184);
return x_186;
}
}
else
{
lean_object* x_187; lean_object* x_188; 
lean_dec(x_171);
lean_dec(x_166);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_187 = lean_box(0);
if (lean_is_scalar(x_172)) {
 x_188 = lean_alloc_ctor(0, 1, 0);
} else {
 x_188 = x_172;
}
lean_ctor_set(x_188, 0, x_187);
return x_188;
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_166);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_189 = lean_ctor_get(x_170, 0);
lean_inc(x_189);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 x_190 = x_170;
} else {
 lean_dec_ref(x_170);
 x_190 = lean_box(0);
}
if (lean_is_scalar(x_190)) {
 x_191 = lean_alloc_ctor(1, 1, 0);
} else {
 x_191 = x_190;
}
lean_ctor_set(x_191, 0, x_189);
return x_191;
}
}
else
{
lean_object* x_192; 
x_192 = l_Lean_Meta_Grind_isEqv___redArg(x_164, x_166, x_5);
lean_dec(x_166);
lean_dec(x_164);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; uint8_t x_195; 
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 x_194 = x_192;
} else {
 lean_dec_ref(x_192);
 x_194 = lean_box(0);
}
x_195 = lean_unbox(x_193);
lean_dec(x_193);
if (x_195 == 0)
{
lean_object* x_196; lean_object* x_197; 
lean_dec(x_194);
x_196 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_196, 0, x_1);
lean_ctor_set(x_196, 1, x_2);
x_197 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate(x_196, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_197;
}
else
{
lean_object* x_198; lean_object* x_199; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_198 = lean_box(0);
if (lean_is_scalar(x_194)) {
 x_199 = lean_alloc_ctor(0, 1, 0);
} else {
 x_199 = x_194;
}
lean_ctor_set(x_199, 0, x_198);
return x_199;
}
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_200 = lean_ctor_get(x_192, 0);
lean_inc(x_200);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 x_201 = x_192;
} else {
 lean_dec_ref(x_192);
 x_201 = lean_box(0);
}
if (lean_is_scalar(x_201)) {
 x_202 = lean_alloc_ctor(1, 1, 0);
} else {
 x_202 = x_201;
}
lean_ctor_set(x_202, 0, x_200);
return x_202;
}
}
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; 
lean_dec(x_166);
lean_dec(x_164);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_203 = lean_ctor_get(x_167, 0);
lean_inc(x_203);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 x_204 = x_167;
} else {
 lean_dec_ref(x_167);
 x_204 = lean_box(0);
}
if (lean_is_scalar(x_204)) {
 x_205 = lean_alloc_ctor(1, 1, 0);
} else {
 x_205 = x_204;
}
lean_ctor_set(x_205, 0, x_203);
return x_205;
}
}
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
lean_dec(x_164);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_211 = lean_ctor_get(x_165, 0);
lean_inc(x_211);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 x_212 = x_165;
} else {
 lean_dec_ref(x_165);
 x_212 = lean_box(0);
}
if (lean_is_scalar(x_212)) {
 x_213 = lean_alloc_ctor(1, 1, 0);
} else {
 x_213 = x_212;
}
lean_ctor_set(x_213, 0, x_211);
return x_213;
}
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_214 = lean_ctor_get(x_163, 0);
lean_inc(x_214);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 x_215 = x_163;
} else {
 lean_dec_ref(x_163);
 x_215 = lean_box(0);
}
if (lean_is_scalar(x_215)) {
 x_216 = lean_alloc_ctor(1, 1, 0);
} else {
 x_216 = x_215;
}
lean_ctor_set(x_216, 0, x_214);
return x_216;
}
}
}
else
{
lean_object* x_217; lean_object* x_218; 
lean_dec(x_158);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_217 = lean_box(0);
x_218 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_218, 0, x_217);
return x_218;
}
}
}
else
{
uint8_t x_219; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_219 = !lean_is_exclusive(x_69);
if (x_219 == 0)
{
return x_69;
}
else
{
lean_object* x_220; lean_object* x_221; 
x_220 = lean_ctor_get(x_69, 0);
lean_inc(x_220);
lean_dec(x_69);
x_221 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_221, 0, x_220);
return x_221;
}
}
}
else
{
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
goto block_64;
}
}
}
block_64:
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_box(0);
if (lean_is_scalar(x_61)) {
 x_63 = lean_alloc_ctor(0, 1, 0);
} else {
 x_63 = x_61;
}
lean_ctor_set(x_63, 0, x_62);
return x_63;
}
}
else
{
uint8_t x_222; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_222 = !lean_is_exclusive(x_59);
if (x_222 == 0)
{
return x_59;
}
else
{
lean_object* x_223; lean_object* x_224; 
x_223 = lean_ctor_get(x_59, 0);
lean_inc(x_223);
lean_dec(x_59);
x_224 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_224, 0, x_223);
return x_224;
}
}
}
else
{
lean_object* x_225; lean_object* x_226; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_225 = lean_box(0);
x_226 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_226, 0, x_225);
return x_226;
}
block_57:
{
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec_ref(x_17);
lean_dec_ref(x_16);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_22 = lean_box(0);
lean_ctor_set(x_18, 0, x_22);
return x_18;
}
else
{
lean_object* x_23; 
lean_free_object(x_18);
x_23 = l_Lean_Meta_Grind_isEqv___redArg(x_17, x_16, x_5);
lean_dec_ref(x_16);
lean_dec_ref(x_17);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_free_object(x_23);
x_27 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_2);
x_28 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate(x_27, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_28;
}
else
{
lean_object* x_29; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_29 = lean_box(0);
lean_ctor_set(x_23, 0, x_29);
return x_23;
}
}
else
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_23, 0);
lean_inc(x_30);
lean_dec(x_23);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_2);
x_33 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate(x_32, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_23);
if (x_36 == 0)
{
return x_23;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_23, 0);
lean_inc(x_37);
lean_dec(x_23);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
}
}
}
else
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_18, 0);
lean_inc(x_39);
lean_dec(x_18);
x_40 = lean_unbox(x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_dec_ref(x_17);
lean_dec_ref(x_16);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
else
{
lean_object* x_43; 
x_43 = l_Lean_Meta_Grind_isEqv___redArg(x_17, x_16, x_5);
lean_dec_ref(x_16);
lean_dec_ref(x_17);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 x_45 = x_43;
} else {
 lean_dec_ref(x_43);
 x_45 = lean_box(0);
}
x_46 = lean_unbox(x_44);
lean_dec(x_44);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_45);
x_47 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_47, 0, x_1);
lean_ctor_set(x_47, 1, x_2);
x_48 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate(x_47, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_49 = lean_box(0);
if (lean_is_scalar(x_45)) {
 x_50 = lean_alloc_ctor(0, 1, 0);
} else {
 x_50 = x_45;
}
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_51 = lean_ctor_get(x_43, 0);
lean_inc(x_51);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 x_52 = x_43;
} else {
 lean_dec_ref(x_43);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(1, 1, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_51);
return x_53;
}
}
}
}
else
{
uint8_t x_54; 
lean_dec_ref(x_17);
lean_dec_ref(x_16);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_18);
if (x_54 == 0)
{
return x_18;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_18, 0);
lean_inc(x_55);
lean_dec(x_18);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_1);
x_13 = lean_nat_dec_lt(x_3, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_3);
x_14 = lean_box(0);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get(x_4, 1);
x_17 = lean_array_fget_borrowed(x_1, x_3);
x_18 = lean_ctor_get(x_17, 0);
x_19 = lean_ctor_get(x_17, 1);
x_20 = lean_nat_dec_eq(x_15, x_18);
if (x_20 == 0)
{
x_5 = x_20;
goto block_11;
}
else
{
uint8_t x_21; 
x_21 = lean_nat_dec_eq(x_16, x_19);
x_5 = x_21;
goto block_11;
}
}
block_11:
{
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_3, x_6);
lean_dec(x_3);
x_3 = x_7;
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_array_fget_borrowed(x_2, x_3);
lean_dec(x_3);
lean_inc(x_9);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1___redArg(x_1, x_2, x_3, x_4);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0___redArg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_5 = x_1;
} else {
 lean_dec_ref(x_1);
 x_5 = lean_box(0);
}
x_6 = lean_box(2);
x_7 = 5;
x_8 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg___closed__1;
x_9 = lean_usize_land(x_2, x_8);
x_10 = lean_usize_to_nat(x_9);
x_11 = lean_array_get(x_6, x_4, x_10);
lean_dec(x_10);
lean_dec_ref(x_4);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_18 = lean_ctor_get(x_3, 0);
x_19 = lean_ctor_get(x_3, 1);
x_20 = lean_ctor_get(x_12, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_dec(x_12);
x_22 = lean_nat_dec_eq(x_18, x_20);
lean_dec(x_20);
if (x_22 == 0)
{
lean_dec(x_21);
x_14 = x_22;
goto block_17;
}
else
{
uint8_t x_23; 
x_23 = lean_nat_dec_eq(x_19, x_21);
lean_dec(x_21);
x_14 = x_23;
goto block_17;
}
block_17:
{
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_13);
lean_dec(x_5);
x_15 = lean_box(0);
return x_15;
}
else
{
lean_object* x_16; 
if (lean_is_scalar(x_5)) {
 x_16 = lean_alloc_ctor(1, 1, 0);
} else {
 x_16 = x_5;
 lean_ctor_set_tag(x_16, 1);
}
lean_ctor_set(x_16, 0, x_13);
return x_16;
}
}
}
case 1:
{
lean_object* x_24; size_t x_25; 
lean_dec(x_5);
x_24 = lean_ctor_get(x_11, 0);
lean_inc(x_24);
lean_dec_ref(x_11);
x_25 = lean_usize_shift_right(x_2, x_7);
x_1 = x_24;
x_2 = x_25;
goto _start;
}
default: 
{
lean_object* x_27; 
lean_dec(x_5);
x_27 = lean_box(0);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_28);
x_29 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_29);
lean_dec_ref(x_1);
x_30 = lean_unsigned_to_nat(0u);
x_31 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1___redArg(x_28, x_29, x_30, x_3);
lean_dec_ref(x_29);
lean_dec_ref(x_28);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0___redArg(x_1, x_4, x_3);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; size_t x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_uint64_of_nat(x_3);
x_6 = lean_uint64_of_nat(x_4);
x_7 = lean_uint64_mix_hash(x_5, x_6);
x_8 = lean_uint64_to_usize(x_7);
x_9 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0___redArg(x_1, x_8, x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_4, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_4, 1);
lean_inc(x_20);
lean_dec_ref(x_4);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
lean_inc(x_5);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_23 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse(x_1, x_2, x_3, x_21, x_22, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_23) == 0)
{
lean_dec_ref(x_23);
x_4 = x_20;
goto _start;
}
else
{
lean_dec(x_20);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_17;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_4, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_4, 1);
lean_inc(x_20);
lean_dec_ref(x_4);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
lean_inc(x_5);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_23 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue(x_1, x_2, x_3, x_21, x_22, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_23) == 0)
{
lean_dec_ref(x_23);
x_4 = x_20;
goto _start;
}
else
{
lean_dec(x_20);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; lean_object* x_30; 
x_30 = l_Lean_Meta_Grind_Order_getStruct(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec_ref(x_30);
x_32 = lean_ctor_get(x_31, 17);
lean_inc_ref(x_32);
lean_dec(x_31);
lean_inc(x_2);
lean_inc(x_1);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_2);
x_34 = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0___redArg(x_32, x_33);
lean_dec_ref(x_33);
if (lean_obj_tag(x_34) == 1)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec_ref(x_34);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_36 = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__2(x_1, x_2, x_3, x_35, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_36) == 0)
{
lean_dec_ref(x_36);
x_16 = lean_box(0);
goto block_29;
}
else
{
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_36;
}
}
else
{
lean_dec(x_34);
x_16 = lean_box(0);
goto block_29;
}
}
else
{
uint8_t x_37; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_30);
if (x_37 == 0)
{
return x_30;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_30, 0);
lean_inc(x_38);
lean_dec(x_30);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
block_29:
{
lean_object* x_17; 
x_17 = l_Lean_Meta_Grind_Order_getStruct(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = lean_ctor_get(x_18, 17);
lean_inc_ref(x_19);
lean_dec(x_18);
lean_inc(x_1);
lean_inc(x_2);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_2);
lean_ctor_set(x_20, 1, x_1);
x_21 = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0___redArg(x_19, x_20);
lean_dec_ref(x_20);
if (lean_obj_tag(x_21) == 1)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_23 = l_List_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__1(x_1, x_2, x_3, x_22, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
lean_dec_ref(x_23);
x_24 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_3);
return x_24;
}
else
{
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_23;
}
}
else
{
lean_object* x_25; 
lean_dec(x_21);
x_25 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_3);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_17);
if (x_26 == 0)
{
return x_17;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_17, 0);
lean_inc(x_27);
lean_dec(x_17);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0(x_1, x_2, x_5, x_4);
lean_dec_ref(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1___redArg(x_2, x_3, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_updateIfShorter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; 
x_17 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isShorter(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = lean_box(0);
lean_ctor_set(x_17, 0, x_21);
return x_17;
}
else
{
lean_object* x_22; 
lean_free_object(x_17);
lean_inc(x_5);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_22 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist___redArg(x_1, x_2, x_3, x_5, x_6);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
lean_dec_ref(x_22);
x_23 = l_Lean_Meta_Grind_Order_getProof(x_4, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec_ref(x_23);
lean_inc(x_5);
lean_inc(x_2);
lean_inc(x_1);
x_25 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___redArg(x_1, x_2, x_24, x_5, x_6);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
lean_dec_ref(x_25);
x_26 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_26;
}
else
{
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_25;
}
}
else
{
uint8_t x_27; 
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_23);
if (x_27 == 0)
{
return x_23;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_23, 0);
lean_inc(x_28);
lean_dec(x_23);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
else
{
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_22;
}
}
}
else
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_17, 0);
lean_inc(x_30);
lean_dec(x_17);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
else
{
lean_object* x_34; 
lean_inc(x_5);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_34 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist___redArg(x_1, x_2, x_3, x_5, x_6);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
lean_dec_ref(x_34);
x_35 = l_Lean_Meta_Grind_Order_getProof(x_4, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec_ref(x_35);
lean_inc(x_5);
lean_inc(x_2);
lean_inc(x_1);
x_37 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___redArg(x_1, x_2, x_36, x_5, x_6);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
lean_dec_ref(x_37);
x_38 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_38;
}
else
{
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_37;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_39 = lean_ctor_get(x_35, 0);
lean_inc(x_39);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 x_40 = x_35;
} else {
 lean_dec_ref(x_35);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(1, 1, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_39);
return x_41;
}
}
else
{
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_34;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_17);
if (x_42 == 0)
{
return x_17;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_17, 0);
lean_inc(x_43);
lean_dec(x_17);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_updateIfShorter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_updateIfShorter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_5);
lean_dec(x_2);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_4, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_4, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_4, 2);
lean_inc(x_21);
lean_dec_ref(x_4);
x_22 = l_Lean_Meta_Grind_Order_Weight_add(x_1, x_20);
lean_inc(x_5);
lean_inc(x_2);
x_23 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_updateIfShorter(x_2, x_19, x_22, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_23) == 0)
{
lean_dec_ref(x_23);
x_4 = x_21;
goto _start;
}
else
{
lean_dec(x_21);
lean_dec(x_5);
lean_dec(x_2);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_4, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_4, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_4, 2);
lean_inc(x_21);
lean_dec_ref(x_4);
lean_inc_ref(x_1);
x_25 = l_Lean_Meta_Grind_Order_Weight_add(x_20, x_1);
lean_dec(x_20);
lean_inc(x_5);
lean_inc_ref(x_25);
lean_inc(x_2);
lean_inc(x_19);
x_26 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_updateIfShorter(x_19, x_2, x_25, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
lean_dec_ref(x_26);
x_27 = l_Lean_Meta_Grind_Order_getStruct(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec_ref(x_27);
x_29 = lean_ctor_get(x_28, 19);
lean_inc_ref(x_29);
lean_dec(x_28);
x_30 = lean_ctor_get(x_29, 2);
x_31 = lean_box(0);
x_32 = lean_nat_dec_lt(x_2, x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec_ref(x_29);
x_33 = l_outOfBounds___redArg(x_31);
lean_inc(x_5);
x_34 = l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0(x_25, x_19, x_2, x_33, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec_ref(x_25);
x_22 = x_34;
goto block_24;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = l_Lean_PersistentArray_get_x21___redArg(x_31, x_29, x_2);
lean_inc(x_5);
x_36 = l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0(x_25, x_19, x_2, x_35, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec_ref(x_25);
x_22 = x_36;
goto block_24;
}
}
else
{
uint8_t x_37; 
lean_dec_ref(x_25);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_37 = !lean_is_exclusive(x_27);
if (x_37 == 0)
{
return x_27;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_27, 0);
lean_inc(x_38);
lean_dec(x_27);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
}
else
{
lean_dec_ref(x_25);
lean_dec(x_19);
x_22 = x_26;
goto block_24;
}
block_24:
{
if (lean_obj_tag(x_22) == 0)
{
lean_dec_ref(x_22);
x_4 = x_21;
goto _start;
}
else
{
lean_dec(x_21);
lean_dec(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; lean_object* x_31; 
x_31 = l_Lean_Meta_Grind_Order_getStruct(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec_ref(x_31);
x_33 = lean_ctor_get(x_32, 19);
lean_inc_ref(x_33);
lean_dec(x_32);
x_34 = lean_ctor_get(x_33, 2);
x_35 = lean_box(0);
x_36 = lean_nat_dec_lt(x_2, x_34);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_dec_ref(x_33);
x_37 = l_outOfBounds___redArg(x_35);
lean_inc(x_4);
lean_inc(x_1);
x_38 = l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0(x_3, x_1, x_2, x_37, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
x_16 = x_38;
goto block_30;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = l_Lean_PersistentArray_get_x21___redArg(x_35, x_33, x_2);
lean_inc(x_4);
lean_inc(x_1);
x_40 = l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__0(x_3, x_1, x_2, x_39, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
x_16 = x_40;
goto block_30;
}
}
else
{
uint8_t x_41; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_31);
if (x_41 == 0)
{
return x_31;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_31, 0);
lean_inc(x_42);
lean_dec(x_31);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
}
block_30:
{
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
lean_dec_ref(x_16);
x_17 = l_Lean_Meta_Grind_Order_getStruct(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = lean_ctor_get(x_18, 18);
lean_inc_ref(x_19);
lean_dec(x_18);
x_20 = lean_ctor_get(x_19, 2);
x_21 = lean_box(0);
x_22 = lean_nat_dec_lt(x_1, x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec_ref(x_19);
x_23 = l_outOfBounds___redArg(x_21);
x_24 = l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__1(x_3, x_2, x_1, x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_1);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = l_Lean_PersistentArray_get_x21___redArg(x_21, x_19, x_1);
x_26 = l_Lean_AssocList_forM___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update_spec__1(x_3, x_2, x_1, x_25, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_1);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_17);
if (x_27 == 0)
{
return x_17;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_17, 0);
lean_inc(x_28);
lean_dec(x_17);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
else
{
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_addEdge(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_81; lean_object* x_85; 
x_85 = l_Lean_Meta_Grind_isInconsistent___redArg(x_6);
if (lean_obj_tag(x_85) == 0)
{
uint8_t x_86; 
x_86 = !lean_is_exclusive(x_85);
if (x_86 == 0)
{
lean_object* x_87; uint8_t x_88; 
x_87 = lean_ctor_get(x_85, 0);
x_88 = lean_unbox(x_87);
lean_dec(x_87);
if (x_88 == 0)
{
uint8_t x_89; 
lean_free_object(x_85);
x_89 = lean_nat_dec_eq(x_1, x_2);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_90 = ((lean_object*)(l_Lean_Meta_Grind_Order_addEdge___closed__1));
x_91 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(x_90, x_14);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 x_93 = x_91;
} else {
 lean_dec_ref(x_91);
 x_93 = lean_box(0);
}
x_94 = lean_unbox(x_92);
lean_dec(x_92);
if (x_94 == 0)
{
lean_dec(x_93);
x_54 = x_5;
x_55 = x_6;
x_56 = x_7;
x_57 = x_8;
x_58 = x_9;
x_59 = x_10;
x_60 = x_11;
x_61 = x_12;
x_62 = x_13;
x_63 = x_14;
x_64 = x_15;
x_65 = lean_box(0);
goto block_80;
}
else
{
lean_object* x_95; 
x_95 = l_Lean_Meta_Grind_Order_getExpr(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
lean_dec_ref(x_95);
x_97 = l_Lean_Meta_Grind_Order_getExpr(x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_113; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
lean_dec_ref(x_97);
x_99 = lean_ctor_get(x_3, 0);
x_100 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
x_101 = l_Lean_MessageData_ofExpr(x_96);
x_102 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__3;
x_103 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
x_104 = l_Lean_MessageData_ofExpr(x_98);
x_105 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
x_106 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_102);
if (x_100 == 0)
{
lean_object* x_117; uint8_t x_118; 
x_117 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5;
x_118 = lean_int_dec_lt(x_99, x_117);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_nat_abs(x_99);
x_120 = l_Nat_reprFast(x_119);
x_107 = x_120;
goto block_112;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_121 = lean_nat_abs(x_99);
x_122 = lean_unsigned_to_nat(1u);
x_123 = lean_nat_sub(x_121, x_122);
lean_dec(x_121);
x_124 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__6));
x_125 = lean_nat_add(x_123, x_122);
lean_dec(x_123);
x_126 = l_Nat_reprFast(x_125);
x_127 = lean_string_append(x_124, x_126);
lean_dec_ref(x_126);
x_107 = x_127;
goto block_112;
}
}
else
{
lean_object* x_128; uint8_t x_129; 
x_128 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5;
x_129 = lean_int_dec_lt(x_99, x_128);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_nat_abs(x_99);
x_131 = l_Nat_reprFast(x_130);
x_113 = x_131;
goto block_116;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_132 = lean_nat_abs(x_99);
x_133 = lean_unsigned_to_nat(1u);
x_134 = lean_nat_sub(x_132, x_133);
lean_dec(x_132);
x_135 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__6));
x_136 = lean_nat_add(x_134, x_133);
lean_dec(x_134);
x_137 = l_Nat_reprFast(x_136);
x_138 = lean_string_append(x_135, x_137);
lean_dec_ref(x_137);
x_113 = x_138;
goto block_116;
}
}
block_112:
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
if (lean_is_scalar(x_93)) {
 x_108 = lean_alloc_ctor(3, 1, 0);
} else {
 x_108 = x_93;
 lean_ctor_set_tag(x_108, 3);
}
lean_ctor_set(x_108, 0, x_107);
x_109 = l_Lean_MessageData_ofFormat(x_108);
x_110 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_110, 0, x_106);
lean_ctor_set(x_110, 1, x_109);
x_111 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___redArg(x_90, x_110, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_111) == 0)
{
lean_dec_ref(x_111);
x_54 = x_5;
x_55 = x_6;
x_56 = x_7;
x_57 = x_8;
x_58 = x_9;
x_59 = x_10;
x_60 = x_11;
x_61 = x_12;
x_62 = x_13;
x_63 = x_14;
x_64 = x_15;
x_65 = lean_box(0);
goto block_80;
}
else
{
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_111;
}
}
block_116:
{
lean_object* x_114; lean_object* x_115; 
x_114 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4));
x_115 = lean_string_append(x_113, x_114);
x_107 = x_115;
goto block_112;
}
}
else
{
uint8_t x_139; 
lean_dec(x_96);
lean_dec(x_93);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_139 = !lean_is_exclusive(x_97);
if (x_139 == 0)
{
return x_97;
}
else
{
lean_object* x_140; lean_object* x_141; 
x_140 = lean_ctor_get(x_97, 0);
lean_inc(x_140);
lean_dec(x_97);
x_141 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_141, 0, x_140);
return x_141;
}
}
}
else
{
uint8_t x_142; 
lean_dec(x_93);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_142 = !lean_is_exclusive(x_95);
if (x_142 == 0)
{
return x_95;
}
else
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_ctor_get(x_95, 0);
lean_inc(x_143);
lean_dec(x_95);
x_144 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_144, 0, x_143);
return x_144;
}
}
}
}
else
{
uint8_t x_145; 
lean_dec(x_2);
x_145 = l_Lean_Meta_Grind_Order_Weight_isNeg(x_3);
if (x_145 == 0)
{
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_81 = lean_box(0);
goto block_84;
}
else
{
lean_object* x_146; 
x_146 = l_Lean_Meta_Grind_Order_getExpr(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_1);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
lean_dec_ref(x_146);
x_148 = l_Lean_Meta_Grind_Order_mkSelfUnsatProof(x_147, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_5);
lean_dec_ref(x_3);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; 
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
lean_dec_ref(x_148);
x_150 = l_Lean_Meta_Grind_closeGoal(x_149, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_150) == 0)
{
lean_dec_ref(x_150);
x_81 = lean_box(0);
goto block_84;
}
else
{
return x_150;
}
}
else
{
uint8_t x_151; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_151 = !lean_is_exclusive(x_148);
if (x_151 == 0)
{
return x_148;
}
else
{
lean_object* x_152; lean_object* x_153; 
x_152 = lean_ctor_get(x_148, 0);
lean_inc(x_152);
lean_dec(x_148);
x_153 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_153, 0, x_152);
return x_153;
}
}
}
else
{
uint8_t x_154; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_154 = !lean_is_exclusive(x_146);
if (x_154 == 0)
{
return x_146;
}
else
{
lean_object* x_155; lean_object* x_156; 
x_155 = lean_ctor_get(x_146, 0);
lean_inc(x_155);
lean_dec(x_146);
x_156 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_156, 0, x_155);
return x_156;
}
}
}
}
}
else
{
lean_object* x_157; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_157 = lean_box(0);
lean_ctor_set(x_85, 0, x_157);
return x_85;
}
}
else
{
lean_object* x_158; uint8_t x_159; 
x_158 = lean_ctor_get(x_85, 0);
lean_inc(x_158);
lean_dec(x_85);
x_159 = lean_unbox(x_158);
lean_dec(x_158);
if (x_159 == 0)
{
uint8_t x_160; 
x_160 = lean_nat_dec_eq(x_1, x_2);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; 
x_161 = ((lean_object*)(l_Lean_Meta_Grind_Order_addEdge___closed__1));
x_162 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(x_161, x_14);
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 x_164 = x_162;
} else {
 lean_dec_ref(x_162);
 x_164 = lean_box(0);
}
x_165 = lean_unbox(x_163);
lean_dec(x_163);
if (x_165 == 0)
{
lean_dec(x_164);
x_54 = x_5;
x_55 = x_6;
x_56 = x_7;
x_57 = x_8;
x_58 = x_9;
x_59 = x_10;
x_60 = x_11;
x_61 = x_12;
x_62 = x_13;
x_63 = x_14;
x_64 = x_15;
x_65 = lean_box(0);
goto block_80;
}
else
{
lean_object* x_166; 
x_166 = l_Lean_Meta_Grind_Order_getExpr(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; 
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
lean_dec_ref(x_166);
x_168 = l_Lean_Meta_Grind_Order_getExpr(x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; lean_object* x_170; uint8_t x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_184; 
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
lean_dec_ref(x_168);
x_170 = lean_ctor_get(x_3, 0);
x_171 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
x_172 = l_Lean_MessageData_ofExpr(x_167);
x_173 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__3;
x_174 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_173);
x_175 = l_Lean_MessageData_ofExpr(x_169);
x_176 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set(x_176, 1, x_175);
x_177 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_173);
if (x_171 == 0)
{
lean_object* x_188; uint8_t x_189; 
x_188 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5;
x_189 = lean_int_dec_lt(x_170, x_188);
if (x_189 == 0)
{
lean_object* x_190; lean_object* x_191; 
x_190 = lean_nat_abs(x_170);
x_191 = l_Nat_reprFast(x_190);
x_178 = x_191;
goto block_183;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_192 = lean_nat_abs(x_170);
x_193 = lean_unsigned_to_nat(1u);
x_194 = lean_nat_sub(x_192, x_193);
lean_dec(x_192);
x_195 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__6));
x_196 = lean_nat_add(x_194, x_193);
lean_dec(x_194);
x_197 = l_Nat_reprFast(x_196);
x_198 = lean_string_append(x_195, x_197);
lean_dec_ref(x_197);
x_178 = x_198;
goto block_183;
}
}
else
{
lean_object* x_199; uint8_t x_200; 
x_199 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5;
x_200 = lean_int_dec_lt(x_170, x_199);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; 
x_201 = lean_nat_abs(x_170);
x_202 = l_Nat_reprFast(x_201);
x_184 = x_202;
goto block_187;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_203 = lean_nat_abs(x_170);
x_204 = lean_unsigned_to_nat(1u);
x_205 = lean_nat_sub(x_203, x_204);
lean_dec(x_203);
x_206 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__6));
x_207 = lean_nat_add(x_205, x_204);
lean_dec(x_205);
x_208 = l_Nat_reprFast(x_207);
x_209 = lean_string_append(x_206, x_208);
lean_dec_ref(x_208);
x_184 = x_209;
goto block_187;
}
}
block_183:
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
if (lean_is_scalar(x_164)) {
 x_179 = lean_alloc_ctor(3, 1, 0);
} else {
 x_179 = x_164;
 lean_ctor_set_tag(x_179, 3);
}
lean_ctor_set(x_179, 0, x_178);
x_180 = l_Lean_MessageData_ofFormat(x_179);
x_181 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_181, 0, x_177);
lean_ctor_set(x_181, 1, x_180);
x_182 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___redArg(x_161, x_181, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_182) == 0)
{
lean_dec_ref(x_182);
x_54 = x_5;
x_55 = x_6;
x_56 = x_7;
x_57 = x_8;
x_58 = x_9;
x_59 = x_10;
x_60 = x_11;
x_61 = x_12;
x_62 = x_13;
x_63 = x_14;
x_64 = x_15;
x_65 = lean_box(0);
goto block_80;
}
else
{
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_182;
}
}
block_187:
{
lean_object* x_185; lean_object* x_186; 
x_185 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__4));
x_186 = lean_string_append(x_184, x_185);
x_178 = x_186;
goto block_183;
}
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
lean_dec(x_167);
lean_dec(x_164);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_210 = lean_ctor_get(x_168, 0);
lean_inc(x_210);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 x_211 = x_168;
} else {
 lean_dec_ref(x_168);
 x_211 = lean_box(0);
}
if (lean_is_scalar(x_211)) {
 x_212 = lean_alloc_ctor(1, 1, 0);
} else {
 x_212 = x_211;
}
lean_ctor_set(x_212, 0, x_210);
return x_212;
}
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; 
lean_dec(x_164);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_213 = lean_ctor_get(x_166, 0);
lean_inc(x_213);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 x_214 = x_166;
} else {
 lean_dec_ref(x_166);
 x_214 = lean_box(0);
}
if (lean_is_scalar(x_214)) {
 x_215 = lean_alloc_ctor(1, 1, 0);
} else {
 x_215 = x_214;
}
lean_ctor_set(x_215, 0, x_213);
return x_215;
}
}
}
else
{
uint8_t x_216; 
lean_dec(x_2);
x_216 = l_Lean_Meta_Grind_Order_Weight_isNeg(x_3);
if (x_216 == 0)
{
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_81 = lean_box(0);
goto block_84;
}
else
{
lean_object* x_217; 
x_217 = l_Lean_Meta_Grind_Order_getExpr(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_1);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; lean_object* x_219; 
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
lean_dec_ref(x_217);
x_219 = l_Lean_Meta_Grind_Order_mkSelfUnsatProof(x_218, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_5);
lean_dec_ref(x_3);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; lean_object* x_221; 
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
lean_dec_ref(x_219);
x_221 = l_Lean_Meta_Grind_closeGoal(x_220, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_221) == 0)
{
lean_dec_ref(x_221);
x_81 = lean_box(0);
goto block_84;
}
else
{
return x_221;
}
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_222 = lean_ctor_get(x_219, 0);
lean_inc(x_222);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 x_223 = x_219;
} else {
 lean_dec_ref(x_219);
 x_223 = lean_box(0);
}
if (lean_is_scalar(x_223)) {
 x_224 = lean_alloc_ctor(1, 1, 0);
} else {
 x_224 = x_223;
}
lean_ctor_set(x_224, 0, x_222);
return x_224;
}
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_225 = lean_ctor_get(x_217, 0);
lean_inc(x_225);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 x_226 = x_217;
} else {
 lean_dec_ref(x_217);
 x_226 = lean_box(0);
}
if (lean_is_scalar(x_226)) {
 x_227 = lean_alloc_ctor(1, 1, 0);
} else {
 x_227 = x_226;
}
lean_ctor_set(x_227, 0, x_225);
return x_227;
}
}
}
}
else
{
lean_object* x_228; lean_object* x_229; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_228 = lean_box(0);
x_229 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_229, 0, x_228);
return x_229;
}
}
}
else
{
uint8_t x_230; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_230 = !lean_is_exclusive(x_85);
if (x_230 == 0)
{
return x_85;
}
else
{
lean_object* x_231; lean_object* x_232; 
x_231 = lean_ctor_get(x_85, 0);
lean_inc(x_231);
lean_dec(x_85);
x_232 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_232, 0, x_231);
return x_232;
}
}
block_53:
{
lean_object* x_29; 
x_29 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_isShorter(x_1, x_2, x_3, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_unbox(x_31);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = lean_box(0);
lean_ctor_set(x_29, 0, x_33);
return x_29;
}
else
{
lean_object* x_34; 
lean_free_object(x_29);
lean_inc(x_17);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_34 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist___redArg(x_1, x_2, x_3, x_17, x_18);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec_ref(x_34);
lean_inc_ref(x_3);
lean_inc(x_1);
x_35 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_35, 0, x_1);
lean_ctor_set(x_35, 1, x_3);
lean_ctor_set(x_35, 2, x_4);
lean_inc(x_17);
lean_inc(x_2);
lean_inc(x_1);
x_36 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___redArg(x_1, x_2, x_35, x_17, x_18);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; 
lean_dec_ref(x_36);
lean_inc(x_17);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_37 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate(x_1, x_2, x_3, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
lean_dec_ref(x_37);
lean_inc(x_17);
x_38 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update(x_1, x_2, x_3, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; 
lean_dec_ref(x_38);
x_39 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending(x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27);
return x_39;
}
else
{
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
return x_38;
}
}
else
{
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_37;
}
}
else
{
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_36;
}
}
else
{
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_34;
}
}
}
else
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_29, 0);
lean_inc(x_40);
lean_dec(x_29);
x_41 = lean_unbox(x_40);
lean_dec(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
else
{
lean_object* x_44; 
lean_inc(x_17);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_44 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setDist___redArg(x_1, x_2, x_3, x_17, x_18);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; 
lean_dec_ref(x_44);
lean_inc_ref(x_3);
lean_inc(x_1);
x_45 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_45, 0, x_1);
lean_ctor_set(x_45, 1, x_3);
lean_ctor_set(x_45, 2, x_4);
lean_inc(x_17);
lean_inc(x_2);
lean_inc(x_1);
x_46 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setProof___redArg(x_1, x_2, x_45, x_17, x_18);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
lean_dec_ref(x_46);
lean_inc(x_17);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_47 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkToPropagate(x_1, x_2, x_3, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
lean_dec_ref(x_47);
lean_inc(x_17);
x_48 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_addEdge_update(x_1, x_2, x_3, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; 
lean_dec_ref(x_48);
x_49 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending(x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27);
return x_49;
}
else
{
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
return x_48;
}
}
else
{
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_47;
}
}
else
{
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_46;
}
}
else
{
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_44;
}
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_29);
if (x_50 == 0)
{
return x_29;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_29, 0);
lean_inc(x_51);
lean_dec(x_29);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
}
}
block_80:
{
lean_object* x_66; 
x_66 = l_Lean_Meta_Grind_Order_getDist_x3f(x_2, x_1, x_54, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_63, x_64);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
lean_dec_ref(x_66);
if (lean_obj_tag(x_67) == 1)
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
lean_dec_ref(x_67);
lean_inc(x_68);
x_69 = l_Lean_Meta_Grind_Order_Weight_add(x_3, x_68);
x_70 = l_Lean_Meta_Grind_Order_Weight_isNeg(x_69);
lean_dec_ref(x_69);
if (x_70 == 0)
{
lean_dec(x_68);
x_17 = x_54;
x_18 = x_55;
x_19 = x_56;
x_20 = x_57;
x_21 = x_58;
x_22 = x_59;
x_23 = x_60;
x_24 = x_61;
x_25 = x_62;
x_26 = x_63;
x_27 = x_64;
x_28 = lean_box(0);
goto block_53;
}
else
{
lean_object* x_71; 
x_71 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_setUnsat(x_1, x_2, x_3, x_4, x_68, x_54, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62, x_63, x_64);
lean_dec(x_68);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
if (lean_obj_tag(x_71) == 0)
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_71, 0);
lean_dec(x_73);
x_74 = lean_box(0);
lean_ctor_set(x_71, 0, x_74);
return x_71;
}
else
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_71);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_76, 0, x_75);
return x_76;
}
}
else
{
return x_71;
}
}
}
else
{
lean_dec(x_67);
x_17 = x_54;
x_18 = x_55;
x_19 = x_56;
x_20 = x_57;
x_21 = x_58;
x_22 = x_59;
x_23 = x_60;
x_24 = x_61;
x_25 = x_62;
x_26 = x_63;
x_27 = x_64;
x_28 = lean_box(0);
goto block_53;
}
}
else
{
uint8_t x_77; 
lean_dec(x_64);
lean_dec_ref(x_63);
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_77 = !lean_is_exclusive(x_66);
if (x_77 == 0)
{
return x_66;
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_66, 0);
lean_inc(x_78);
lean_dec(x_66);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_78);
return x_79;
}
}
}
block_84:
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_box(0);
x_83 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_83, 0, x_82);
return x_83;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_addEdge___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Lean_Meta_Grind_Order_addEdge(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_17;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__1));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_79 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__4));
x_80 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(x_79, x_13);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
lean_dec_ref(x_80);
x_82 = lean_unbox(x_81);
lean_dec(x_81);
if (x_82 == 0)
{
x_59 = x_4;
x_60 = x_5;
x_61 = x_6;
x_62 = x_7;
x_63 = x_8;
x_64 = x_9;
x_65 = x_10;
x_66 = x_11;
x_67 = x_12;
x_68 = x_13;
x_69 = x_14;
x_70 = lean_box(0);
goto block_78;
}
else
{
lean_object* x_83; 
x_83 = l_Lean_Meta_Grind_Order_Cnstr_pp(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
lean_dec_ref(x_83);
x_85 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___redArg(x_79, x_84, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_85) == 0)
{
lean_dec_ref(x_85);
x_59 = x_4;
x_60 = x_5;
x_61 = x_6;
x_62 = x_7;
x_63 = x_8;
x_64 = x_9;
x_65 = x_10;
x_66 = x_11;
x_67 = x_12;
x_68 = x_13;
x_69 = x_14;
x_70 = lean_box(0);
goto block_78;
}
else
{
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_85;
}
}
else
{
uint8_t x_86; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_86 = !lean_is_exclusive(x_83);
if (x_86 == 0)
{
return x_83;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_83, 0);
lean_inc(x_87);
lean_dec(x_83);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_87);
return x_88;
}
}
}
block_35:
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_33, 0, x_26);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_32);
x_34 = l_Lean_Meta_Grind_Order_addEdge(x_21, x_27, x_33, x_29, x_31, x_19, x_16, x_22, x_28, x_17, x_20, x_24, x_23, x_25, x_30);
return x_34;
}
block_58:
{
uint8_t x_49; 
x_49 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
if (x_49 == 1)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_50 = lean_ctor_get(x_1, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_1, 1);
lean_inc(x_51);
x_52 = lean_ctor_get(x_1, 2);
lean_inc(x_52);
lean_dec_ref(x_1);
x_53 = 1;
x_16 = x_39;
x_17 = x_42;
x_18 = lean_box(0);
x_19 = x_38;
x_20 = x_43;
x_21 = x_50;
x_22 = x_40;
x_23 = x_45;
x_24 = x_44;
x_25 = x_46;
x_26 = x_52;
x_27 = x_51;
x_28 = x_41;
x_29 = x_36;
x_30 = x_47;
x_31 = x_37;
x_32 = x_53;
goto block_35;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_54 = lean_ctor_get(x_1, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_1, 1);
lean_inc(x_55);
x_56 = lean_ctor_get(x_1, 2);
lean_inc(x_56);
lean_dec_ref(x_1);
x_57 = 0;
x_16 = x_39;
x_17 = x_42;
x_18 = lean_box(0);
x_19 = x_38;
x_20 = x_43;
x_21 = x_54;
x_22 = x_40;
x_23 = x_45;
x_24 = x_44;
x_25 = x_46;
x_26 = x_56;
x_27 = x_55;
x_28 = x_41;
x_29 = x_36;
x_30 = x_47;
x_31 = x_37;
x_32 = x_57;
goto block_35;
}
}
block_78:
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_1, 4);
if (lean_obj_tag(x_71) == 1)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_72 = lean_ctor_get(x_1, 3);
x_73 = lean_ctor_get(x_71, 0);
x_74 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__2;
lean_inc_ref(x_2);
x_75 = l_Lean_Meta_mkOfEqTrueCore(x_2, x_3);
lean_inc(x_73);
lean_inc_ref(x_72);
x_76 = l_Lean_mkApp4(x_74, x_2, x_72, x_73, x_75);
x_36 = x_76;
x_37 = x_59;
x_38 = x_60;
x_39 = x_61;
x_40 = x_62;
x_41 = x_63;
x_42 = x_64;
x_43 = x_65;
x_44 = x_66;
x_45 = x_67;
x_46 = x_68;
x_47 = x_69;
x_48 = lean_box(0);
goto block_58;
}
else
{
lean_object* x_77; 
x_77 = l_Lean_Meta_mkOfEqTrueCore(x_2, x_3);
x_36 = x_77;
x_37 = x_59;
x_38 = x_60;
x_39 = x_61;
x_40 = x_62;
x_41 = x_63;
x_42 = x_64;
x_43 = x_65;
x_44 = x_66;
x_45 = x_67;
x_46 = x_68;
x_47 = x_69;
x_48 = lean_box(0);
goto block_58;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__1));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Level_ofNat(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__7;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__8;
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__6));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__11));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__14));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__27));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__29));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_111; 
x_111 = l_Lean_Meta_Grind_Order_isLinearPreorder(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_111) == 0)
{
uint8_t x_112; 
x_112 = !lean_is_exclusive(x_111);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_141; uint8_t x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_174; uint8_t x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; uint8_t x_342; 
x_113 = lean_ctor_get(x_111, 0);
x_342 = lean_unbox(x_113);
if (x_342 == 0)
{
lean_object* x_343; 
lean_dec(x_113);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_343 = lean_box(0);
lean_ctor_set(x_111, 0, x_343);
return x_111;
}
else
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; uint8_t x_347; 
lean_free_object(x_111);
x_344 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__4));
x_345 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(x_344, x_13);
x_346 = lean_ctor_get(x_345, 0);
lean_inc(x_346);
lean_dec_ref(x_345);
x_347 = lean_unbox(x_346);
lean_dec(x_346);
if (x_347 == 0)
{
x_322 = x_4;
x_323 = x_5;
x_324 = x_6;
x_325 = x_7;
x_326 = x_8;
x_327 = x_9;
x_328 = x_10;
x_329 = x_11;
x_330 = x_12;
x_331 = x_13;
x_332 = x_14;
x_333 = lean_box(0);
goto block_341;
}
else
{
lean_object* x_348; 
x_348 = l_Lean_Meta_Grind_Order_Cnstr_pp(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_348) == 0)
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; 
x_349 = lean_ctor_get(x_348, 0);
lean_inc(x_349);
lean_dec_ref(x_348);
x_350 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__30;
x_351 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_351, 0, x_350);
lean_ctor_set(x_351, 1, x_349);
x_352 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___redArg(x_344, x_351, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_352) == 0)
{
lean_dec_ref(x_352);
x_322 = x_4;
x_323 = x_5;
x_324 = x_6;
x_325 = x_7;
x_326 = x_8;
x_327 = x_9;
x_328 = x_10;
x_329 = x_11;
x_330 = x_12;
x_331 = x_13;
x_332 = x_14;
x_333 = lean_box(0);
goto block_341;
}
else
{
lean_dec(x_113);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_352;
}
}
else
{
uint8_t x_353; 
lean_dec(x_113);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_353 = !lean_is_exclusive(x_348);
if (x_353 == 0)
{
return x_348;
}
else
{
lean_object* x_354; lean_object* x_355; 
x_354 = lean_ctor_get(x_348, 0);
lean_inc(x_354);
lean_dec(x_348);
x_355 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_355, 0, x_354);
return x_355;
}
}
}
}
block_140:
{
lean_object* x_136; lean_object* x_137; 
x_136 = l_Lean_eagerReflBoolTrue;
lean_inc_ref(x_135);
x_137 = l_Lean_mkApp6(x_131, x_133, x_118, x_126, x_135, x_136, x_134);
if (x_115 == 0)
{
uint8_t x_138; 
x_138 = lean_unbox(x_113);
lean_dec(x_113);
x_61 = x_114;
x_62 = x_116;
x_63 = x_117;
x_64 = x_136;
x_65 = x_135;
x_66 = x_119;
x_67 = x_120;
x_68 = x_121;
x_69 = x_122;
x_70 = x_123;
x_71 = x_124;
x_72 = x_125;
x_73 = x_127;
x_74 = x_137;
x_75 = lean_box(0);
x_76 = x_129;
x_77 = x_130;
x_78 = x_132;
x_79 = x_138;
goto block_110;
}
else
{
uint8_t x_139; 
lean_dec(x_113);
x_139 = 0;
x_61 = x_114;
x_62 = x_116;
x_63 = x_117;
x_64 = x_136;
x_65 = x_135;
x_66 = x_119;
x_67 = x_120;
x_68 = x_121;
x_69 = x_122;
x_70 = x_123;
x_71 = x_124;
x_72 = x_125;
x_73 = x_127;
x_74 = x_137;
x_75 = lean_box(0);
x_76 = x_129;
x_77 = x_130;
x_78 = x_132;
x_79 = x_139;
goto block_110;
}
}
block_173:
{
lean_object* x_162; uint8_t x_163; 
x_162 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5;
x_163 = lean_int_dec_le(x_162, x_153);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_164 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__9;
x_165 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__12;
x_166 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__15;
x_167 = lean_int_neg(x_153);
x_168 = l_Int_toNat(x_167);
lean_dec(x_167);
x_169 = l_Lean_instToExprInt_mkNat(x_168);
x_170 = l_Lean_mkApp3(x_164, x_165, x_166, x_169);
x_114 = x_141;
x_115 = x_142;
x_116 = x_143;
x_117 = x_144;
x_118 = x_145;
x_119 = x_146;
x_120 = x_147;
x_121 = x_148;
x_122 = x_149;
x_123 = x_150;
x_124 = x_151;
x_125 = x_152;
x_126 = x_161;
x_127 = x_153;
x_128 = lean_box(0);
x_129 = x_155;
x_130 = x_157;
x_131 = x_156;
x_132 = x_158;
x_133 = x_159;
x_134 = x_160;
x_135 = x_170;
goto block_140;
}
else
{
lean_object* x_171; lean_object* x_172; 
x_171 = l_Int_toNat(x_153);
x_172 = l_Lean_instToExprInt_mkNat(x_171);
x_114 = x_141;
x_115 = x_142;
x_116 = x_143;
x_117 = x_144;
x_118 = x_145;
x_119 = x_146;
x_120 = x_147;
x_121 = x_148;
x_122 = x_149;
x_123 = x_150;
x_124 = x_151;
x_125 = x_152;
x_126 = x_161;
x_127 = x_153;
x_128 = lean_box(0);
x_129 = x_155;
x_130 = x_157;
x_131 = x_156;
x_132 = x_158;
x_133 = x_159;
x_134 = x_160;
x_135 = x_172;
goto block_140;
}
}
block_218:
{
lean_object* x_192; 
x_192 = l_Lean_Meta_Grind_Order_mkLinearOrdRingPrefix(x_191, x_189, x_185, x_176, x_174, x_177, x_178, x_182, x_181, x_186, x_188, x_179);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; 
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
lean_dec_ref(x_192);
x_194 = l_Lean_Meta_Grind_Order_getExpr(x_184, x_189, x_185, x_176, x_174, x_177, x_178, x_182, x_181, x_186, x_188, x_179);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; lean_object* x_196; 
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
lean_dec_ref(x_194);
x_196 = l_Lean_Meta_Grind_Order_getExpr(x_183, x_189, x_185, x_176, x_174, x_177, x_178, x_182, x_181, x_186, x_188, x_179);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; 
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
lean_dec_ref(x_196);
x_198 = lean_int_neg(x_187);
x_199 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5;
x_200 = lean_int_dec_le(x_199, x_187);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
lean_dec(x_187);
x_201 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__9;
x_202 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__12;
x_203 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__15;
x_204 = l_Int_toNat(x_198);
x_205 = l_Lean_instToExprInt_mkNat(x_204);
x_206 = l_Lean_mkApp3(x_201, x_202, x_203, x_205);
x_141 = x_174;
x_142 = x_175;
x_143 = x_176;
x_144 = x_177;
x_145 = x_197;
x_146 = x_178;
x_147 = x_179;
x_148 = x_181;
x_149 = x_182;
x_150 = x_183;
x_151 = x_184;
x_152 = x_185;
x_153 = x_198;
x_154 = lean_box(0);
x_155 = x_186;
x_156 = x_193;
x_157 = x_188;
x_158 = x_189;
x_159 = x_195;
x_160 = x_190;
x_161 = x_206;
goto block_173;
}
else
{
lean_object* x_207; lean_object* x_208; 
x_207 = l_Int_toNat(x_187);
lean_dec(x_187);
x_208 = l_Lean_instToExprInt_mkNat(x_207);
x_141 = x_174;
x_142 = x_175;
x_143 = x_176;
x_144 = x_177;
x_145 = x_197;
x_146 = x_178;
x_147 = x_179;
x_148 = x_181;
x_149 = x_182;
x_150 = x_183;
x_151 = x_184;
x_152 = x_185;
x_153 = x_198;
x_154 = lean_box(0);
x_155 = x_186;
x_156 = x_193;
x_157 = x_188;
x_158 = x_189;
x_159 = x_195;
x_160 = x_190;
x_161 = x_208;
goto block_173;
}
}
else
{
uint8_t x_209; 
lean_dec(x_195);
lean_dec(x_193);
lean_dec_ref(x_190);
lean_dec(x_189);
lean_dec_ref(x_188);
lean_dec(x_187);
lean_dec(x_186);
lean_dec(x_185);
lean_dec(x_184);
lean_dec(x_183);
lean_dec(x_182);
lean_dec_ref(x_181);
lean_dec(x_179);
lean_dec_ref(x_178);
lean_dec(x_177);
lean_dec(x_176);
lean_dec_ref(x_174);
lean_dec(x_113);
x_209 = !lean_is_exclusive(x_196);
if (x_209 == 0)
{
return x_196;
}
else
{
lean_object* x_210; lean_object* x_211; 
x_210 = lean_ctor_get(x_196, 0);
lean_inc(x_210);
lean_dec(x_196);
x_211 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_211, 0, x_210);
return x_211;
}
}
}
else
{
uint8_t x_212; 
lean_dec(x_193);
lean_dec_ref(x_190);
lean_dec(x_189);
lean_dec_ref(x_188);
lean_dec(x_187);
lean_dec(x_186);
lean_dec(x_185);
lean_dec(x_184);
lean_dec(x_183);
lean_dec(x_182);
lean_dec_ref(x_181);
lean_dec(x_179);
lean_dec_ref(x_178);
lean_dec(x_177);
lean_dec(x_176);
lean_dec_ref(x_174);
lean_dec(x_113);
x_212 = !lean_is_exclusive(x_194);
if (x_212 == 0)
{
return x_194;
}
else
{
lean_object* x_213; lean_object* x_214; 
x_213 = lean_ctor_get(x_194, 0);
lean_inc(x_213);
lean_dec(x_194);
x_214 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_214, 0, x_213);
return x_214;
}
}
}
else
{
uint8_t x_215; 
lean_dec_ref(x_190);
lean_dec(x_189);
lean_dec_ref(x_188);
lean_dec(x_187);
lean_dec(x_186);
lean_dec(x_185);
lean_dec(x_184);
lean_dec(x_183);
lean_dec(x_182);
lean_dec_ref(x_181);
lean_dec(x_179);
lean_dec_ref(x_178);
lean_dec(x_177);
lean_dec(x_176);
lean_dec_ref(x_174);
lean_dec(x_113);
x_215 = !lean_is_exclusive(x_192);
if (x_215 == 0)
{
return x_192;
}
else
{
lean_object* x_216; lean_object* x_217; 
x_216 = lean_ctor_get(x_192, 0);
lean_inc(x_216);
lean_dec(x_192);
x_217 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_217, 0, x_216);
return x_217;
}
}
}
block_321:
{
lean_object* x_232; 
x_232 = l_Lean_Meta_Grind_Order_isRing(x_220, x_221, x_222, x_223, x_224, x_225, x_226, x_227, x_228, x_229, x_230);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; uint8_t x_234; 
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
lean_dec_ref(x_232);
x_234 = lean_unbox(x_233);
if (x_234 == 0)
{
uint8_t x_235; 
x_235 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
if (x_235 == 1)
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
lean_dec(x_113);
x_236 = lean_ctor_get(x_1, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_1, 1);
lean_inc(x_237);
lean_dec_ref(x_1);
x_238 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__17));
x_239 = l_Lean_Meta_Grind_Order_mkLeLtLinearPrefix(x_238, x_220, x_221, x_222, x_223, x_224, x_225, x_226, x_227, x_228, x_229, x_230);
if (lean_obj_tag(x_239) == 0)
{
lean_object* x_240; lean_object* x_241; 
x_240 = lean_ctor_get(x_239, 0);
lean_inc(x_240);
lean_dec_ref(x_239);
x_241 = l_Lean_Meta_Grind_Order_getExpr(x_236, x_220, x_221, x_222, x_223, x_224, x_225, x_226, x_227, x_228, x_229, x_230);
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_242; lean_object* x_243; 
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
lean_dec_ref(x_241);
x_243 = l_Lean_Meta_Grind_Order_getExpr(x_237, x_220, x_221, x_222, x_223, x_224, x_225, x_226, x_227, x_228, x_229, x_230);
if (lean_obj_tag(x_243) == 0)
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; uint8_t x_248; lean_object* x_249; 
x_244 = lean_ctor_get(x_243, 0);
lean_inc(x_244);
lean_dec_ref(x_243);
x_245 = l_Lean_mkApp3(x_240, x_242, x_244, x_219);
x_246 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5;
x_247 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_247, 0, x_246);
x_248 = lean_unbox(x_233);
lean_dec(x_233);
lean_ctor_set_uint8(x_247, sizeof(void*)*1, x_248);
x_249 = l_Lean_Meta_Grind_Order_addEdge(x_237, x_236, x_247, x_245, x_220, x_221, x_222, x_223, x_224, x_225, x_226, x_227, x_228, x_229, x_230);
return x_249;
}
else
{
uint8_t x_250; 
lean_dec(x_242);
lean_dec(x_240);
lean_dec(x_237);
lean_dec(x_236);
lean_dec(x_233);
lean_dec(x_230);
lean_dec_ref(x_229);
lean_dec(x_228);
lean_dec_ref(x_227);
lean_dec(x_226);
lean_dec_ref(x_225);
lean_dec(x_224);
lean_dec_ref(x_223);
lean_dec(x_222);
lean_dec(x_221);
lean_dec(x_220);
lean_dec_ref(x_219);
x_250 = !lean_is_exclusive(x_243);
if (x_250 == 0)
{
return x_243;
}
else
{
lean_object* x_251; lean_object* x_252; 
x_251 = lean_ctor_get(x_243, 0);
lean_inc(x_251);
lean_dec(x_243);
x_252 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_252, 0, x_251);
return x_252;
}
}
}
else
{
uint8_t x_253; 
lean_dec(x_240);
lean_dec(x_237);
lean_dec(x_236);
lean_dec(x_233);
lean_dec(x_230);
lean_dec_ref(x_229);
lean_dec(x_228);
lean_dec_ref(x_227);
lean_dec(x_226);
lean_dec_ref(x_225);
lean_dec(x_224);
lean_dec_ref(x_223);
lean_dec(x_222);
lean_dec(x_221);
lean_dec(x_220);
lean_dec_ref(x_219);
x_253 = !lean_is_exclusive(x_241);
if (x_253 == 0)
{
return x_241;
}
else
{
lean_object* x_254; lean_object* x_255; 
x_254 = lean_ctor_get(x_241, 0);
lean_inc(x_254);
lean_dec(x_241);
x_255 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_255, 0, x_254);
return x_255;
}
}
}
else
{
uint8_t x_256; 
lean_dec(x_237);
lean_dec(x_236);
lean_dec(x_233);
lean_dec(x_230);
lean_dec_ref(x_229);
lean_dec(x_228);
lean_dec_ref(x_227);
lean_dec(x_226);
lean_dec_ref(x_225);
lean_dec(x_224);
lean_dec_ref(x_223);
lean_dec(x_222);
lean_dec(x_221);
lean_dec(x_220);
lean_dec_ref(x_219);
x_256 = !lean_is_exclusive(x_239);
if (x_256 == 0)
{
return x_239;
}
else
{
lean_object* x_257; lean_object* x_258; 
x_257 = lean_ctor_get(x_239, 0);
lean_inc(x_257);
lean_dec(x_239);
x_258 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_258, 0, x_257);
return x_258;
}
}
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; 
lean_dec(x_233);
x_259 = lean_ctor_get(x_1, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_1, 1);
lean_inc(x_260);
lean_dec_ref(x_1);
x_261 = l_Lean_Meta_Grind_Order_hasLt(x_220, x_221, x_222, x_223, x_224, x_225, x_226, x_227, x_228, x_229, x_230);
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_262; uint8_t x_263; 
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
lean_dec_ref(x_261);
x_263 = lean_unbox(x_262);
if (x_263 == 0)
{
lean_object* x_264; lean_object* x_265; 
lean_dec(x_113);
x_264 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__19));
x_265 = l_Lean_Meta_Grind_Order_mkLeLinearPrefix(x_264, x_220, x_221, x_222, x_223, x_224, x_225, x_226, x_227, x_228, x_229, x_230);
if (lean_obj_tag(x_265) == 0)
{
lean_object* x_266; lean_object* x_267; 
x_266 = lean_ctor_get(x_265, 0);
lean_inc(x_266);
lean_dec_ref(x_265);
x_267 = l_Lean_Meta_Grind_Order_getExpr(x_259, x_220, x_221, x_222, x_223, x_224, x_225, x_226, x_227, x_228, x_229, x_230);
if (lean_obj_tag(x_267) == 0)
{
lean_object* x_268; lean_object* x_269; 
x_268 = lean_ctor_get(x_267, 0);
lean_inc(x_268);
lean_dec_ref(x_267);
x_269 = l_Lean_Meta_Grind_Order_getExpr(x_260, x_220, x_221, x_222, x_223, x_224, x_225, x_226, x_227, x_228, x_229, x_230);
if (lean_obj_tag(x_269) == 0)
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; uint8_t x_274; lean_object* x_275; 
x_270 = lean_ctor_get(x_269, 0);
lean_inc(x_270);
lean_dec_ref(x_269);
x_271 = l_Lean_mkApp3(x_266, x_268, x_270, x_219);
x_272 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5;
x_273 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_273, 0, x_272);
x_274 = lean_unbox(x_262);
lean_dec(x_262);
lean_ctor_set_uint8(x_273, sizeof(void*)*1, x_274);
x_275 = l_Lean_Meta_Grind_Order_addEdge(x_260, x_259, x_273, x_271, x_220, x_221, x_222, x_223, x_224, x_225, x_226, x_227, x_228, x_229, x_230);
return x_275;
}
else
{
uint8_t x_276; 
lean_dec(x_268);
lean_dec(x_266);
lean_dec(x_262);
lean_dec(x_260);
lean_dec(x_259);
lean_dec(x_230);
lean_dec_ref(x_229);
lean_dec(x_228);
lean_dec_ref(x_227);
lean_dec(x_226);
lean_dec_ref(x_225);
lean_dec(x_224);
lean_dec_ref(x_223);
lean_dec(x_222);
lean_dec(x_221);
lean_dec(x_220);
lean_dec_ref(x_219);
x_276 = !lean_is_exclusive(x_269);
if (x_276 == 0)
{
return x_269;
}
else
{
lean_object* x_277; lean_object* x_278; 
x_277 = lean_ctor_get(x_269, 0);
lean_inc(x_277);
lean_dec(x_269);
x_278 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_278, 0, x_277);
return x_278;
}
}
}
else
{
uint8_t x_279; 
lean_dec(x_266);
lean_dec(x_262);
lean_dec(x_260);
lean_dec(x_259);
lean_dec(x_230);
lean_dec_ref(x_229);
lean_dec(x_228);
lean_dec_ref(x_227);
lean_dec(x_226);
lean_dec_ref(x_225);
lean_dec(x_224);
lean_dec_ref(x_223);
lean_dec(x_222);
lean_dec(x_221);
lean_dec(x_220);
lean_dec_ref(x_219);
x_279 = !lean_is_exclusive(x_267);
if (x_279 == 0)
{
return x_267;
}
else
{
lean_object* x_280; lean_object* x_281; 
x_280 = lean_ctor_get(x_267, 0);
lean_inc(x_280);
lean_dec(x_267);
x_281 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_281, 0, x_280);
return x_281;
}
}
}
else
{
uint8_t x_282; 
lean_dec(x_262);
lean_dec(x_260);
lean_dec(x_259);
lean_dec(x_230);
lean_dec_ref(x_229);
lean_dec(x_228);
lean_dec_ref(x_227);
lean_dec(x_226);
lean_dec_ref(x_225);
lean_dec(x_224);
lean_dec_ref(x_223);
lean_dec(x_222);
lean_dec(x_221);
lean_dec(x_220);
lean_dec_ref(x_219);
x_282 = !lean_is_exclusive(x_265);
if (x_282 == 0)
{
return x_265;
}
else
{
lean_object* x_283; lean_object* x_284; 
x_283 = lean_ctor_get(x_265, 0);
lean_inc(x_283);
lean_dec(x_265);
x_284 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_284, 0, x_283);
return x_284;
}
}
}
else
{
lean_object* x_285; lean_object* x_286; 
lean_dec(x_262);
x_285 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__21));
x_286 = l_Lean_Meta_Grind_Order_mkLeLtLinearPrefix(x_285, x_220, x_221, x_222, x_223, x_224, x_225, x_226, x_227, x_228, x_229, x_230);
if (lean_obj_tag(x_286) == 0)
{
lean_object* x_287; lean_object* x_288; 
x_287 = lean_ctor_get(x_286, 0);
lean_inc(x_287);
lean_dec_ref(x_286);
x_288 = l_Lean_Meta_Grind_Order_getExpr(x_259, x_220, x_221, x_222, x_223, x_224, x_225, x_226, x_227, x_228, x_229, x_230);
if (lean_obj_tag(x_288) == 0)
{
lean_object* x_289; lean_object* x_290; 
x_289 = lean_ctor_get(x_288, 0);
lean_inc(x_289);
lean_dec_ref(x_288);
x_290 = l_Lean_Meta_Grind_Order_getExpr(x_260, x_220, x_221, x_222, x_223, x_224, x_225, x_226, x_227, x_228, x_229, x_230);
if (lean_obj_tag(x_290) == 0)
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; uint8_t x_295; lean_object* x_296; 
x_291 = lean_ctor_get(x_290, 0);
lean_inc(x_291);
lean_dec_ref(x_290);
x_292 = l_Lean_mkApp3(x_287, x_289, x_291, x_219);
x_293 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5;
x_294 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_294, 0, x_293);
x_295 = lean_unbox(x_113);
lean_dec(x_113);
lean_ctor_set_uint8(x_294, sizeof(void*)*1, x_295);
x_296 = l_Lean_Meta_Grind_Order_addEdge(x_260, x_259, x_294, x_292, x_220, x_221, x_222, x_223, x_224, x_225, x_226, x_227, x_228, x_229, x_230);
return x_296;
}
else
{
uint8_t x_297; 
lean_dec(x_289);
lean_dec(x_287);
lean_dec(x_260);
lean_dec(x_259);
lean_dec(x_230);
lean_dec_ref(x_229);
lean_dec(x_228);
lean_dec_ref(x_227);
lean_dec(x_226);
lean_dec_ref(x_225);
lean_dec(x_224);
lean_dec_ref(x_223);
lean_dec(x_222);
lean_dec(x_221);
lean_dec(x_220);
lean_dec_ref(x_219);
lean_dec(x_113);
x_297 = !lean_is_exclusive(x_290);
if (x_297 == 0)
{
return x_290;
}
else
{
lean_object* x_298; lean_object* x_299; 
x_298 = lean_ctor_get(x_290, 0);
lean_inc(x_298);
lean_dec(x_290);
x_299 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_299, 0, x_298);
return x_299;
}
}
}
else
{
uint8_t x_300; 
lean_dec(x_287);
lean_dec(x_260);
lean_dec(x_259);
lean_dec(x_230);
lean_dec_ref(x_229);
lean_dec(x_228);
lean_dec_ref(x_227);
lean_dec(x_226);
lean_dec_ref(x_225);
lean_dec(x_224);
lean_dec_ref(x_223);
lean_dec(x_222);
lean_dec(x_221);
lean_dec(x_220);
lean_dec_ref(x_219);
lean_dec(x_113);
x_300 = !lean_is_exclusive(x_288);
if (x_300 == 0)
{
return x_288;
}
else
{
lean_object* x_301; lean_object* x_302; 
x_301 = lean_ctor_get(x_288, 0);
lean_inc(x_301);
lean_dec(x_288);
x_302 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_302, 0, x_301);
return x_302;
}
}
}
else
{
uint8_t x_303; 
lean_dec(x_260);
lean_dec(x_259);
lean_dec(x_230);
lean_dec_ref(x_229);
lean_dec(x_228);
lean_dec_ref(x_227);
lean_dec(x_226);
lean_dec_ref(x_225);
lean_dec(x_224);
lean_dec_ref(x_223);
lean_dec(x_222);
lean_dec(x_221);
lean_dec(x_220);
lean_dec_ref(x_219);
lean_dec(x_113);
x_303 = !lean_is_exclusive(x_286);
if (x_303 == 0)
{
return x_286;
}
else
{
lean_object* x_304; lean_object* x_305; 
x_304 = lean_ctor_get(x_286, 0);
lean_inc(x_304);
lean_dec(x_286);
x_305 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_305, 0, x_304);
return x_305;
}
}
}
}
else
{
uint8_t x_306; 
lean_dec(x_260);
lean_dec(x_259);
lean_dec(x_230);
lean_dec_ref(x_229);
lean_dec(x_228);
lean_dec_ref(x_227);
lean_dec(x_226);
lean_dec_ref(x_225);
lean_dec(x_224);
lean_dec_ref(x_223);
lean_dec(x_222);
lean_dec(x_221);
lean_dec(x_220);
lean_dec_ref(x_219);
lean_dec(x_113);
x_306 = !lean_is_exclusive(x_261);
if (x_306 == 0)
{
return x_261;
}
else
{
lean_object* x_307; lean_object* x_308; 
x_307 = lean_ctor_get(x_261, 0);
lean_inc(x_307);
lean_dec(x_261);
x_308 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_308, 0, x_307);
return x_308;
}
}
}
}
else
{
uint8_t x_309; 
lean_dec(x_233);
x_309 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
if (x_309 == 1)
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_310 = lean_ctor_get(x_1, 0);
lean_inc(x_310);
x_311 = lean_ctor_get(x_1, 1);
lean_inc(x_311);
x_312 = lean_ctor_get(x_1, 2);
lean_inc(x_312);
lean_dec_ref(x_1);
x_313 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__23));
x_174 = x_223;
x_175 = x_309;
x_176 = x_222;
x_177 = x_224;
x_178 = x_225;
x_179 = x_230;
x_180 = lean_box(0);
x_181 = x_227;
x_182 = x_226;
x_183 = x_311;
x_184 = x_310;
x_185 = x_221;
x_186 = x_228;
x_187 = x_312;
x_188 = x_229;
x_189 = x_220;
x_190 = x_219;
x_191 = x_313;
goto block_218;
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_314 = lean_ctor_get(x_1, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_1, 1);
lean_inc(x_315);
x_316 = lean_ctor_get(x_1, 2);
lean_inc(x_316);
lean_dec_ref(x_1);
x_317 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__25));
x_174 = x_223;
x_175 = x_309;
x_176 = x_222;
x_177 = x_224;
x_178 = x_225;
x_179 = x_230;
x_180 = lean_box(0);
x_181 = x_227;
x_182 = x_226;
x_183 = x_315;
x_184 = x_314;
x_185 = x_221;
x_186 = x_228;
x_187 = x_316;
x_188 = x_229;
x_189 = x_220;
x_190 = x_219;
x_191 = x_317;
goto block_218;
}
}
}
else
{
uint8_t x_318; 
lean_dec(x_230);
lean_dec_ref(x_229);
lean_dec(x_228);
lean_dec_ref(x_227);
lean_dec(x_226);
lean_dec_ref(x_225);
lean_dec(x_224);
lean_dec_ref(x_223);
lean_dec(x_222);
lean_dec(x_221);
lean_dec(x_220);
lean_dec_ref(x_219);
lean_dec(x_113);
lean_dec_ref(x_1);
x_318 = !lean_is_exclusive(x_232);
if (x_318 == 0)
{
return x_232;
}
else
{
lean_object* x_319; lean_object* x_320; 
x_319 = lean_ctor_get(x_232, 0);
lean_inc(x_319);
lean_dec(x_232);
x_320 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_320, 0, x_319);
return x_320;
}
}
}
block_341:
{
lean_object* x_334; 
x_334 = lean_ctor_get(x_1, 4);
if (lean_obj_tag(x_334) == 1)
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_335 = lean_ctor_get(x_1, 3);
x_336 = lean_ctor_get(x_334, 0);
x_337 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__28;
lean_inc_ref(x_2);
x_338 = l_Lean_Meta_mkOfEqFalseCore(x_2, x_3);
lean_inc(x_336);
lean_inc_ref(x_335);
x_339 = l_Lean_mkApp4(x_337, x_2, x_335, x_336, x_338);
x_219 = x_339;
x_220 = x_322;
x_221 = x_323;
x_222 = x_324;
x_223 = x_325;
x_224 = x_326;
x_225 = x_327;
x_226 = x_328;
x_227 = x_329;
x_228 = x_330;
x_229 = x_331;
x_230 = x_332;
x_231 = lean_box(0);
goto block_321;
}
else
{
lean_object* x_340; 
x_340 = l_Lean_Meta_mkOfEqFalseCore(x_2, x_3);
x_219 = x_340;
x_220 = x_322;
x_221 = x_323;
x_222 = x_324;
x_223 = x_325;
x_224 = x_326;
x_225 = x_327;
x_226 = x_328;
x_227 = x_329;
x_228 = x_330;
x_229 = x_331;
x_230 = x_332;
x_231 = lean_box(0);
goto block_321;
}
}
}
else
{
lean_object* x_356; lean_object* x_357; uint8_t x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_384; uint8_t x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_417; uint8_t x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; uint8_t x_585; 
x_356 = lean_ctor_get(x_111, 0);
lean_inc(x_356);
lean_dec(x_111);
x_585 = lean_unbox(x_356);
if (x_585 == 0)
{
lean_object* x_586; lean_object* x_587; 
lean_dec(x_356);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_586 = lean_box(0);
x_587 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_587, 0, x_586);
return x_587;
}
else
{
lean_object* x_588; lean_object* x_589; lean_object* x_590; uint8_t x_591; 
x_588 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__4));
x_589 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(x_588, x_13);
x_590 = lean_ctor_get(x_589, 0);
lean_inc(x_590);
lean_dec_ref(x_589);
x_591 = lean_unbox(x_590);
lean_dec(x_590);
if (x_591 == 0)
{
x_565 = x_4;
x_566 = x_5;
x_567 = x_6;
x_568 = x_7;
x_569 = x_8;
x_570 = x_9;
x_571 = x_10;
x_572 = x_11;
x_573 = x_12;
x_574 = x_13;
x_575 = x_14;
x_576 = lean_box(0);
goto block_584;
}
else
{
lean_object* x_592; 
x_592 = l_Lean_Meta_Grind_Order_Cnstr_pp(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_592) == 0)
{
lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; 
x_593 = lean_ctor_get(x_592, 0);
lean_inc(x_593);
lean_dec_ref(x_592);
x_594 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__30;
x_595 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_595, 0, x_594);
lean_ctor_set(x_595, 1, x_593);
x_596 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___redArg(x_588, x_595, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_596) == 0)
{
lean_dec_ref(x_596);
x_565 = x_4;
x_566 = x_5;
x_567 = x_6;
x_568 = x_7;
x_569 = x_8;
x_570 = x_9;
x_571 = x_10;
x_572 = x_11;
x_573 = x_12;
x_574 = x_13;
x_575 = x_14;
x_576 = lean_box(0);
goto block_584;
}
else
{
lean_dec(x_356);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_596;
}
}
else
{
lean_object* x_597; lean_object* x_598; lean_object* x_599; 
lean_dec(x_356);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_597 = lean_ctor_get(x_592, 0);
lean_inc(x_597);
if (lean_is_exclusive(x_592)) {
 lean_ctor_release(x_592, 0);
 x_598 = x_592;
} else {
 lean_dec_ref(x_592);
 x_598 = lean_box(0);
}
if (lean_is_scalar(x_598)) {
 x_599 = lean_alloc_ctor(1, 1, 0);
} else {
 x_599 = x_598;
}
lean_ctor_set(x_599, 0, x_597);
return x_599;
}
}
}
block_383:
{
lean_object* x_379; lean_object* x_380; 
x_379 = l_Lean_eagerReflBoolTrue;
lean_inc_ref(x_378);
x_380 = l_Lean_mkApp6(x_374, x_376, x_361, x_369, x_378, x_379, x_377);
if (x_358 == 0)
{
uint8_t x_381; 
x_381 = lean_unbox(x_356);
lean_dec(x_356);
x_61 = x_357;
x_62 = x_359;
x_63 = x_360;
x_64 = x_379;
x_65 = x_378;
x_66 = x_362;
x_67 = x_363;
x_68 = x_364;
x_69 = x_365;
x_70 = x_366;
x_71 = x_367;
x_72 = x_368;
x_73 = x_370;
x_74 = x_380;
x_75 = lean_box(0);
x_76 = x_372;
x_77 = x_373;
x_78 = x_375;
x_79 = x_381;
goto block_110;
}
else
{
uint8_t x_382; 
lean_dec(x_356);
x_382 = 0;
x_61 = x_357;
x_62 = x_359;
x_63 = x_360;
x_64 = x_379;
x_65 = x_378;
x_66 = x_362;
x_67 = x_363;
x_68 = x_364;
x_69 = x_365;
x_70 = x_366;
x_71 = x_367;
x_72 = x_368;
x_73 = x_370;
x_74 = x_380;
x_75 = lean_box(0);
x_76 = x_372;
x_77 = x_373;
x_78 = x_375;
x_79 = x_382;
goto block_110;
}
}
block_416:
{
lean_object* x_405; uint8_t x_406; 
x_405 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5;
x_406 = lean_int_dec_le(x_405, x_396);
if (x_406 == 0)
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; 
x_407 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__9;
x_408 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__12;
x_409 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__15;
x_410 = lean_int_neg(x_396);
x_411 = l_Int_toNat(x_410);
lean_dec(x_410);
x_412 = l_Lean_instToExprInt_mkNat(x_411);
x_413 = l_Lean_mkApp3(x_407, x_408, x_409, x_412);
x_357 = x_384;
x_358 = x_385;
x_359 = x_386;
x_360 = x_387;
x_361 = x_388;
x_362 = x_389;
x_363 = x_390;
x_364 = x_391;
x_365 = x_392;
x_366 = x_393;
x_367 = x_394;
x_368 = x_395;
x_369 = x_404;
x_370 = x_396;
x_371 = lean_box(0);
x_372 = x_398;
x_373 = x_400;
x_374 = x_399;
x_375 = x_401;
x_376 = x_402;
x_377 = x_403;
x_378 = x_413;
goto block_383;
}
else
{
lean_object* x_414; lean_object* x_415; 
x_414 = l_Int_toNat(x_396);
x_415 = l_Lean_instToExprInt_mkNat(x_414);
x_357 = x_384;
x_358 = x_385;
x_359 = x_386;
x_360 = x_387;
x_361 = x_388;
x_362 = x_389;
x_363 = x_390;
x_364 = x_391;
x_365 = x_392;
x_366 = x_393;
x_367 = x_394;
x_368 = x_395;
x_369 = x_404;
x_370 = x_396;
x_371 = lean_box(0);
x_372 = x_398;
x_373 = x_400;
x_374 = x_399;
x_375 = x_401;
x_376 = x_402;
x_377 = x_403;
x_378 = x_415;
goto block_383;
}
}
block_461:
{
lean_object* x_435; 
x_435 = l_Lean_Meta_Grind_Order_mkLinearOrdRingPrefix(x_434, x_432, x_428, x_419, x_417, x_420, x_421, x_425, x_424, x_429, x_431, x_422);
if (lean_obj_tag(x_435) == 0)
{
lean_object* x_436; lean_object* x_437; 
x_436 = lean_ctor_get(x_435, 0);
lean_inc(x_436);
lean_dec_ref(x_435);
x_437 = l_Lean_Meta_Grind_Order_getExpr(x_427, x_432, x_428, x_419, x_417, x_420, x_421, x_425, x_424, x_429, x_431, x_422);
if (lean_obj_tag(x_437) == 0)
{
lean_object* x_438; lean_object* x_439; 
x_438 = lean_ctor_get(x_437, 0);
lean_inc(x_438);
lean_dec_ref(x_437);
x_439 = l_Lean_Meta_Grind_Order_getExpr(x_426, x_432, x_428, x_419, x_417, x_420, x_421, x_425, x_424, x_429, x_431, x_422);
if (lean_obj_tag(x_439) == 0)
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; uint8_t x_443; 
x_440 = lean_ctor_get(x_439, 0);
lean_inc(x_440);
lean_dec_ref(x_439);
x_441 = lean_int_neg(x_430);
x_442 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5;
x_443 = lean_int_dec_le(x_442, x_430);
if (x_443 == 0)
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; 
lean_dec(x_430);
x_444 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__9;
x_445 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__12;
x_446 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__15;
x_447 = l_Int_toNat(x_441);
x_448 = l_Lean_instToExprInt_mkNat(x_447);
x_449 = l_Lean_mkApp3(x_444, x_445, x_446, x_448);
x_384 = x_417;
x_385 = x_418;
x_386 = x_419;
x_387 = x_420;
x_388 = x_440;
x_389 = x_421;
x_390 = x_422;
x_391 = x_424;
x_392 = x_425;
x_393 = x_426;
x_394 = x_427;
x_395 = x_428;
x_396 = x_441;
x_397 = lean_box(0);
x_398 = x_429;
x_399 = x_436;
x_400 = x_431;
x_401 = x_432;
x_402 = x_438;
x_403 = x_433;
x_404 = x_449;
goto block_416;
}
else
{
lean_object* x_450; lean_object* x_451; 
x_450 = l_Int_toNat(x_430);
lean_dec(x_430);
x_451 = l_Lean_instToExprInt_mkNat(x_450);
x_384 = x_417;
x_385 = x_418;
x_386 = x_419;
x_387 = x_420;
x_388 = x_440;
x_389 = x_421;
x_390 = x_422;
x_391 = x_424;
x_392 = x_425;
x_393 = x_426;
x_394 = x_427;
x_395 = x_428;
x_396 = x_441;
x_397 = lean_box(0);
x_398 = x_429;
x_399 = x_436;
x_400 = x_431;
x_401 = x_432;
x_402 = x_438;
x_403 = x_433;
x_404 = x_451;
goto block_416;
}
}
else
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; 
lean_dec(x_438);
lean_dec(x_436);
lean_dec_ref(x_433);
lean_dec(x_432);
lean_dec_ref(x_431);
lean_dec(x_430);
lean_dec(x_429);
lean_dec(x_428);
lean_dec(x_427);
lean_dec(x_426);
lean_dec(x_425);
lean_dec_ref(x_424);
lean_dec(x_422);
lean_dec_ref(x_421);
lean_dec(x_420);
lean_dec(x_419);
lean_dec_ref(x_417);
lean_dec(x_356);
x_452 = lean_ctor_get(x_439, 0);
lean_inc(x_452);
if (lean_is_exclusive(x_439)) {
 lean_ctor_release(x_439, 0);
 x_453 = x_439;
} else {
 lean_dec_ref(x_439);
 x_453 = lean_box(0);
}
if (lean_is_scalar(x_453)) {
 x_454 = lean_alloc_ctor(1, 1, 0);
} else {
 x_454 = x_453;
}
lean_ctor_set(x_454, 0, x_452);
return x_454;
}
}
else
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; 
lean_dec(x_436);
lean_dec_ref(x_433);
lean_dec(x_432);
lean_dec_ref(x_431);
lean_dec(x_430);
lean_dec(x_429);
lean_dec(x_428);
lean_dec(x_427);
lean_dec(x_426);
lean_dec(x_425);
lean_dec_ref(x_424);
lean_dec(x_422);
lean_dec_ref(x_421);
lean_dec(x_420);
lean_dec(x_419);
lean_dec_ref(x_417);
lean_dec(x_356);
x_455 = lean_ctor_get(x_437, 0);
lean_inc(x_455);
if (lean_is_exclusive(x_437)) {
 lean_ctor_release(x_437, 0);
 x_456 = x_437;
} else {
 lean_dec_ref(x_437);
 x_456 = lean_box(0);
}
if (lean_is_scalar(x_456)) {
 x_457 = lean_alloc_ctor(1, 1, 0);
} else {
 x_457 = x_456;
}
lean_ctor_set(x_457, 0, x_455);
return x_457;
}
}
else
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; 
lean_dec_ref(x_433);
lean_dec(x_432);
lean_dec_ref(x_431);
lean_dec(x_430);
lean_dec(x_429);
lean_dec(x_428);
lean_dec(x_427);
lean_dec(x_426);
lean_dec(x_425);
lean_dec_ref(x_424);
lean_dec(x_422);
lean_dec_ref(x_421);
lean_dec(x_420);
lean_dec(x_419);
lean_dec_ref(x_417);
lean_dec(x_356);
x_458 = lean_ctor_get(x_435, 0);
lean_inc(x_458);
if (lean_is_exclusive(x_435)) {
 lean_ctor_release(x_435, 0);
 x_459 = x_435;
} else {
 lean_dec_ref(x_435);
 x_459 = lean_box(0);
}
if (lean_is_scalar(x_459)) {
 x_460 = lean_alloc_ctor(1, 1, 0);
} else {
 x_460 = x_459;
}
lean_ctor_set(x_460, 0, x_458);
return x_460;
}
}
block_564:
{
lean_object* x_475; 
x_475 = l_Lean_Meta_Grind_Order_isRing(x_463, x_464, x_465, x_466, x_467, x_468, x_469, x_470, x_471, x_472, x_473);
if (lean_obj_tag(x_475) == 0)
{
lean_object* x_476; uint8_t x_477; 
x_476 = lean_ctor_get(x_475, 0);
lean_inc(x_476);
lean_dec_ref(x_475);
x_477 = lean_unbox(x_476);
if (x_477 == 0)
{
uint8_t x_478; 
x_478 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
if (x_478 == 1)
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; 
lean_dec(x_356);
x_479 = lean_ctor_get(x_1, 0);
lean_inc(x_479);
x_480 = lean_ctor_get(x_1, 1);
lean_inc(x_480);
lean_dec_ref(x_1);
x_481 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__17));
x_482 = l_Lean_Meta_Grind_Order_mkLeLtLinearPrefix(x_481, x_463, x_464, x_465, x_466, x_467, x_468, x_469, x_470, x_471, x_472, x_473);
if (lean_obj_tag(x_482) == 0)
{
lean_object* x_483; lean_object* x_484; 
x_483 = lean_ctor_get(x_482, 0);
lean_inc(x_483);
lean_dec_ref(x_482);
x_484 = l_Lean_Meta_Grind_Order_getExpr(x_479, x_463, x_464, x_465, x_466, x_467, x_468, x_469, x_470, x_471, x_472, x_473);
if (lean_obj_tag(x_484) == 0)
{
lean_object* x_485; lean_object* x_486; 
x_485 = lean_ctor_get(x_484, 0);
lean_inc(x_485);
lean_dec_ref(x_484);
x_486 = l_Lean_Meta_Grind_Order_getExpr(x_480, x_463, x_464, x_465, x_466, x_467, x_468, x_469, x_470, x_471, x_472, x_473);
if (lean_obj_tag(x_486) == 0)
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; uint8_t x_491; lean_object* x_492; 
x_487 = lean_ctor_get(x_486, 0);
lean_inc(x_487);
lean_dec_ref(x_486);
x_488 = l_Lean_mkApp3(x_483, x_485, x_487, x_462);
x_489 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5;
x_490 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_490, 0, x_489);
x_491 = lean_unbox(x_476);
lean_dec(x_476);
lean_ctor_set_uint8(x_490, sizeof(void*)*1, x_491);
x_492 = l_Lean_Meta_Grind_Order_addEdge(x_480, x_479, x_490, x_488, x_463, x_464, x_465, x_466, x_467, x_468, x_469, x_470, x_471, x_472, x_473);
return x_492;
}
else
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; 
lean_dec(x_485);
lean_dec(x_483);
lean_dec(x_480);
lean_dec(x_479);
lean_dec(x_476);
lean_dec(x_473);
lean_dec_ref(x_472);
lean_dec(x_471);
lean_dec_ref(x_470);
lean_dec(x_469);
lean_dec_ref(x_468);
lean_dec(x_467);
lean_dec_ref(x_466);
lean_dec(x_465);
lean_dec(x_464);
lean_dec(x_463);
lean_dec_ref(x_462);
x_493 = lean_ctor_get(x_486, 0);
lean_inc(x_493);
if (lean_is_exclusive(x_486)) {
 lean_ctor_release(x_486, 0);
 x_494 = x_486;
} else {
 lean_dec_ref(x_486);
 x_494 = lean_box(0);
}
if (lean_is_scalar(x_494)) {
 x_495 = lean_alloc_ctor(1, 1, 0);
} else {
 x_495 = x_494;
}
lean_ctor_set(x_495, 0, x_493);
return x_495;
}
}
else
{
lean_object* x_496; lean_object* x_497; lean_object* x_498; 
lean_dec(x_483);
lean_dec(x_480);
lean_dec(x_479);
lean_dec(x_476);
lean_dec(x_473);
lean_dec_ref(x_472);
lean_dec(x_471);
lean_dec_ref(x_470);
lean_dec(x_469);
lean_dec_ref(x_468);
lean_dec(x_467);
lean_dec_ref(x_466);
lean_dec(x_465);
lean_dec(x_464);
lean_dec(x_463);
lean_dec_ref(x_462);
x_496 = lean_ctor_get(x_484, 0);
lean_inc(x_496);
if (lean_is_exclusive(x_484)) {
 lean_ctor_release(x_484, 0);
 x_497 = x_484;
} else {
 lean_dec_ref(x_484);
 x_497 = lean_box(0);
}
if (lean_is_scalar(x_497)) {
 x_498 = lean_alloc_ctor(1, 1, 0);
} else {
 x_498 = x_497;
}
lean_ctor_set(x_498, 0, x_496);
return x_498;
}
}
else
{
lean_object* x_499; lean_object* x_500; lean_object* x_501; 
lean_dec(x_480);
lean_dec(x_479);
lean_dec(x_476);
lean_dec(x_473);
lean_dec_ref(x_472);
lean_dec(x_471);
lean_dec_ref(x_470);
lean_dec(x_469);
lean_dec_ref(x_468);
lean_dec(x_467);
lean_dec_ref(x_466);
lean_dec(x_465);
lean_dec(x_464);
lean_dec(x_463);
lean_dec_ref(x_462);
x_499 = lean_ctor_get(x_482, 0);
lean_inc(x_499);
if (lean_is_exclusive(x_482)) {
 lean_ctor_release(x_482, 0);
 x_500 = x_482;
} else {
 lean_dec_ref(x_482);
 x_500 = lean_box(0);
}
if (lean_is_scalar(x_500)) {
 x_501 = lean_alloc_ctor(1, 1, 0);
} else {
 x_501 = x_500;
}
lean_ctor_set(x_501, 0, x_499);
return x_501;
}
}
else
{
lean_object* x_502; lean_object* x_503; lean_object* x_504; 
lean_dec(x_476);
x_502 = lean_ctor_get(x_1, 0);
lean_inc(x_502);
x_503 = lean_ctor_get(x_1, 1);
lean_inc(x_503);
lean_dec_ref(x_1);
x_504 = l_Lean_Meta_Grind_Order_hasLt(x_463, x_464, x_465, x_466, x_467, x_468, x_469, x_470, x_471, x_472, x_473);
if (lean_obj_tag(x_504) == 0)
{
lean_object* x_505; uint8_t x_506; 
x_505 = lean_ctor_get(x_504, 0);
lean_inc(x_505);
lean_dec_ref(x_504);
x_506 = lean_unbox(x_505);
if (x_506 == 0)
{
lean_object* x_507; lean_object* x_508; 
lean_dec(x_356);
x_507 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__19));
x_508 = l_Lean_Meta_Grind_Order_mkLeLinearPrefix(x_507, x_463, x_464, x_465, x_466, x_467, x_468, x_469, x_470, x_471, x_472, x_473);
if (lean_obj_tag(x_508) == 0)
{
lean_object* x_509; lean_object* x_510; 
x_509 = lean_ctor_get(x_508, 0);
lean_inc(x_509);
lean_dec_ref(x_508);
x_510 = l_Lean_Meta_Grind_Order_getExpr(x_502, x_463, x_464, x_465, x_466, x_467, x_468, x_469, x_470, x_471, x_472, x_473);
if (lean_obj_tag(x_510) == 0)
{
lean_object* x_511; lean_object* x_512; 
x_511 = lean_ctor_get(x_510, 0);
lean_inc(x_511);
lean_dec_ref(x_510);
x_512 = l_Lean_Meta_Grind_Order_getExpr(x_503, x_463, x_464, x_465, x_466, x_467, x_468, x_469, x_470, x_471, x_472, x_473);
if (lean_obj_tag(x_512) == 0)
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; uint8_t x_517; lean_object* x_518; 
x_513 = lean_ctor_get(x_512, 0);
lean_inc(x_513);
lean_dec_ref(x_512);
x_514 = l_Lean_mkApp3(x_509, x_511, x_513, x_462);
x_515 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5;
x_516 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_516, 0, x_515);
x_517 = lean_unbox(x_505);
lean_dec(x_505);
lean_ctor_set_uint8(x_516, sizeof(void*)*1, x_517);
x_518 = l_Lean_Meta_Grind_Order_addEdge(x_503, x_502, x_516, x_514, x_463, x_464, x_465, x_466, x_467, x_468, x_469, x_470, x_471, x_472, x_473);
return x_518;
}
else
{
lean_object* x_519; lean_object* x_520; lean_object* x_521; 
lean_dec(x_511);
lean_dec(x_509);
lean_dec(x_505);
lean_dec(x_503);
lean_dec(x_502);
lean_dec(x_473);
lean_dec_ref(x_472);
lean_dec(x_471);
lean_dec_ref(x_470);
lean_dec(x_469);
lean_dec_ref(x_468);
lean_dec(x_467);
lean_dec_ref(x_466);
lean_dec(x_465);
lean_dec(x_464);
lean_dec(x_463);
lean_dec_ref(x_462);
x_519 = lean_ctor_get(x_512, 0);
lean_inc(x_519);
if (lean_is_exclusive(x_512)) {
 lean_ctor_release(x_512, 0);
 x_520 = x_512;
} else {
 lean_dec_ref(x_512);
 x_520 = lean_box(0);
}
if (lean_is_scalar(x_520)) {
 x_521 = lean_alloc_ctor(1, 1, 0);
} else {
 x_521 = x_520;
}
lean_ctor_set(x_521, 0, x_519);
return x_521;
}
}
else
{
lean_object* x_522; lean_object* x_523; lean_object* x_524; 
lean_dec(x_509);
lean_dec(x_505);
lean_dec(x_503);
lean_dec(x_502);
lean_dec(x_473);
lean_dec_ref(x_472);
lean_dec(x_471);
lean_dec_ref(x_470);
lean_dec(x_469);
lean_dec_ref(x_468);
lean_dec(x_467);
lean_dec_ref(x_466);
lean_dec(x_465);
lean_dec(x_464);
lean_dec(x_463);
lean_dec_ref(x_462);
x_522 = lean_ctor_get(x_510, 0);
lean_inc(x_522);
if (lean_is_exclusive(x_510)) {
 lean_ctor_release(x_510, 0);
 x_523 = x_510;
} else {
 lean_dec_ref(x_510);
 x_523 = lean_box(0);
}
if (lean_is_scalar(x_523)) {
 x_524 = lean_alloc_ctor(1, 1, 0);
} else {
 x_524 = x_523;
}
lean_ctor_set(x_524, 0, x_522);
return x_524;
}
}
else
{
lean_object* x_525; lean_object* x_526; lean_object* x_527; 
lean_dec(x_505);
lean_dec(x_503);
lean_dec(x_502);
lean_dec(x_473);
lean_dec_ref(x_472);
lean_dec(x_471);
lean_dec_ref(x_470);
lean_dec(x_469);
lean_dec_ref(x_468);
lean_dec(x_467);
lean_dec_ref(x_466);
lean_dec(x_465);
lean_dec(x_464);
lean_dec(x_463);
lean_dec_ref(x_462);
x_525 = lean_ctor_get(x_508, 0);
lean_inc(x_525);
if (lean_is_exclusive(x_508)) {
 lean_ctor_release(x_508, 0);
 x_526 = x_508;
} else {
 lean_dec_ref(x_508);
 x_526 = lean_box(0);
}
if (lean_is_scalar(x_526)) {
 x_527 = lean_alloc_ctor(1, 1, 0);
} else {
 x_527 = x_526;
}
lean_ctor_set(x_527, 0, x_525);
return x_527;
}
}
else
{
lean_object* x_528; lean_object* x_529; 
lean_dec(x_505);
x_528 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__21));
x_529 = l_Lean_Meta_Grind_Order_mkLeLtLinearPrefix(x_528, x_463, x_464, x_465, x_466, x_467, x_468, x_469, x_470, x_471, x_472, x_473);
if (lean_obj_tag(x_529) == 0)
{
lean_object* x_530; lean_object* x_531; 
x_530 = lean_ctor_get(x_529, 0);
lean_inc(x_530);
lean_dec_ref(x_529);
x_531 = l_Lean_Meta_Grind_Order_getExpr(x_502, x_463, x_464, x_465, x_466, x_467, x_468, x_469, x_470, x_471, x_472, x_473);
if (lean_obj_tag(x_531) == 0)
{
lean_object* x_532; lean_object* x_533; 
x_532 = lean_ctor_get(x_531, 0);
lean_inc(x_532);
lean_dec_ref(x_531);
x_533 = l_Lean_Meta_Grind_Order_getExpr(x_503, x_463, x_464, x_465, x_466, x_467, x_468, x_469, x_470, x_471, x_472, x_473);
if (lean_obj_tag(x_533) == 0)
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; uint8_t x_538; lean_object* x_539; 
x_534 = lean_ctor_get(x_533, 0);
lean_inc(x_534);
lean_dec_ref(x_533);
x_535 = l_Lean_mkApp3(x_530, x_532, x_534, x_462);
x_536 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5;
x_537 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_537, 0, x_536);
x_538 = lean_unbox(x_356);
lean_dec(x_356);
lean_ctor_set_uint8(x_537, sizeof(void*)*1, x_538);
x_539 = l_Lean_Meta_Grind_Order_addEdge(x_503, x_502, x_537, x_535, x_463, x_464, x_465, x_466, x_467, x_468, x_469, x_470, x_471, x_472, x_473);
return x_539;
}
else
{
lean_object* x_540; lean_object* x_541; lean_object* x_542; 
lean_dec(x_532);
lean_dec(x_530);
lean_dec(x_503);
lean_dec(x_502);
lean_dec(x_473);
lean_dec_ref(x_472);
lean_dec(x_471);
lean_dec_ref(x_470);
lean_dec(x_469);
lean_dec_ref(x_468);
lean_dec(x_467);
lean_dec_ref(x_466);
lean_dec(x_465);
lean_dec(x_464);
lean_dec(x_463);
lean_dec_ref(x_462);
lean_dec(x_356);
x_540 = lean_ctor_get(x_533, 0);
lean_inc(x_540);
if (lean_is_exclusive(x_533)) {
 lean_ctor_release(x_533, 0);
 x_541 = x_533;
} else {
 lean_dec_ref(x_533);
 x_541 = lean_box(0);
}
if (lean_is_scalar(x_541)) {
 x_542 = lean_alloc_ctor(1, 1, 0);
} else {
 x_542 = x_541;
}
lean_ctor_set(x_542, 0, x_540);
return x_542;
}
}
else
{
lean_object* x_543; lean_object* x_544; lean_object* x_545; 
lean_dec(x_530);
lean_dec(x_503);
lean_dec(x_502);
lean_dec(x_473);
lean_dec_ref(x_472);
lean_dec(x_471);
lean_dec_ref(x_470);
lean_dec(x_469);
lean_dec_ref(x_468);
lean_dec(x_467);
lean_dec_ref(x_466);
lean_dec(x_465);
lean_dec(x_464);
lean_dec(x_463);
lean_dec_ref(x_462);
lean_dec(x_356);
x_543 = lean_ctor_get(x_531, 0);
lean_inc(x_543);
if (lean_is_exclusive(x_531)) {
 lean_ctor_release(x_531, 0);
 x_544 = x_531;
} else {
 lean_dec_ref(x_531);
 x_544 = lean_box(0);
}
if (lean_is_scalar(x_544)) {
 x_545 = lean_alloc_ctor(1, 1, 0);
} else {
 x_545 = x_544;
}
lean_ctor_set(x_545, 0, x_543);
return x_545;
}
}
else
{
lean_object* x_546; lean_object* x_547; lean_object* x_548; 
lean_dec(x_503);
lean_dec(x_502);
lean_dec(x_473);
lean_dec_ref(x_472);
lean_dec(x_471);
lean_dec_ref(x_470);
lean_dec(x_469);
lean_dec_ref(x_468);
lean_dec(x_467);
lean_dec_ref(x_466);
lean_dec(x_465);
lean_dec(x_464);
lean_dec(x_463);
lean_dec_ref(x_462);
lean_dec(x_356);
x_546 = lean_ctor_get(x_529, 0);
lean_inc(x_546);
if (lean_is_exclusive(x_529)) {
 lean_ctor_release(x_529, 0);
 x_547 = x_529;
} else {
 lean_dec_ref(x_529);
 x_547 = lean_box(0);
}
if (lean_is_scalar(x_547)) {
 x_548 = lean_alloc_ctor(1, 1, 0);
} else {
 x_548 = x_547;
}
lean_ctor_set(x_548, 0, x_546);
return x_548;
}
}
}
else
{
lean_object* x_549; lean_object* x_550; lean_object* x_551; 
lean_dec(x_503);
lean_dec(x_502);
lean_dec(x_473);
lean_dec_ref(x_472);
lean_dec(x_471);
lean_dec_ref(x_470);
lean_dec(x_469);
lean_dec_ref(x_468);
lean_dec(x_467);
lean_dec_ref(x_466);
lean_dec(x_465);
lean_dec(x_464);
lean_dec(x_463);
lean_dec_ref(x_462);
lean_dec(x_356);
x_549 = lean_ctor_get(x_504, 0);
lean_inc(x_549);
if (lean_is_exclusive(x_504)) {
 lean_ctor_release(x_504, 0);
 x_550 = x_504;
} else {
 lean_dec_ref(x_504);
 x_550 = lean_box(0);
}
if (lean_is_scalar(x_550)) {
 x_551 = lean_alloc_ctor(1, 1, 0);
} else {
 x_551 = x_550;
}
lean_ctor_set(x_551, 0, x_549);
return x_551;
}
}
}
else
{
uint8_t x_552; 
lean_dec(x_476);
x_552 = lean_ctor_get_uint8(x_1, sizeof(void*)*5);
if (x_552 == 1)
{
lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; 
x_553 = lean_ctor_get(x_1, 0);
lean_inc(x_553);
x_554 = lean_ctor_get(x_1, 1);
lean_inc(x_554);
x_555 = lean_ctor_get(x_1, 2);
lean_inc(x_555);
lean_dec_ref(x_1);
x_556 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__23));
x_417 = x_466;
x_418 = x_552;
x_419 = x_465;
x_420 = x_467;
x_421 = x_468;
x_422 = x_473;
x_423 = lean_box(0);
x_424 = x_470;
x_425 = x_469;
x_426 = x_554;
x_427 = x_553;
x_428 = x_464;
x_429 = x_471;
x_430 = x_555;
x_431 = x_472;
x_432 = x_463;
x_433 = x_462;
x_434 = x_556;
goto block_461;
}
else
{
lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; 
x_557 = lean_ctor_get(x_1, 0);
lean_inc(x_557);
x_558 = lean_ctor_get(x_1, 1);
lean_inc(x_558);
x_559 = lean_ctor_get(x_1, 2);
lean_inc(x_559);
lean_dec_ref(x_1);
x_560 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__25));
x_417 = x_466;
x_418 = x_552;
x_419 = x_465;
x_420 = x_467;
x_421 = x_468;
x_422 = x_473;
x_423 = lean_box(0);
x_424 = x_470;
x_425 = x_469;
x_426 = x_558;
x_427 = x_557;
x_428 = x_464;
x_429 = x_471;
x_430 = x_559;
x_431 = x_472;
x_432 = x_463;
x_433 = x_462;
x_434 = x_560;
goto block_461;
}
}
}
else
{
lean_object* x_561; lean_object* x_562; lean_object* x_563; 
lean_dec(x_473);
lean_dec_ref(x_472);
lean_dec(x_471);
lean_dec_ref(x_470);
lean_dec(x_469);
lean_dec_ref(x_468);
lean_dec(x_467);
lean_dec_ref(x_466);
lean_dec(x_465);
lean_dec(x_464);
lean_dec(x_463);
lean_dec_ref(x_462);
lean_dec(x_356);
lean_dec_ref(x_1);
x_561 = lean_ctor_get(x_475, 0);
lean_inc(x_561);
if (lean_is_exclusive(x_475)) {
 lean_ctor_release(x_475, 0);
 x_562 = x_475;
} else {
 lean_dec_ref(x_475);
 x_562 = lean_box(0);
}
if (lean_is_scalar(x_562)) {
 x_563 = lean_alloc_ctor(1, 1, 0);
} else {
 x_563 = x_562;
}
lean_ctor_set(x_563, 0, x_561);
return x_563;
}
}
block_584:
{
lean_object* x_577; 
x_577 = lean_ctor_get(x_1, 4);
if (lean_obj_tag(x_577) == 1)
{
lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; 
x_578 = lean_ctor_get(x_1, 3);
x_579 = lean_ctor_get(x_577, 0);
x_580 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__28;
lean_inc_ref(x_2);
x_581 = l_Lean_Meta_mkOfEqFalseCore(x_2, x_3);
lean_inc(x_579);
lean_inc_ref(x_578);
x_582 = l_Lean_mkApp4(x_580, x_2, x_578, x_579, x_581);
x_462 = x_582;
x_463 = x_565;
x_464 = x_566;
x_465 = x_567;
x_466 = x_568;
x_467 = x_569;
x_468 = x_570;
x_469 = x_571;
x_470 = x_572;
x_471 = x_573;
x_472 = x_574;
x_473 = x_575;
x_474 = lean_box(0);
goto block_564;
}
else
{
lean_object* x_583; 
x_583 = l_Lean_Meta_mkOfEqFalseCore(x_2, x_3);
x_462 = x_583;
x_463 = x_565;
x_464 = x_566;
x_465 = x_567;
x_466 = x_568;
x_467 = x_569;
x_468 = x_570;
x_469 = x_571;
x_470 = x_572;
x_471 = x_573;
x_472 = x_574;
x_473 = x_575;
x_474 = lean_box(0);
goto block_564;
}
}
}
}
else
{
uint8_t x_600; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_600 = !lean_is_exclusive(x_111);
if (x_600 == 0)
{
return x_111;
}
else
{
lean_object* x_601; lean_object* x_602; 
x_601 = lean_ctor_get(x_111, 0);
lean_inc(x_601);
lean_dec(x_111);
x_602 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_602, 0, x_601);
return x_602;
}
}
block_35:
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_33, 0, x_19);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_20);
x_34 = l_Lean_Meta_Grind_Order_addEdge(x_16, x_17, x_33, x_18, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28, x_29, x_30, x_31);
return x_34;
}
block_60:
{
lean_object* x_58; uint8_t x_59; 
x_58 = l_Lean_mkApp6(x_50, x_43, x_53, x_41, x_57, x_39, x_49);
x_59 = 0;
x_16 = x_46;
x_17 = x_47;
x_18 = x_58;
x_19 = x_51;
x_20 = x_59;
x_21 = x_55;
x_22 = x_48;
x_23 = x_37;
x_24 = x_36;
x_25 = x_38;
x_26 = x_42;
x_27 = x_45;
x_28 = x_44;
x_29 = x_52;
x_30 = x_54;
x_31 = x_40;
x_32 = lean_box(0);
goto block_35;
}
block_110:
{
lean_object* x_80; 
x_80 = l_Lean_Meta_Grind_Order_isInt(x_78, x_72, x_62, x_61, x_63, x_66, x_69, x_68, x_76, x_77, x_67);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; uint8_t x_82; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
lean_dec_ref(x_80);
x_82 = lean_unbox(x_81);
lean_dec(x_81);
if (x_82 == 0)
{
lean_dec_ref(x_65);
lean_dec_ref(x_64);
x_16 = x_70;
x_17 = x_71;
x_18 = x_74;
x_19 = x_73;
x_20 = x_79;
x_21 = x_78;
x_22 = x_72;
x_23 = x_62;
x_24 = x_61;
x_25 = x_63;
x_26 = x_66;
x_27 = x_69;
x_28 = x_68;
x_29 = x_76;
x_30 = x_77;
x_31 = x_67;
x_32 = lean_box(0);
goto block_35;
}
else
{
if (x_79 == 0)
{
lean_dec_ref(x_65);
lean_dec_ref(x_64);
x_16 = x_70;
x_17 = x_71;
x_18 = x_74;
x_19 = x_73;
x_20 = x_79;
x_21 = x_78;
x_22 = x_72;
x_23 = x_62;
x_24 = x_61;
x_25 = x_63;
x_26 = x_66;
x_27 = x_69;
x_28 = x_68;
x_29 = x_76;
x_30 = x_77;
x_31 = x_67;
x_32 = lean_box(0);
goto block_35;
}
else
{
lean_object* x_83; 
x_83 = l_Lean_Meta_Grind_Order_getExpr(x_70, x_78, x_72, x_62, x_61, x_63, x_66, x_69, x_68, x_76, x_77, x_67);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
lean_dec_ref(x_83);
x_85 = l_Lean_Meta_Grind_Order_getExpr(x_71, x_78, x_72, x_62, x_61, x_63, x_66, x_69, x_68, x_76, x_77, x_67);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
lean_dec_ref(x_85);
x_87 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__2;
x_88 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__3;
x_89 = lean_int_sub(x_73, x_88);
lean_dec(x_73);
x_90 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5;
x_91 = lean_int_dec_le(x_90, x_89);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_92 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__9;
x_93 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__12;
x_94 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__15;
x_95 = lean_int_neg(x_89);
x_96 = l_Int_toNat(x_95);
lean_dec(x_95);
x_97 = l_Lean_instToExprInt_mkNat(x_96);
x_98 = l_Lean_mkApp3(x_92, x_93, x_94, x_97);
x_36 = x_61;
x_37 = x_62;
x_38 = x_63;
x_39 = x_64;
x_40 = x_67;
x_41 = x_65;
x_42 = x_66;
x_43 = x_84;
x_44 = x_68;
x_45 = x_69;
x_46 = x_70;
x_47 = x_71;
x_48 = x_72;
x_49 = x_74;
x_50 = x_87;
x_51 = x_89;
x_52 = x_76;
x_53 = x_86;
x_54 = x_77;
x_55 = x_78;
x_56 = lean_box(0);
x_57 = x_98;
goto block_60;
}
else
{
lean_object* x_99; lean_object* x_100; 
x_99 = l_Int_toNat(x_89);
x_100 = l_Lean_instToExprInt_mkNat(x_99);
x_36 = x_61;
x_37 = x_62;
x_38 = x_63;
x_39 = x_64;
x_40 = x_67;
x_41 = x_65;
x_42 = x_66;
x_43 = x_84;
x_44 = x_68;
x_45 = x_69;
x_46 = x_70;
x_47 = x_71;
x_48 = x_72;
x_49 = x_74;
x_50 = x_87;
x_51 = x_89;
x_52 = x_76;
x_53 = x_86;
x_54 = x_77;
x_55 = x_78;
x_56 = lean_box(0);
x_57 = x_100;
goto block_60;
}
}
else
{
uint8_t x_101; 
lean_dec(x_84);
lean_dec(x_78);
lean_dec_ref(x_77);
lean_dec(x_76);
lean_dec_ref(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_69);
lean_dec_ref(x_68);
lean_dec(x_67);
lean_dec_ref(x_66);
lean_dec_ref(x_65);
lean_dec_ref(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec_ref(x_61);
x_101 = !lean_is_exclusive(x_85);
if (x_101 == 0)
{
return x_85;
}
else
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_85, 0);
lean_inc(x_102);
lean_dec(x_85);
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_102);
return x_103;
}
}
}
else
{
uint8_t x_104; 
lean_dec(x_78);
lean_dec_ref(x_77);
lean_dec(x_76);
lean_dec_ref(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_69);
lean_dec_ref(x_68);
lean_dec(x_67);
lean_dec_ref(x_66);
lean_dec_ref(x_65);
lean_dec_ref(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec_ref(x_61);
x_104 = !lean_is_exclusive(x_83);
if (x_104 == 0)
{
return x_83;
}
else
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_83, 0);
lean_inc(x_105);
lean_dec(x_83);
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_105);
return x_106;
}
}
}
}
}
else
{
uint8_t x_107; 
lean_dec(x_78);
lean_dec_ref(x_77);
lean_dec(x_76);
lean_dec_ref(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_69);
lean_dec_ref(x_68);
lean_dec(x_67);
lean_dec_ref(x_66);
lean_dec_ref(x_65);
lean_dec_ref(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec_ref(x_61);
x_107 = !lean_is_exclusive(x_80);
if (x_107 == 0)
{
return x_80;
}
else
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_ctor_get(x_80, 0);
lean_inc(x_108);
lean_dec(x_80);
x_109 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_109, 0, x_108);
return x_109;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_Order_get_x27___redArg(x_2, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 2);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(x_8, x_1);
lean_ctor_set(x_5, 0, x_9);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_ctor_get(x_10, 2);
lean_inc_ref(x_11);
lean_dec(x_10);
x_12 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(x_11, x_1);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
return x_5;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_5, 0);
lean_inc(x_15);
lean_dec(x_5);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___redArg(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___redArg(x_1, x_2, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_13;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__1));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__4));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___redArg(x_2, x_4, x_12);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
if (lean_obj_tag(x_17) == 1)
{
lean_object* x_18; lean_object* x_19; 
lean_free_object(x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = l_Lean_Meta_Grind_Order_getCnstr_x3f(x_2, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
if (lean_obj_tag(x_21) == 1)
{
lean_object* x_22; lean_object* x_23; 
lean_free_object(x_19);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
lean_inc_ref(x_1);
x_23 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_4, x_8, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec_ref(x_23);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_inc_ref(x_1);
x_26 = l_Lean_Meta_Grind_isEqFalse___redArg(x_1, x_4, x_8, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_22);
lean_dec(x_18);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_30 = lean_box(0);
lean_ctor_set(x_26, 0, x_30);
return x_26;
}
else
{
lean_object* x_31; 
lean_free_object(x_26);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_1);
x_31 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_31) == 0)
{
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec_ref(x_31);
x_33 = lean_ctor_get(x_3, 0);
lean_inc(x_33);
lean_dec_ref(x_3);
x_34 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__2;
lean_inc_ref(x_2);
x_35 = l_Lean_mkApp4(x_34, x_1, x_2, x_33, x_32);
x_36 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse(x_22, x_2, x_35, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_37 = lean_ctor_get(x_31, 0);
lean_inc(x_37);
lean_dec_ref(x_31);
x_38 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse(x_22, x_2, x_37, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_22);
lean_dec(x_18);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_39 = !lean_is_exclusive(x_31);
if (x_39 == 0)
{
return x_31;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_31, 0);
lean_inc(x_40);
lean_dec(x_31);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
}
}
else
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_26, 0);
lean_inc(x_42);
lean_dec(x_26);
x_43 = lean_unbox(x_42);
lean_dec(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_22);
lean_dec(x_18);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
else
{
lean_object* x_46; 
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_1);
x_46 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_46) == 0)
{
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec_ref(x_46);
x_48 = lean_ctor_get(x_3, 0);
lean_inc(x_48);
lean_dec_ref(x_3);
x_49 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__2;
lean_inc_ref(x_2);
x_50 = l_Lean_mkApp4(x_49, x_1, x_2, x_48, x_47);
x_51 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse(x_22, x_2, x_50, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_52 = lean_ctor_get(x_46, 0);
lean_inc(x_52);
lean_dec_ref(x_46);
x_53 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse(x_22, x_2, x_52, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_22);
lean_dec(x_18);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_54 = lean_ctor_get(x_46, 0);
lean_inc(x_54);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 x_55 = x_46;
} else {
 lean_dec_ref(x_46);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(1, 1, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_54);
return x_56;
}
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_22);
lean_dec(x_18);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_57 = !lean_is_exclusive(x_26);
if (x_57 == 0)
{
return x_26;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_26, 0);
lean_inc(x_58);
lean_dec(x_26);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
return x_59;
}
}
}
else
{
lean_object* x_60; 
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_1);
x_60 = l_Lean_Meta_Grind_mkEqTrueProof(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_60) == 0)
{
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
lean_dec_ref(x_60);
x_62 = lean_ctor_get(x_3, 0);
lean_inc(x_62);
lean_dec_ref(x_3);
x_63 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__5;
lean_inc_ref(x_2);
x_64 = l_Lean_mkApp4(x_63, x_1, x_2, x_62, x_61);
x_65 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue(x_22, x_2, x_64, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_66 = lean_ctor_get(x_60, 0);
lean_inc(x_66);
lean_dec_ref(x_60);
x_67 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue(x_22, x_2, x_66, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_67;
}
}
else
{
uint8_t x_68; 
lean_dec(x_22);
lean_dec(x_18);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_68 = !lean_is_exclusive(x_60);
if (x_68 == 0)
{
return x_60;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_60, 0);
lean_inc(x_69);
lean_dec(x_60);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_22);
lean_dec(x_18);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_71 = !lean_is_exclusive(x_23);
if (x_71 == 0)
{
return x_23;
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_23, 0);
lean_inc(x_72);
lean_dec(x_23);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
return x_73;
}
}
}
else
{
lean_object* x_74; 
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_74 = lean_box(0);
lean_ctor_set(x_19, 0, x_74);
return x_19;
}
}
else
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_19, 0);
lean_inc(x_75);
lean_dec(x_19);
if (lean_obj_tag(x_75) == 1)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
lean_dec_ref(x_75);
lean_inc_ref(x_1);
x_77 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_4, x_8, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; uint8_t x_79; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
lean_dec_ref(x_77);
x_79 = lean_unbox(x_78);
lean_dec(x_78);
if (x_79 == 0)
{
lean_object* x_80; 
lean_inc_ref(x_1);
x_80 = l_Lean_Meta_Grind_isEqFalse___redArg(x_1, x_4, x_8, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 x_82 = x_80;
} else {
 lean_dec_ref(x_80);
 x_82 = lean_box(0);
}
x_83 = lean_unbox(x_81);
lean_dec(x_81);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_76);
lean_dec(x_18);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_84 = lean_box(0);
if (lean_is_scalar(x_82)) {
 x_85 = lean_alloc_ctor(0, 1, 0);
} else {
 x_85 = x_82;
}
lean_ctor_set(x_85, 0, x_84);
return x_85;
}
else
{
lean_object* x_86; 
lean_dec(x_82);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_1);
x_86 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_86) == 0)
{
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
lean_dec_ref(x_86);
x_88 = lean_ctor_get(x_3, 0);
lean_inc(x_88);
lean_dec_ref(x_3);
x_89 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__2;
lean_inc_ref(x_2);
x_90 = l_Lean_mkApp4(x_89, x_1, x_2, x_88, x_87);
x_91 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse(x_76, x_2, x_90, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_92 = lean_ctor_get(x_86, 0);
lean_inc(x_92);
lean_dec_ref(x_86);
x_93 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse(x_76, x_2, x_92, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_93;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_76);
lean_dec(x_18);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_94 = lean_ctor_get(x_86, 0);
lean_inc(x_94);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 x_95 = x_86;
} else {
 lean_dec_ref(x_86);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(1, 1, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_94);
return x_96;
}
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_76);
lean_dec(x_18);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_97 = lean_ctor_get(x_80, 0);
lean_inc(x_97);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 x_98 = x_80;
} else {
 lean_dec_ref(x_80);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(1, 1, 0);
} else {
 x_99 = x_98;
}
lean_ctor_set(x_99, 0, x_97);
return x_99;
}
}
else
{
lean_object* x_100; 
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_1);
x_100 = l_Lean_Meta_Grind_mkEqTrueProof(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_100) == 0)
{
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
lean_dec_ref(x_100);
x_102 = lean_ctor_get(x_3, 0);
lean_inc(x_102);
lean_dec_ref(x_3);
x_103 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__5;
lean_inc_ref(x_2);
x_104 = l_Lean_mkApp4(x_103, x_1, x_2, x_102, x_101);
x_105 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue(x_76, x_2, x_104, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_105;
}
else
{
lean_object* x_106; lean_object* x_107; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_106 = lean_ctor_get(x_100, 0);
lean_inc(x_106);
lean_dec_ref(x_100);
x_107 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue(x_76, x_2, x_106, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_107;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_76);
lean_dec(x_18);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_108 = lean_ctor_get(x_100, 0);
lean_inc(x_108);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 x_109 = x_100;
} else {
 lean_dec_ref(x_100);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(1, 1, 0);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_108);
return x_110;
}
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_76);
lean_dec(x_18);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_111 = lean_ctor_get(x_77, 0);
lean_inc(x_111);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 x_112 = x_77;
} else {
 lean_dec_ref(x_77);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(1, 1, 0);
} else {
 x_113 = x_112;
}
lean_ctor_set(x_113, 0, x_111);
return x_113;
}
}
else
{
lean_object* x_114; lean_object* x_115; 
lean_dec(x_75);
lean_dec(x_18);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_114 = lean_box(0);
x_115 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_115, 0, x_114);
return x_115;
}
}
}
else
{
uint8_t x_116; 
lean_dec(x_18);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_116 = !lean_is_exclusive(x_19);
if (x_116 == 0)
{
return x_19;
}
else
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_ctor_get(x_19, 0);
lean_inc(x_117);
lean_dec(x_19);
x_118 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_118, 0, x_117);
return x_118;
}
}
}
else
{
lean_object* x_119; 
lean_dec(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_119 = lean_box(0);
lean_ctor_set(x_15, 0, x_119);
return x_15;
}
}
else
{
lean_object* x_120; 
x_120 = lean_ctor_get(x_15, 0);
lean_inc(x_120);
lean_dec(x_15);
if (lean_obj_tag(x_120) == 1)
{
lean_object* x_121; lean_object* x_122; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
lean_dec_ref(x_120);
x_122 = l_Lean_Meta_Grind_Order_getCnstr_x3f(x_2, x_121, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 x_124 = x_122;
} else {
 lean_dec_ref(x_122);
 x_124 = lean_box(0);
}
if (lean_obj_tag(x_123) == 1)
{
lean_object* x_125; lean_object* x_126; 
lean_dec(x_124);
x_125 = lean_ctor_get(x_123, 0);
lean_inc(x_125);
lean_dec_ref(x_123);
lean_inc_ref(x_1);
x_126 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_4, x_8, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; uint8_t x_128; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
lean_dec_ref(x_126);
x_128 = lean_unbox(x_127);
lean_dec(x_127);
if (x_128 == 0)
{
lean_object* x_129; 
lean_inc_ref(x_1);
x_129 = l_Lean_Meta_Grind_isEqFalse___redArg(x_1, x_4, x_8, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 x_131 = x_129;
} else {
 lean_dec_ref(x_129);
 x_131 = lean_box(0);
}
x_132 = lean_unbox(x_130);
lean_dec(x_130);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; 
lean_dec(x_125);
lean_dec(x_121);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_133 = lean_box(0);
if (lean_is_scalar(x_131)) {
 x_134 = lean_alloc_ctor(0, 1, 0);
} else {
 x_134 = x_131;
}
lean_ctor_set(x_134, 0, x_133);
return x_134;
}
else
{
lean_object* x_135; 
lean_dec(x_131);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_1);
x_135 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_135) == 0)
{
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
lean_dec_ref(x_135);
x_137 = lean_ctor_get(x_3, 0);
lean_inc(x_137);
lean_dec_ref(x_3);
x_138 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__2;
lean_inc_ref(x_2);
x_139 = l_Lean_mkApp4(x_138, x_1, x_2, x_137, x_136);
x_140 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse(x_125, x_2, x_139, x_121, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_140;
}
else
{
lean_object* x_141; lean_object* x_142; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_141 = lean_ctor_get(x_135, 0);
lean_inc(x_141);
lean_dec_ref(x_135);
x_142 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse(x_125, x_2, x_141, x_121, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_142;
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_125);
lean_dec(x_121);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_143 = lean_ctor_get(x_135, 0);
lean_inc(x_143);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 x_144 = x_135;
} else {
 lean_dec_ref(x_135);
 x_144 = lean_box(0);
}
if (lean_is_scalar(x_144)) {
 x_145 = lean_alloc_ctor(1, 1, 0);
} else {
 x_145 = x_144;
}
lean_ctor_set(x_145, 0, x_143);
return x_145;
}
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_125);
lean_dec(x_121);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_146 = lean_ctor_get(x_129, 0);
lean_inc(x_146);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 x_147 = x_129;
} else {
 lean_dec_ref(x_129);
 x_147 = lean_box(0);
}
if (lean_is_scalar(x_147)) {
 x_148 = lean_alloc_ctor(1, 1, 0);
} else {
 x_148 = x_147;
}
lean_ctor_set(x_148, 0, x_146);
return x_148;
}
}
else
{
lean_object* x_149; 
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_1);
x_149 = l_Lean_Meta_Grind_mkEqTrueProof(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_149) == 0)
{
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
lean_dec_ref(x_149);
x_151 = lean_ctor_get(x_3, 0);
lean_inc(x_151);
lean_dec_ref(x_3);
x_152 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__5;
lean_inc_ref(x_2);
x_153 = l_Lean_mkApp4(x_152, x_1, x_2, x_151, x_150);
x_154 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue(x_125, x_2, x_153, x_121, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_154;
}
else
{
lean_object* x_155; lean_object* x_156; 
lean_dec(x_3);
lean_dec_ref(x_1);
x_155 = lean_ctor_get(x_149, 0);
lean_inc(x_155);
lean_dec_ref(x_149);
x_156 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue(x_125, x_2, x_155, x_121, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_156;
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_125);
lean_dec(x_121);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_157 = lean_ctor_get(x_149, 0);
lean_inc(x_157);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 x_158 = x_149;
} else {
 lean_dec_ref(x_149);
 x_158 = lean_box(0);
}
if (lean_is_scalar(x_158)) {
 x_159 = lean_alloc_ctor(1, 1, 0);
} else {
 x_159 = x_158;
}
lean_ctor_set(x_159, 0, x_157);
return x_159;
}
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_125);
lean_dec(x_121);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_160 = lean_ctor_get(x_126, 0);
lean_inc(x_160);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 x_161 = x_126;
} else {
 lean_dec_ref(x_126);
 x_161 = lean_box(0);
}
if (lean_is_scalar(x_161)) {
 x_162 = lean_alloc_ctor(1, 1, 0);
} else {
 x_162 = x_161;
}
lean_ctor_set(x_162, 0, x_160);
return x_162;
}
}
else
{
lean_object* x_163; lean_object* x_164; 
lean_dec(x_123);
lean_dec(x_121);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_163 = lean_box(0);
if (lean_is_scalar(x_124)) {
 x_164 = lean_alloc_ctor(0, 1, 0);
} else {
 x_164 = x_124;
}
lean_ctor_set(x_164, 0, x_163);
return x_164;
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_dec(x_121);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_165 = lean_ctor_get(x_122, 0);
lean_inc(x_165);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 x_166 = x_122;
} else {
 lean_dec_ref(x_122);
 x_166 = lean_box(0);
}
if (lean_is_scalar(x_166)) {
 x_167 = lean_alloc_ctor(1, 1, 0);
} else {
 x_167 = x_166;
}
lean_ctor_set(x_167, 0, x_165);
return x_167;
}
}
else
{
lean_object* x_168; lean_object* x_169; 
lean_dec(x_120);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_168 = lean_box(0);
x_169 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_169, 0, x_168);
return x_169;
}
}
}
else
{
uint8_t x_170; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_170 = !lean_is_exclusive(x_15);
if (x_170 == 0)
{
return x_15;
}
else
{
lean_object* x_171; lean_object* x_172; 
x_171 = lean_ctor_get(x_15, 0);
lean_inc(x_171);
lean_dec(x_15);
x_172 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_172, 0, x_171);
return x_172;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Order_get_x27___redArg(x_2, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = lean_ctor_get(x_14, 3);
lean_inc_ref(x_15);
lean_dec(x_14);
x_16 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(x_15, x_1);
if (lean_obj_tag(x_16) == 1)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_20);
x_21 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go(x_1, x_19, x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_16, 0);
lean_inc(x_22);
lean_dec(x_16);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go(x_1, x_23, x_25, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_16);
x_27 = lean_box(0);
lean_inc_ref(x_1);
x_28 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go(x_1, x_1, x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_29 = !lean_is_exclusive(x_13);
if (x_29 == 0)
{
return x_13;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_13, 0);
lean_inc(x_30);
lean_dec(x_13);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_8_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_8_));
x_3 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1___closed__3_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_8_));
x_4 = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_8____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_8_();
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_1204040634____hygCtx___hyg_8_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_8_));
x_3 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_1204040634____hygCtx___hyg_8_));
x_4 = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_1204040634____hygCtx___hyg_8____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_1204040634____hygCtx___hyg_8_();
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_Order_get_x27___redArg(x_2, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 3);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(x_8, x_1);
lean_ctor_set(x_5, 0, x_9);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_ctor_get(x_10, 3);
lean_inc_ref(x_11);
lean_dec(x_10);
x_12 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0___redArg(x_11, x_1);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
return x_5;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_5, 0);
lean_inc(x_15);
lean_dec(x_5);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f___redArg(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f___redArg(x_1, x_2, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_13;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__8() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__9));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_80; 
x_80 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___redArg(x_1, x_4, x_12);
if (lean_obj_tag(x_80) == 0)
{
uint8_t x_81; 
x_81 = !lean_is_exclusive(x_80);
if (x_81 == 0)
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_80, 0);
if (lean_obj_tag(x_82) == 1)
{
lean_object* x_83; lean_object* x_84; 
lean_free_object(x_80);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
lean_dec_ref(x_82);
x_84 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___redArg(x_2, x_4, x_12);
if (lean_obj_tag(x_84) == 0)
{
uint8_t x_85; 
x_85 = !lean_is_exclusive(x_84);
if (x_85 == 0)
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_84, 0);
if (lean_obj_tag(x_86) == 1)
{
lean_object* x_87; uint8_t x_88; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
lean_dec_ref(x_86);
x_88 = lean_nat_dec_eq(x_83, x_87);
lean_dec(x_87);
if (x_88 == 0)
{
lean_object* x_89; 
lean_dec(x_83);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_89 = lean_box(0);
lean_ctor_set(x_84, 0, x_89);
return x_84;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
lean_free_object(x_84);
x_90 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__4));
x_91 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(x_90, x_12);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
lean_dec_ref(x_91);
x_93 = lean_unbox(x_92);
lean_dec(x_92);
if (x_93 == 0)
{
x_15 = x_83;
x_16 = x_4;
x_17 = x_5;
x_18 = x_6;
x_19 = x_7;
x_20 = x_8;
x_21 = x_9;
x_22 = x_10;
x_23 = x_11;
x_24 = x_12;
x_25 = x_13;
x_26 = lean_box(0);
goto block_79;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_inc_ref(x_1);
x_94 = l_Lean_MessageData_ofExpr(x_1);
x_95 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__10;
x_96 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
lean_inc_ref(x_2);
x_97 = l_Lean_MessageData_ofExpr(x_2);
x_98 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
x_99 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___redArg(x_90, x_98, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_99) == 0)
{
lean_dec_ref(x_99);
x_15 = x_83;
x_16 = x_4;
x_17 = x_5;
x_18 = x_6;
x_19 = x_7;
x_20 = x_8;
x_21 = x_9;
x_22 = x_10;
x_23 = x_11;
x_24 = x_12;
x_25 = x_13;
x_26 = lean_box(0);
goto block_79;
}
else
{
lean_dec(x_83);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_99;
}
}
}
}
else
{
lean_object* x_100; 
lean_dec(x_86);
lean_dec(x_83);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_100 = lean_box(0);
lean_ctor_set(x_84, 0, x_100);
return x_84;
}
}
else
{
lean_object* x_101; 
x_101 = lean_ctor_get(x_84, 0);
lean_inc(x_101);
lean_dec(x_84);
if (lean_obj_tag(x_101) == 1)
{
lean_object* x_102; uint8_t x_103; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
lean_dec_ref(x_101);
x_103 = lean_nat_dec_eq(x_83, x_102);
lean_dec(x_102);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; 
lean_dec(x_83);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_104 = lean_box(0);
x_105 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_105, 0, x_104);
return x_105;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_106 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__4));
x_107 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(x_106, x_12);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
lean_dec_ref(x_107);
x_109 = lean_unbox(x_108);
lean_dec(x_108);
if (x_109 == 0)
{
x_15 = x_83;
x_16 = x_4;
x_17 = x_5;
x_18 = x_6;
x_19 = x_7;
x_20 = x_8;
x_21 = x_9;
x_22 = x_10;
x_23 = x_11;
x_24 = x_12;
x_25 = x_13;
x_26 = lean_box(0);
goto block_79;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_inc_ref(x_1);
x_110 = l_Lean_MessageData_ofExpr(x_1);
x_111 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__10;
x_112 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
lean_inc_ref(x_2);
x_113 = l_Lean_MessageData_ofExpr(x_2);
x_114 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
x_115 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___redArg(x_106, x_114, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_115) == 0)
{
lean_dec_ref(x_115);
x_15 = x_83;
x_16 = x_4;
x_17 = x_5;
x_18 = x_6;
x_19 = x_7;
x_20 = x_8;
x_21 = x_9;
x_22 = x_10;
x_23 = x_11;
x_24 = x_12;
x_25 = x_13;
x_26 = lean_box(0);
goto block_79;
}
else
{
lean_dec(x_83);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_115;
}
}
}
}
else
{
lean_object* x_116; lean_object* x_117; 
lean_dec(x_101);
lean_dec(x_83);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_116 = lean_box(0);
x_117 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_117, 0, x_116);
return x_117;
}
}
}
else
{
uint8_t x_118; 
lean_dec(x_83);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_118 = !lean_is_exclusive(x_84);
if (x_118 == 0)
{
return x_84;
}
else
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_84, 0);
lean_inc(x_119);
lean_dec(x_84);
x_120 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_120, 0, x_119);
return x_120;
}
}
}
else
{
lean_object* x_121; 
lean_dec(x_82);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_121 = lean_box(0);
lean_ctor_set(x_80, 0, x_121);
return x_80;
}
}
else
{
lean_object* x_122; 
x_122 = lean_ctor_get(x_80, 0);
lean_inc(x_122);
lean_dec(x_80);
if (lean_obj_tag(x_122) == 1)
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
lean_dec_ref(x_122);
x_124 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_getStructIdOf_x3f___redArg(x_2, x_4, x_12);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 x_126 = x_124;
} else {
 lean_dec_ref(x_124);
 x_126 = lean_box(0);
}
if (lean_obj_tag(x_125) == 1)
{
lean_object* x_127; uint8_t x_128; 
x_127 = lean_ctor_get(x_125, 0);
lean_inc(x_127);
lean_dec_ref(x_125);
x_128 = lean_nat_dec_eq(x_123, x_127);
lean_dec(x_127);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; 
lean_dec(x_123);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_129 = lean_box(0);
if (lean_is_scalar(x_126)) {
 x_130 = lean_alloc_ctor(0, 1, 0);
} else {
 x_130 = x_126;
}
lean_ctor_set(x_130, 0, x_129);
return x_130;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; 
lean_dec(x_126);
x_131 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__4));
x_132 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__0___redArg(x_131, x_12);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
lean_dec_ref(x_132);
x_134 = lean_unbox(x_133);
lean_dec(x_133);
if (x_134 == 0)
{
x_15 = x_123;
x_16 = x_4;
x_17 = x_5;
x_18 = x_6;
x_19 = x_7;
x_20 = x_8;
x_21 = x_9;
x_22 = x_10;
x_23 = x_11;
x_24 = x_12;
x_25 = x_13;
x_26 = lean_box(0);
goto block_79;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_inc_ref(x_1);
x_135 = l_Lean_MessageData_ofExpr(x_1);
x_136 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__10;
x_137 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
lean_inc_ref(x_2);
x_138 = l_Lean_MessageData_ofExpr(x_2);
x_139 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
x_140 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___redArg(x_131, x_139, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_140) == 0)
{
lean_dec_ref(x_140);
x_15 = x_123;
x_16 = x_4;
x_17 = x_5;
x_18 = x_6;
x_19 = x_7;
x_20 = x_8;
x_21 = x_9;
x_22 = x_10;
x_23 = x_11;
x_24 = x_12;
x_25 = x_13;
x_26 = lean_box(0);
goto block_79;
}
else
{
lean_dec(x_123);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_140;
}
}
}
}
else
{
lean_object* x_141; lean_object* x_142; 
lean_dec(x_125);
lean_dec(x_123);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_141 = lean_box(0);
if (lean_is_scalar(x_126)) {
 x_142 = lean_alloc_ctor(0, 1, 0);
} else {
 x_142 = x_126;
}
lean_ctor_set(x_142, 0, x_141);
return x_142;
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_123);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_143 = lean_ctor_get(x_124, 0);
lean_inc(x_143);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 x_144 = x_124;
} else {
 lean_dec_ref(x_124);
 x_144 = lean_box(0);
}
if (lean_is_scalar(x_144)) {
 x_145 = lean_alloc_ctor(1, 1, 0);
} else {
 x_145 = x_144;
}
lean_ctor_set(x_145, 0, x_143);
return x_145;
}
}
else
{
lean_object* x_146; lean_object* x_147; 
lean_dec(x_122);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_146 = lean_box(0);
x_147 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_147, 0, x_146);
return x_147;
}
}
}
else
{
uint8_t x_148; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_148 = !lean_is_exclusive(x_80);
if (x_148 == 0)
{
return x_80;
}
else
{
lean_object* x_149; lean_object* x_150; 
x_149 = lean_ctor_get(x_80, 0);
lean_inc(x_149);
lean_dec(x_80);
x_150 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_150, 0, x_149);
return x_150;
}
}
block_79:
{
lean_object* x_27; 
lean_inc_ref(x_1);
x_27 = l_Lean_Meta_Grind_Order_getNodeId(x_1, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec_ref(x_27);
lean_inc_ref(x_2);
x_29 = l_Lean_Meta_Grind_Order_getNodeId(x_2, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
x_31 = l_Lean_Meta_Grind_Order_isRing(x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec_ref(x_31);
x_33 = lean_unbox(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__1));
x_35 = l_Lean_Meta_Grind_Order_mkLePreorderPrefix(x_34, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec_ref(x_35);
x_37 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__3));
x_38 = l_Lean_Meta_Grind_Order_mkLePreorderPrefix(x_37, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec_ref(x_38);
lean_inc_ref(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_40 = l_Lean_mkApp3(x_36, x_1, x_2, x_3);
x_41 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5;
x_42 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_42, 0, x_41);
x_43 = lean_unbox(x_32);
lean_dec(x_32);
lean_ctor_set_uint8(x_42, sizeof(void*)*1, x_43);
lean_inc(x_25);
lean_inc_ref(x_24);
lean_inc(x_23);
lean_inc_ref(x_22);
lean_inc(x_21);
lean_inc_ref(x_20);
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc_ref(x_42);
lean_inc(x_30);
lean_inc(x_28);
x_44 = l_Lean_Meta_Grind_Order_addEdge(x_28, x_30, x_42, x_40, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; 
lean_dec_ref(x_44);
x_45 = l_Lean_mkApp3(x_39, x_1, x_2, x_3);
x_46 = l_Lean_Meta_Grind_Order_addEdge(x_30, x_28, x_42, x_45, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25);
return x_46;
}
else
{
lean_dec_ref(x_42);
lean_dec(x_39);
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_44;
}
}
else
{
uint8_t x_47; 
lean_dec(x_36);
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_47 = !lean_is_exclusive(x_38);
if (x_47 == 0)
{
return x_38;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_38, 0);
lean_inc(x_48);
lean_dec(x_38);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_50 = !lean_is_exclusive(x_35);
if (x_50 == 0)
{
return x_35;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_35, 0);
lean_inc(x_51);
lean_dec(x_35);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_32);
x_53 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__5));
x_54 = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(x_53, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
lean_dec_ref(x_54);
x_56 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__7));
x_57 = l_Lean_Meta_Grind_Order_mkOrdRingPrefix(x_56, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
lean_dec_ref(x_57);
lean_inc_ref(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_59 = l_Lean_mkApp3(x_55, x_1, x_2, x_3);
x_60 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__8;
lean_inc(x_25);
lean_inc_ref(x_24);
lean_inc(x_23);
lean_inc_ref(x_22);
lean_inc(x_21);
lean_inc_ref(x_20);
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_30);
lean_inc(x_28);
x_61 = l_Lean_Meta_Grind_Order_addEdge(x_28, x_30, x_60, x_59, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; 
lean_dec_ref(x_61);
x_62 = l_Lean_mkApp3(x_58, x_1, x_2, x_3);
x_63 = l_Lean_Meta_Grind_Order_addEdge(x_30, x_28, x_60, x_62, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25);
return x_63;
}
else
{
lean_dec(x_58);
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_61;
}
}
else
{
uint8_t x_64; 
lean_dec(x_55);
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_64 = !lean_is_exclusive(x_57);
if (x_64 == 0)
{
return x_57;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_57, 0);
lean_inc(x_65);
lean_dec(x_57);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_65);
return x_66;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_67 = !lean_is_exclusive(x_54);
if (x_67 == 0)
{
return x_54;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_54, 0);
lean_inc(x_68);
lean_dec(x_54);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_68);
return x_69;
}
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_70 = !lean_is_exclusive(x_31);
if (x_70 == 0)
{
return x_31;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_31, 0);
lean_inc(x_71);
lean_dec(x_31);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_71);
return x_72;
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_28);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_73 = !lean_is_exclusive(x_29);
if (x_73 == 0)
{
return x_29;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_29, 0);
lean_inc(x_74);
lean_dec(x_29);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_74);
return x_75;
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_76 = !lean_is_exclusive(x_27);
if (x_76 == 0)
{
return x_27;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_27, 0);
lean_inc(x_77);
lean_dec(x_27);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Order_processNewEq___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_Order_processNewEq___closed__1));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_processNewEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_14; 
x_14 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_1, x_2);
if (x_14 == 0)
{
lean_object* x_15; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_15 = lean_grind_mk_eq_proof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f___redArg(x_1, x_3, x_11);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
if (lean_obj_tag(x_18) == 1)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_getAuxTerm_x3f___redArg(x_2, x_3, x_11);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
if (lean_obj_tag(x_24) == 1)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_free_object(x_22);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Meta_Grind_Order_processNewEq___closed__2;
lean_inc(x_26);
lean_inc(x_20);
x_29 = l_Lean_mkApp7(x_28, x_1, x_2, x_20, x_26, x_21, x_27, x_16);
x_30 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go(x_20, x_26, x_29, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_30;
}
else
{
lean_object* x_31; 
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_31 = lean_box(0);
lean_ctor_set(x_22, 0, x_31);
return x_22;
}
}
else
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_22, 0);
lean_inc(x_32);
lean_dec(x_22);
if (lean_obj_tag(x_32) == 1)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_Meta_Grind_Order_processNewEq___closed__2;
lean_inc(x_34);
lean_inc(x_20);
x_37 = l_Lean_mkApp7(x_36, x_1, x_2, x_20, x_34, x_21, x_35, x_16);
x_38 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go(x_20, x_34, x_37, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_32);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_41 = !lean_is_exclusive(x_22);
if (x_41 == 0)
{
return x_22;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_22, 0);
lean_inc(x_42);
lean_dec(x_22);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
}
}
else
{
lean_object* x_44; 
lean_dec(x_18);
x_44 = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go(x_1, x_2, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_dec(x_16);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_45 = !lean_is_exclusive(x_17);
if (x_45 == 0)
{
return x_17;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_17, 0);
lean_inc(x_46);
lean_dec(x_17);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_48 = !lean_is_exclusive(x_15);
if (x_48 == 0)
{
return x_15;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_15, 0);
lean_inc(x_49);
lean_dec(x_15);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Order_processNewEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_Order_processNewEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
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
l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__0);
l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachSourceOf___closed__1);
l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___redArg___closed__0 = _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___redArg___closed__0();
l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___redArg___closed__2 = _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___redArg___closed__2();
lean_mark_persistent(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_pushToPropagate_spec__1___redArg___closed__2);
l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg___closed__0 = _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg___closed__0();
l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg___closed__1 = _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Order_propagateEqTrue_spec__0_spec__0___redArg___closed__1();
l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5 = _init_l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_Order_propagateEqTrue___closed__5);
l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0___closed__0 = _init_l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0___closed__0();
lean_mark_persistent(l_panic___at___00Lean_Meta_Grind_Order_propagateSelfEqTrue_spec__0___closed__0);
l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__3 = _init_l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Order_propagateSelfEqTrue___closed__3);
l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2 = _init_l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Order_propagateEqFalse___closed__2);
l_Lean_Meta_Grind_Order_propagateSelfEqFalse___closed__1 = _init_l_Lean_Meta_Grind_Order_propagateSelfEqFalse___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Order_propagateSelfEqFalse___closed__1);
l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg___closed__2 = _init_l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg___closed__2();
lean_mark_persistent(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagatePending_spec__0___redArg___closed__2);
l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__3);
l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5 = _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqTrue___closed__5);
l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_checkEqFalse___closed__3);
l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__1);
l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__2);
l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_forEachCnstrsOf___closed__3);
l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqTrue___closed__2);
l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__2);
l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__3);
l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__7 = _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__7);
l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__8 = _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__8();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__8);
l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__9 = _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__9();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__9);
l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__12 = _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__12();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__12);
l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__15 = _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__15();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__15);
l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__28 = _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__28();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__28);
l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__30 = _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__30();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_assertIneqFalse___closed__30);
l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__2);
l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__5 = _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateIneq_go___closed__5);
if (builtin) {res = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLE_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_4281489886____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT___regBuiltin___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_propagateLT_declare__1_00___x40_Lean_Meta_Tactic_Grind_Order_Assert_1204040634____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__8 = _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__8();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__8);
l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__10 = _init_l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__10();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Order_Assert_0__Lean_Meta_Grind_Order_processNewEq_go___closed__10);
l_Lean_Meta_Grind_Order_processNewEq___closed__2 = _init_l_Lean_Meta_Grind_Order_processNewEq___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Order_processNewEq___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
