// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.CommRing.RingM
// Imports: public import Lean.Meta.Tactic.Grind.SynthInstance public import Lean.Meta.Tactic.Grind.Arith.CommRing.MonadRing
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
lean_object* l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_grind_canon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon___redArg(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_CommRing_ringExt;
lean_object* l_Lean_Meta_Grind_SolverExtension_markTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_hashPtrExpr_unsafe__1___boxed(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_compare(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Grind_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_synthInstanceMeta_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxSteps___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxSteps___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxSteps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxSteps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg___lam__0(lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_incSteps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_incSteps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getRingId___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getRingId___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getRingId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getRingId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__0___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___closed__0_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__1___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___closed__0_value),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___closed__1_value)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "`grind` internal error, invalid ringId"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisorsInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisorsInst_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisors(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisors___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_hasChar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_hasChar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 60, .m_capacity = 60, .m_length = 59, .m_data = "`grind` internal error, ring does not have a characteristic"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCharInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCharInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isField(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isField___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "expression in two different rings"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___closed__0_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_hashPtrExpr_unsafe__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkVar_spec__0___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkVar_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkVar_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxSteps___redArg(lean_object* v_a_1_, lean_object* v_a_2_, lean_object* v_a_3_){
_start:
{
lean_object* v___x_5_; 
v___x_5_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_1_, v_a_3_);
if (lean_obj_tag(v___x_5_) == 0)
{
lean_object* v_a_6_; lean_object* v___x_7_; 
v_a_6_ = lean_ctor_get(v___x_5_, 0);
lean_inc(v_a_6_);
lean_dec_ref(v___x_5_);
v___x_7_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_2_);
if (lean_obj_tag(v___x_7_) == 0)
{
lean_object* v_a_8_; lean_object* v___x_10_; uint8_t v_isShared_11_; uint8_t v_isSharedCheck_19_; 
v_a_8_ = lean_ctor_get(v___x_7_, 0);
v_isSharedCheck_19_ = !lean_is_exclusive(v___x_7_);
if (v_isSharedCheck_19_ == 0)
{
v___x_10_ = v___x_7_;
v_isShared_11_ = v_isSharedCheck_19_;
goto v_resetjp_9_;
}
else
{
lean_inc(v_a_8_);
lean_dec(v___x_7_);
v___x_10_ = lean_box(0);
v_isShared_11_ = v_isSharedCheck_19_;
goto v_resetjp_9_;
}
v_resetjp_9_:
{
lean_object* v_ringSteps_12_; lean_object* v_steps_13_; uint8_t v___x_14_; lean_object* v___x_15_; lean_object* v___x_17_; 
v_ringSteps_12_ = lean_ctor_get(v_a_8_, 5);
lean_inc(v_ringSteps_12_);
lean_dec(v_a_8_);
v_steps_13_ = lean_ctor_get(v_a_6_, 12);
lean_inc(v_steps_13_);
lean_dec(v_a_6_);
v___x_14_ = lean_nat_dec_le(v_ringSteps_12_, v_steps_13_);
lean_dec(v_steps_13_);
lean_dec(v_ringSteps_12_);
v___x_15_ = lean_box(v___x_14_);
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 0, v___x_15_);
v___x_17_ = v___x_10_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v___x_15_);
v___x_17_ = v_reuseFailAlloc_18_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
return v___x_17_;
}
}
}
else
{
lean_object* v_a_20_; lean_object* v___x_22_; uint8_t v_isShared_23_; uint8_t v_isSharedCheck_27_; 
lean_dec(v_a_6_);
v_a_20_ = lean_ctor_get(v___x_7_, 0);
v_isSharedCheck_27_ = !lean_is_exclusive(v___x_7_);
if (v_isSharedCheck_27_ == 0)
{
v___x_22_ = v___x_7_;
v_isShared_23_ = v_isSharedCheck_27_;
goto v_resetjp_21_;
}
else
{
lean_inc(v_a_20_);
lean_dec(v___x_7_);
v___x_22_ = lean_box(0);
v_isShared_23_ = v_isSharedCheck_27_;
goto v_resetjp_21_;
}
v_resetjp_21_:
{
lean_object* v___x_25_; 
if (v_isShared_23_ == 0)
{
v___x_25_ = v___x_22_;
goto v_reusejp_24_;
}
else
{
lean_object* v_reuseFailAlloc_26_; 
v_reuseFailAlloc_26_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_26_, 0, v_a_20_);
v___x_25_ = v_reuseFailAlloc_26_;
goto v_reusejp_24_;
}
v_reusejp_24_:
{
return v___x_25_;
}
}
}
}
else
{
lean_object* v_a_28_; lean_object* v___x_30_; uint8_t v_isShared_31_; uint8_t v_isSharedCheck_35_; 
v_a_28_ = lean_ctor_get(v___x_5_, 0);
v_isSharedCheck_35_ = !lean_is_exclusive(v___x_5_);
if (v_isSharedCheck_35_ == 0)
{
v___x_30_ = v___x_5_;
v_isShared_31_ = v_isSharedCheck_35_;
goto v_resetjp_29_;
}
else
{
lean_inc(v_a_28_);
lean_dec(v___x_5_);
v___x_30_ = lean_box(0);
v_isShared_31_ = v_isSharedCheck_35_;
goto v_resetjp_29_;
}
v_resetjp_29_:
{
lean_object* v___x_33_; 
if (v_isShared_31_ == 0)
{
v___x_33_ = v___x_30_;
goto v_reusejp_32_;
}
else
{
lean_object* v_reuseFailAlloc_34_; 
v_reuseFailAlloc_34_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_34_, 0, v_a_28_);
v___x_33_ = v_reuseFailAlloc_34_;
goto v_reusejp_32_;
}
v_reusejp_32_:
{
return v___x_33_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxSteps___redArg___boxed(lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lean_Meta_Grind_Arith_CommRing_checkMaxSteps___redArg(v_a_36_, v_a_37_, v_a_38_);
lean_dec_ref(v_a_38_);
lean_dec_ref(v_a_37_);
lean_dec(v_a_36_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxSteps(lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l_Lean_Meta_Grind_Arith_CommRing_checkMaxSteps___redArg(v_a_41_, v_a_43_, v_a_49_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxSteps___boxed(lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_Lean_Meta_Grind_Arith_CommRing_checkMaxSteps(v_a_53_, v_a_54_, v_a_55_, v_a_56_, v_a_57_, v_a_58_, v_a_59_, v_a_60_, v_a_61_, v_a_62_);
lean_dec(v_a_62_);
lean_dec_ref(v_a_61_);
lean_dec(v_a_60_);
lean_dec_ref(v_a_59_);
lean_dec(v_a_58_);
lean_dec_ref(v_a_57_);
lean_dec(v_a_56_);
lean_dec_ref(v_a_55_);
lean_dec(v_a_54_);
lean_dec(v_a_53_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg___lam__0(lean_object* v_s_65_){
_start:
{
lean_object* v_rings_66_; lean_object* v_typeIdOf_67_; lean_object* v_exprToRingId_68_; lean_object* v_semirings_69_; lean_object* v_stypeIdOf_70_; lean_object* v_exprToSemiringId_71_; lean_object* v_ncRings_72_; lean_object* v_exprToNCRingId_73_; lean_object* v_nctypeIdOf_74_; lean_object* v_ncSemirings_75_; lean_object* v_exprToNCSemiringId_76_; lean_object* v_ncstypeIdOf_77_; lean_object* v_steps_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_87_; 
v_rings_66_ = lean_ctor_get(v_s_65_, 0);
v_typeIdOf_67_ = lean_ctor_get(v_s_65_, 1);
v_exprToRingId_68_ = lean_ctor_get(v_s_65_, 2);
v_semirings_69_ = lean_ctor_get(v_s_65_, 3);
v_stypeIdOf_70_ = lean_ctor_get(v_s_65_, 4);
v_exprToSemiringId_71_ = lean_ctor_get(v_s_65_, 5);
v_ncRings_72_ = lean_ctor_get(v_s_65_, 6);
v_exprToNCRingId_73_ = lean_ctor_get(v_s_65_, 7);
v_nctypeIdOf_74_ = lean_ctor_get(v_s_65_, 8);
v_ncSemirings_75_ = lean_ctor_get(v_s_65_, 9);
v_exprToNCSemiringId_76_ = lean_ctor_get(v_s_65_, 10);
v_ncstypeIdOf_77_ = lean_ctor_get(v_s_65_, 11);
v_steps_78_ = lean_ctor_get(v_s_65_, 12);
v_isSharedCheck_87_ = !lean_is_exclusive(v_s_65_);
if (v_isSharedCheck_87_ == 0)
{
v___x_80_ = v_s_65_;
v_isShared_81_ = v_isSharedCheck_87_;
goto v_resetjp_79_;
}
else
{
lean_inc(v_steps_78_);
lean_inc(v_ncstypeIdOf_77_);
lean_inc(v_exprToNCSemiringId_76_);
lean_inc(v_ncSemirings_75_);
lean_inc(v_nctypeIdOf_74_);
lean_inc(v_exprToNCRingId_73_);
lean_inc(v_ncRings_72_);
lean_inc(v_exprToSemiringId_71_);
lean_inc(v_stypeIdOf_70_);
lean_inc(v_semirings_69_);
lean_inc(v_exprToRingId_68_);
lean_inc(v_typeIdOf_67_);
lean_inc(v_rings_66_);
lean_dec(v_s_65_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_87_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_85_; 
v___x_82_ = lean_unsigned_to_nat(1u);
v___x_83_ = lean_nat_add(v_steps_78_, v___x_82_);
lean_dec(v_steps_78_);
if (v_isShared_81_ == 0)
{
lean_ctor_set(v___x_80_, 12, v___x_83_);
v___x_85_ = v___x_80_;
goto v_reusejp_84_;
}
else
{
lean_object* v_reuseFailAlloc_86_; 
v_reuseFailAlloc_86_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_86_, 0, v_rings_66_);
lean_ctor_set(v_reuseFailAlloc_86_, 1, v_typeIdOf_67_);
lean_ctor_set(v_reuseFailAlloc_86_, 2, v_exprToRingId_68_);
lean_ctor_set(v_reuseFailAlloc_86_, 3, v_semirings_69_);
lean_ctor_set(v_reuseFailAlloc_86_, 4, v_stypeIdOf_70_);
lean_ctor_set(v_reuseFailAlloc_86_, 5, v_exprToSemiringId_71_);
lean_ctor_set(v_reuseFailAlloc_86_, 6, v_ncRings_72_);
lean_ctor_set(v_reuseFailAlloc_86_, 7, v_exprToNCRingId_73_);
lean_ctor_set(v_reuseFailAlloc_86_, 8, v_nctypeIdOf_74_);
lean_ctor_set(v_reuseFailAlloc_86_, 9, v_ncSemirings_75_);
lean_ctor_set(v_reuseFailAlloc_86_, 10, v_exprToNCSemiringId_76_);
lean_ctor_set(v_reuseFailAlloc_86_, 11, v_ncstypeIdOf_77_);
lean_ctor_set(v_reuseFailAlloc_86_, 12, v___x_83_);
v___x_85_ = v_reuseFailAlloc_86_;
goto v_reusejp_84_;
}
v_reusejp_84_:
{
return v___x_85_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg(lean_object* v_a_89_){
_start:
{
lean_object* v___f_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v___f_91_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg___closed__0));
v___x_92_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_93_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_92_, v___f_91_, v_a_89_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg___boxed(lean_object* v_a_94_, lean_object* v_a_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg(v_a_94_);
lean_dec(v_a_94_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_incSteps(lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg(v_a_97_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_incSteps___boxed(lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_Lean_Meta_Grind_Arith_CommRing_incSteps(v_a_109_, v_a_110_, v_a_111_, v_a_112_, v_a_113_, v_a_114_, v_a_115_, v_a_116_, v_a_117_, v_a_118_);
lean_dec(v_a_118_);
lean_dec_ref(v_a_117_);
lean_dec(v_a_116_);
lean_dec_ref(v_a_115_);
lean_dec(v_a_114_);
lean_dec_ref(v_a_113_);
lean_dec(v_a_112_);
lean_dec_ref(v_a_111_);
lean_dec(v_a_110_);
lean_dec(v_a_109_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_run___redArg(lean_object* v_ringId_121_, lean_object* v_x_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_){
_start:
{
uint8_t v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_134_ = 0;
v___x_135_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_135_, 0, v_ringId_121_);
lean_ctor_set_uint8(v___x_135_, sizeof(void*)*1, v___x_134_);
v___x_136_ = lean_apply_12(v_x_122_, v___x_135_, v_a_123_, v_a_124_, v_a_125_, v_a_126_, v_a_127_, v_a_128_, v_a_129_, v_a_130_, v_a_131_, v_a_132_, lean_box(0));
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_run___redArg___boxed(lean_object* v_ringId_137_, lean_object* v_x_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_run___redArg(v_ringId_137_, v_x_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_run(lean_object* v_00_u03b1_151_, lean_object* v_ringId_152_, lean_object* v_x_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_){
_start:
{
uint8_t v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_165_ = 0;
v___x_166_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_166_, 0, v_ringId_152_);
lean_ctor_set_uint8(v___x_166_, sizeof(void*)*1, v___x_165_);
v___x_167_ = lean_apply_12(v_x_153_, v___x_166_, v_a_154_, v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_, v_a_163_, lean_box(0));
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_run___boxed(lean_object* v_00_u03b1_168_, lean_object* v_ringId_169_, lean_object* v_x_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_run(v_00_u03b1_168_, v_ringId_169_, v_x_170_, v_a_171_, v_a_172_, v_a_173_, v_a_174_, v_a_175_, v_a_176_, v_a_177_, v_a_178_, v_a_179_, v_a_180_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getRingId___redArg(lean_object* v_a_183_){
_start:
{
lean_object* v_ringId_185_; lean_object* v___x_186_; 
v_ringId_185_ = lean_ctor_get(v_a_183_, 0);
lean_inc(v_ringId_185_);
v___x_186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_186_, 0, v_ringId_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getRingId___redArg___boxed(lean_object* v_a_187_, lean_object* v_a_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l_Lean_Meta_Grind_Arith_CommRing_getRingId___redArg(v_a_187_);
lean_dec_ref(v_a_187_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getRingId(lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_){
_start:
{
lean_object* v_ringId_202_; lean_object* v___x_203_; 
v_ringId_202_ = lean_ctor_get(v_a_190_, 0);
lean_inc(v_ringId_202_);
v___x_203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_203_, 0, v_ringId_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getRingId___boxed(lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_Lean_Meta_Grind_Arith_CommRing_getRingId(v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_);
lean_dec(v_a_214_);
lean_dec_ref(v_a_213_);
lean_dec(v_a_212_);
lean_dec_ref(v_a_211_);
lean_dec(v_a_210_);
lean_dec_ref(v_a_209_);
lean_dec(v_a_208_);
lean_dec_ref(v_a_207_);
lean_dec(v_a_206_);
lean_dec(v_a_205_);
lean_dec_ref(v_a_204_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__0(lean_object* v_e_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_){
_start:
{
lean_object* v___x_230_; 
lean_inc(v___y_224_);
v___x_230_ = lean_grind_canon(v_e_217_, v___y_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_, v___y_228_);
if (lean_obj_tag(v___x_230_) == 0)
{
lean_object* v_a_231_; lean_object* v___x_232_; 
v_a_231_ = lean_ctor_get(v___x_230_, 0);
lean_inc(v_a_231_);
lean_dec_ref(v___x_230_);
v___x_232_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_231_, v___y_224_);
lean_dec(v___y_224_);
return v___x_232_;
}
else
{
lean_dec(v___y_224_);
return v___x_230_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__0___boxed(lean_object* v_e_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__0(v_e_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_);
lean_dec_ref(v___y_234_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__1(lean_object* v_e_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_){
_start:
{
lean_object* v___x_260_; 
v___x_260_ = l_Lean_Meta_Grind_synthInstanceMeta_x3f(v_e_247_, v___y_255_, v___y_256_, v___y_257_, v___y_258_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__1___boxed(lean_object* v_e_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__1(v_e_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_, v___y_272_);
lean_dec(v___y_268_);
lean_dec_ref(v___y_267_);
lean_dec(v___y_266_);
lean_dec_ref(v___y_265_);
lean_dec(v___y_264_);
lean_dec(v___y_263_);
lean_dec_ref(v___y_262_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0_spec__0(lean_object* v_msgData_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_){
_start:
{
lean_object* v___x_287_; lean_object* v_env_288_; lean_object* v___x_289_; lean_object* v_mctx_290_; lean_object* v_lctx_291_; lean_object* v_options_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_287_ = lean_st_ref_get(v___y_285_);
v_env_288_ = lean_ctor_get(v___x_287_, 0);
lean_inc_ref(v_env_288_);
lean_dec(v___x_287_);
v___x_289_ = lean_st_ref_get(v___y_283_);
v_mctx_290_ = lean_ctor_get(v___x_289_, 0);
lean_inc_ref(v_mctx_290_);
lean_dec(v___x_289_);
v_lctx_291_ = lean_ctor_get(v___y_282_, 2);
v_options_292_ = lean_ctor_get(v___y_284_, 2);
lean_inc_ref(v_options_292_);
lean_inc_ref(v_lctx_291_);
v___x_293_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_293_, 0, v_env_288_);
lean_ctor_set(v___x_293_, 1, v_mctx_290_);
lean_ctor_set(v___x_293_, 2, v_lctx_291_);
lean_ctor_set(v___x_293_, 3, v_options_292_);
v___x_294_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_294_, 0, v___x_293_);
lean_ctor_set(v___x_294_, 1, v_msgData_281_);
v___x_295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_295_, 0, v___x_294_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0_spec__0___boxed(lean_object* v_msgData_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0_spec__0(v_msgData_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_);
lean_dec(v___y_300_);
lean_dec_ref(v___y_299_);
lean_dec(v___y_298_);
lean_dec_ref(v___y_297_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg(lean_object* v_msg_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_){
_start:
{
lean_object* v_ref_309_; lean_object* v___x_310_; lean_object* v_a_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_319_; 
v_ref_309_ = lean_ctor_get(v___y_306_, 5);
v___x_310_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0_spec__0(v_msg_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_);
v_a_311_ = lean_ctor_get(v___x_310_, 0);
v_isSharedCheck_319_ = !lean_is_exclusive(v___x_310_);
if (v_isSharedCheck_319_ == 0)
{
v___x_313_ = v___x_310_;
v_isShared_314_ = v_isSharedCheck_319_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_a_311_);
lean_dec(v___x_310_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_319_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v___x_315_; lean_object* v___x_317_; 
lean_inc(v_ref_309_);
v___x_315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_315_, 0, v_ref_309_);
lean_ctor_set(v___x_315_, 1, v_a_311_);
if (v_isShared_314_ == 0)
{
lean_ctor_set_tag(v___x_313_, 1);
lean_ctor_set(v___x_313_, 0, v___x_315_);
v___x_317_ = v___x_313_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v___x_315_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg___boxed(lean_object* v_msg_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg(v_msg_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_);
lean_dec(v___y_324_);
lean_dec_ref(v___y_323_);
lean_dec(v___y_322_);
lean_dec_ref(v___y_321_);
return v_res_326_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__1(void){
_start:
{
lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_328_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__0));
v___x_329_ = l_Lean_stringToMessageData(v___x_328_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_){
_start:
{
lean_object* v___x_342_; 
v___x_342_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_331_, v_a_339_);
if (lean_obj_tag(v___x_342_) == 0)
{
lean_object* v_a_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_357_; 
v_a_343_ = lean_ctor_get(v___x_342_, 0);
v_isSharedCheck_357_ = !lean_is_exclusive(v___x_342_);
if (v_isSharedCheck_357_ == 0)
{
v___x_345_ = v___x_342_;
v_isShared_346_ = v_isSharedCheck_357_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_a_343_);
lean_dec(v___x_342_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_357_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v_ringId_347_; lean_object* v_rings_348_; lean_object* v___x_349_; uint8_t v___x_350_; 
v_ringId_347_ = lean_ctor_get(v_a_330_, 0);
v_rings_348_ = lean_ctor_get(v_a_343_, 0);
lean_inc_ref(v_rings_348_);
lean_dec(v_a_343_);
v___x_349_ = lean_array_get_size(v_rings_348_);
v___x_350_ = lean_nat_dec_lt(v_ringId_347_, v___x_349_);
if (v___x_350_ == 0)
{
lean_object* v___x_351_; lean_object* v___x_352_; 
lean_dec_ref(v_rings_348_);
lean_del_object(v___x_345_);
v___x_351_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__1);
v___x_352_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg(v___x_351_, v_a_337_, v_a_338_, v_a_339_, v_a_340_);
return v___x_352_;
}
else
{
lean_object* v___x_353_; lean_object* v___x_355_; 
v___x_353_ = lean_array_fget(v_rings_348_, v_ringId_347_);
lean_dec_ref(v_rings_348_);
if (v_isShared_346_ == 0)
{
lean_ctor_set(v___x_345_, 0, v___x_353_);
v___x_355_ = v___x_345_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v___x_353_);
v___x_355_ = v_reuseFailAlloc_356_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
return v___x_355_;
}
}
}
}
else
{
lean_object* v_a_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_365_; 
v_a_358_ = lean_ctor_get(v___x_342_, 0);
v_isSharedCheck_365_ = !lean_is_exclusive(v___x_342_);
if (v_isSharedCheck_365_ == 0)
{
v___x_360_ = v___x_342_;
v_isShared_361_ = v_isSharedCheck_365_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_a_358_);
lean_dec(v___x_342_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_365_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_363_; 
if (v_isShared_361_ == 0)
{
v___x_363_ = v___x_360_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v_a_358_);
v___x_363_ = v_reuseFailAlloc_364_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
return v___x_363_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___boxed(lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_, v_a_371_, v_a_372_, v_a_373_, v_a_374_, v_a_375_, v_a_376_);
lean_dec(v_a_376_);
lean_dec_ref(v_a_375_);
lean_dec(v_a_374_);
lean_dec_ref(v_a_373_);
lean_dec(v_a_372_);
lean_dec_ref(v_a_371_);
lean_dec(v_a_370_);
lean_dec_ref(v_a_369_);
lean_dec(v_a_368_);
lean_dec(v_a_367_);
lean_dec_ref(v_a_366_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0(lean_object* v_00_u03b1_379_, lean_object* v_msg_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_){
_start:
{
lean_object* v___x_393_; 
v___x_393_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg(v_msg_380_, v___y_388_, v___y_389_, v___y_390_, v___y_391_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___boxed(lean_object* v_00_u03b1_394_, lean_object* v_msg_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0(v_00_u03b1_394_, v_msg_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_);
lean_dec(v___y_406_);
lean_dec_ref(v___y_405_);
lean_dec(v___y_404_);
lean_dec_ref(v___y_403_);
lean_dec(v___y_402_);
lean_dec_ref(v___y_401_);
lean_dec(v___y_400_);
lean_dec_ref(v___y_399_);
lean_dec(v___y_398_);
lean_dec(v___y_397_);
lean_dec_ref(v___y_396_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg___lam__0(lean_object* v_ringId_409_, lean_object* v_f_410_, lean_object* v_s_411_){
_start:
{
lean_object* v_rings_412_; lean_object* v_typeIdOf_413_; lean_object* v_exprToRingId_414_; lean_object* v_semirings_415_; lean_object* v_stypeIdOf_416_; lean_object* v_exprToSemiringId_417_; lean_object* v_ncRings_418_; lean_object* v_exprToNCRingId_419_; lean_object* v_nctypeIdOf_420_; lean_object* v_ncSemirings_421_; lean_object* v_exprToNCSemiringId_422_; lean_object* v_ncstypeIdOf_423_; lean_object* v_steps_424_; lean_object* v___x_425_; uint8_t v___x_426_; 
v_rings_412_ = lean_ctor_get(v_s_411_, 0);
v_typeIdOf_413_ = lean_ctor_get(v_s_411_, 1);
v_exprToRingId_414_ = lean_ctor_get(v_s_411_, 2);
v_semirings_415_ = lean_ctor_get(v_s_411_, 3);
v_stypeIdOf_416_ = lean_ctor_get(v_s_411_, 4);
v_exprToSemiringId_417_ = lean_ctor_get(v_s_411_, 5);
v_ncRings_418_ = lean_ctor_get(v_s_411_, 6);
v_exprToNCRingId_419_ = lean_ctor_get(v_s_411_, 7);
v_nctypeIdOf_420_ = lean_ctor_get(v_s_411_, 8);
v_ncSemirings_421_ = lean_ctor_get(v_s_411_, 9);
v_exprToNCSemiringId_422_ = lean_ctor_get(v_s_411_, 10);
v_ncstypeIdOf_423_ = lean_ctor_get(v_s_411_, 11);
v_steps_424_ = lean_ctor_get(v_s_411_, 12);
v___x_425_ = lean_array_get_size(v_rings_412_);
v___x_426_ = lean_nat_dec_lt(v_ringId_409_, v___x_425_);
if (v___x_426_ == 0)
{
lean_dec_ref(v_f_410_);
return v_s_411_;
}
else
{
lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_438_; 
lean_inc(v_steps_424_);
lean_inc_ref(v_ncstypeIdOf_423_);
lean_inc_ref(v_exprToNCSemiringId_422_);
lean_inc_ref(v_ncSemirings_421_);
lean_inc_ref(v_nctypeIdOf_420_);
lean_inc_ref(v_exprToNCRingId_419_);
lean_inc_ref(v_ncRings_418_);
lean_inc_ref(v_exprToSemiringId_417_);
lean_inc_ref(v_stypeIdOf_416_);
lean_inc_ref(v_semirings_415_);
lean_inc_ref(v_exprToRingId_414_);
lean_inc_ref(v_typeIdOf_413_);
lean_inc_ref(v_rings_412_);
v_isSharedCheck_438_ = !lean_is_exclusive(v_s_411_);
if (v_isSharedCheck_438_ == 0)
{
lean_object* v_unused_439_; lean_object* v_unused_440_; lean_object* v_unused_441_; lean_object* v_unused_442_; lean_object* v_unused_443_; lean_object* v_unused_444_; lean_object* v_unused_445_; lean_object* v_unused_446_; lean_object* v_unused_447_; lean_object* v_unused_448_; lean_object* v_unused_449_; lean_object* v_unused_450_; lean_object* v_unused_451_; 
v_unused_439_ = lean_ctor_get(v_s_411_, 12);
lean_dec(v_unused_439_);
v_unused_440_ = lean_ctor_get(v_s_411_, 11);
lean_dec(v_unused_440_);
v_unused_441_ = lean_ctor_get(v_s_411_, 10);
lean_dec(v_unused_441_);
v_unused_442_ = lean_ctor_get(v_s_411_, 9);
lean_dec(v_unused_442_);
v_unused_443_ = lean_ctor_get(v_s_411_, 8);
lean_dec(v_unused_443_);
v_unused_444_ = lean_ctor_get(v_s_411_, 7);
lean_dec(v_unused_444_);
v_unused_445_ = lean_ctor_get(v_s_411_, 6);
lean_dec(v_unused_445_);
v_unused_446_ = lean_ctor_get(v_s_411_, 5);
lean_dec(v_unused_446_);
v_unused_447_ = lean_ctor_get(v_s_411_, 4);
lean_dec(v_unused_447_);
v_unused_448_ = lean_ctor_get(v_s_411_, 3);
lean_dec(v_unused_448_);
v_unused_449_ = lean_ctor_get(v_s_411_, 2);
lean_dec(v_unused_449_);
v_unused_450_ = lean_ctor_get(v_s_411_, 1);
lean_dec(v_unused_450_);
v_unused_451_ = lean_ctor_get(v_s_411_, 0);
lean_dec(v_unused_451_);
v___x_428_ = v_s_411_;
v_isShared_429_ = v_isSharedCheck_438_;
goto v_resetjp_427_;
}
else
{
lean_dec(v_s_411_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_438_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v_v_430_; lean_object* v___x_431_; lean_object* v_xs_x27_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_436_; 
v_v_430_ = lean_array_fget(v_rings_412_, v_ringId_409_);
v___x_431_ = lean_box(0);
v_xs_x27_432_ = lean_array_fset(v_rings_412_, v_ringId_409_, v___x_431_);
v___x_433_ = lean_apply_1(v_f_410_, v_v_430_);
v___x_434_ = lean_array_fset(v_xs_x27_432_, v_ringId_409_, v___x_433_);
if (v_isShared_429_ == 0)
{
lean_ctor_set(v___x_428_, 0, v___x_434_);
v___x_436_ = v___x_428_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v___x_434_);
lean_ctor_set(v_reuseFailAlloc_437_, 1, v_typeIdOf_413_);
lean_ctor_set(v_reuseFailAlloc_437_, 2, v_exprToRingId_414_);
lean_ctor_set(v_reuseFailAlloc_437_, 3, v_semirings_415_);
lean_ctor_set(v_reuseFailAlloc_437_, 4, v_stypeIdOf_416_);
lean_ctor_set(v_reuseFailAlloc_437_, 5, v_exprToSemiringId_417_);
lean_ctor_set(v_reuseFailAlloc_437_, 6, v_ncRings_418_);
lean_ctor_set(v_reuseFailAlloc_437_, 7, v_exprToNCRingId_419_);
lean_ctor_set(v_reuseFailAlloc_437_, 8, v_nctypeIdOf_420_);
lean_ctor_set(v_reuseFailAlloc_437_, 9, v_ncSemirings_421_);
lean_ctor_set(v_reuseFailAlloc_437_, 10, v_exprToNCSemiringId_422_);
lean_ctor_set(v_reuseFailAlloc_437_, 11, v_ncstypeIdOf_423_);
lean_ctor_set(v_reuseFailAlloc_437_, 12, v_steps_424_);
v___x_436_ = v_reuseFailAlloc_437_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
return v___x_436_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg___lam__0___boxed(lean_object* v_ringId_452_, lean_object* v_f_453_, lean_object* v_s_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg___lam__0(v_ringId_452_, v_f_453_, v_s_454_);
lean_dec(v_ringId_452_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(lean_object* v_f_456_, lean_object* v_a_457_, lean_object* v_a_458_){
_start:
{
lean_object* v_ringId_460_; lean_object* v___f_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v_ringId_460_ = lean_ctor_get(v_a_457_, 0);
lean_inc(v_ringId_460_);
lean_dec_ref(v_a_457_);
v___f_461_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_461_, 0, v_ringId_460_);
lean_closure_set(v___f_461_, 1, v_f_456_);
v___x_462_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_463_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_462_, v___f_461_, v_a_458_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg___boxed(lean_object* v_f_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v_f_464_, v_a_465_, v_a_466_);
lean_dec(v_a_466_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing(lean_object* v_f_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_){
_start:
{
lean_object* v___x_482_; 
v___x_482_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v_f_469_, v_a_470_, v_a_471_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___boxed(lean_object* v_f_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing(v_f_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_);
lean_dec(v_a_494_);
lean_dec_ref(v_a_493_);
lean_dec(v_a_492_);
lean_dec_ref(v_a_491_);
lean_dec(v_a_490_);
lean_dec_ref(v_a_489_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec(v_a_486_);
lean_dec(v_a_485_);
return v_res_496_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__1(void){
_start:
{
lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_498_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__0));
v___x_499_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___boxed), 12, 0);
v___x_500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_500_, 0, v___x_499_);
lean_ctor_set(v___x_500_, 1, v___x_498_);
return v___x_500_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM(void){
_start:
{
lean_object* v___x_501_; 
v___x_501_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__1);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd___redArg(lean_object* v_x_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_){
_start:
{
lean_object* v_ringId_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_524_; 
v_ringId_515_ = lean_ctor_get(v_a_503_, 0);
v_isSharedCheck_524_ = !lean_is_exclusive(v_a_503_);
if (v_isSharedCheck_524_ == 0)
{
v___x_517_ = v_a_503_;
v_isShared_518_ = v_isSharedCheck_524_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_ringId_515_);
lean_dec(v_a_503_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_524_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
uint8_t v___x_519_; lean_object* v___x_521_; 
v___x_519_ = 1;
if (v_isShared_518_ == 0)
{
v___x_521_ = v___x_517_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v_ringId_515_);
v___x_521_ = v_reuseFailAlloc_523_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
lean_object* v___x_522_; 
lean_ctor_set_uint8(v___x_521_, sizeof(void*)*1, v___x_519_);
v___x_522_ = lean_apply_12(v_x_502_, v___x_521_, v_a_504_, v_a_505_, v_a_506_, v_a_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_, lean_box(0));
return v___x_522_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd___redArg___boxed(lean_object* v_x_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd___redArg(v_x_525_, v_a_526_, v_a_527_, v_a_528_, v_a_529_, v_a_530_, v_a_531_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd(lean_object* v_00_u03b1_539_, lean_object* v_x_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_){
_start:
{
lean_object* v_ringId_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_562_; 
v_ringId_553_ = lean_ctor_get(v_a_541_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v_a_541_);
if (v_isSharedCheck_562_ == 0)
{
v___x_555_ = v_a_541_;
v_isShared_556_ = v_isSharedCheck_562_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_ringId_553_);
lean_dec(v_a_541_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_562_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
uint8_t v___x_557_; lean_object* v___x_559_; 
v___x_557_ = 1;
if (v_isShared_556_ == 0)
{
v___x_559_ = v___x_555_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_ringId_553_);
v___x_559_ = v_reuseFailAlloc_561_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
lean_object* v___x_560_; 
lean_ctor_set_uint8(v___x_559_, sizeof(void*)*1, v___x_557_);
v___x_560_ = lean_apply_12(v_x_540_, v___x_559_, v_a_542_, v_a_543_, v_a_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_, v_a_550_, v_a_551_, lean_box(0));
return v___x_560_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd___boxed(lean_object* v_00_u03b1_563_, lean_object* v_x_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd(v_00_u03b1_563_, v_x_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_, v_a_570_, v_a_571_, v_a_572_, v_a_573_, v_a_574_, v_a_575_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___redArg(lean_object* v_a_578_){
_start:
{
uint8_t v_checkCoeffDvd_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v_checkCoeffDvd_580_ = lean_ctor_get_uint8(v_a_578_, sizeof(void*)*1);
v___x_581_ = lean_box(v_checkCoeffDvd_580_);
v___x_582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_582_, 0, v___x_581_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___redArg___boxed(lean_object* v_a_583_, lean_object* v_a_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___redArg(v_a_583_);
lean_dec_ref(v_a_583_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd(lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_){
_start:
{
lean_object* v___x_598_; 
v___x_598_ = l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___redArg(v_a_586_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___boxed(lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd(v_a_599_, v_a_600_, v_a_601_, v_a_602_, v_a_603_, v_a_604_, v_a_605_, v_a_606_, v_a_607_, v_a_608_, v_a_609_);
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
lean_dec_ref(v_a_599_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_612_, lean_object* v_vals_613_, lean_object* v_i_614_, lean_object* v_k_615_){
_start:
{
lean_object* v___x_616_; uint8_t v___x_617_; 
v___x_616_ = lean_array_get_size(v_keys_612_);
v___x_617_ = lean_nat_dec_lt(v_i_614_, v___x_616_);
if (v___x_617_ == 0)
{
lean_object* v___x_618_; 
lean_dec(v_i_614_);
v___x_618_ = lean_box(0);
return v___x_618_;
}
else
{
lean_object* v_k_x27_619_; uint8_t v___x_620_; 
v_k_x27_619_ = lean_array_fget_borrowed(v_keys_612_, v_i_614_);
v___x_620_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_615_, v_k_x27_619_);
if (v___x_620_ == 0)
{
lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_621_ = lean_unsigned_to_nat(1u);
v___x_622_ = lean_nat_add(v_i_614_, v___x_621_);
lean_dec(v_i_614_);
v_i_614_ = v___x_622_;
goto _start;
}
else
{
lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_624_ = lean_array_fget_borrowed(v_vals_613_, v_i_614_);
lean_dec(v_i_614_);
lean_inc(v___x_624_);
v___x_625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_625_, 0, v___x_624_);
return v___x_625_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_626_, lean_object* v_vals_627_, lean_object* v_i_628_, lean_object* v_k_629_){
_start:
{
lean_object* v_res_630_; 
v_res_630_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_626_, v_vals_627_, v_i_628_, v_k_629_);
lean_dec_ref(v_k_629_);
lean_dec_ref(v_vals_627_);
lean_dec_ref(v_keys_626_);
return v_res_630_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_631_; size_t v___x_632_; size_t v___x_633_; 
v___x_631_ = ((size_t)5ULL);
v___x_632_ = ((size_t)1ULL);
v___x_633_ = lean_usize_shift_left(v___x_632_, v___x_631_);
return v___x_633_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_634_; size_t v___x_635_; size_t v___x_636_; 
v___x_634_ = ((size_t)1ULL);
v___x_635_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__0);
v___x_636_ = lean_usize_sub(v___x_635_, v___x_634_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg(lean_object* v_x_637_, size_t v_x_638_, lean_object* v_x_639_){
_start:
{
if (lean_obj_tag(v_x_637_) == 0)
{
lean_object* v_es_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_661_; 
v_es_640_ = lean_ctor_get(v_x_637_, 0);
v_isSharedCheck_661_ = !lean_is_exclusive(v_x_637_);
if (v_isSharedCheck_661_ == 0)
{
v___x_642_ = v_x_637_;
v_isShared_643_ = v_isSharedCheck_661_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_es_640_);
lean_dec(v_x_637_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_661_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_644_; size_t v___x_645_; size_t v___x_646_; size_t v___x_647_; lean_object* v_j_648_; lean_object* v___x_649_; 
v___x_644_ = lean_box(2);
v___x_645_ = ((size_t)5ULL);
v___x_646_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__1);
v___x_647_ = lean_usize_land(v_x_638_, v___x_646_);
v_j_648_ = lean_usize_to_nat(v___x_647_);
v___x_649_ = lean_array_get(v___x_644_, v_es_640_, v_j_648_);
lean_dec(v_j_648_);
lean_dec_ref(v_es_640_);
switch(lean_obj_tag(v___x_649_))
{
case 0:
{
lean_object* v_key_650_; lean_object* v_val_651_; uint8_t v___x_652_; 
v_key_650_ = lean_ctor_get(v___x_649_, 0);
lean_inc(v_key_650_);
v_val_651_ = lean_ctor_get(v___x_649_, 1);
lean_inc(v_val_651_);
lean_dec_ref(v___x_649_);
v___x_652_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_639_, v_key_650_);
lean_dec(v_key_650_);
if (v___x_652_ == 0)
{
lean_object* v___x_653_; 
lean_dec(v_val_651_);
lean_del_object(v___x_642_);
v___x_653_ = lean_box(0);
return v___x_653_;
}
else
{
lean_object* v___x_655_; 
if (v_isShared_643_ == 0)
{
lean_ctor_set_tag(v___x_642_, 1);
lean_ctor_set(v___x_642_, 0, v_val_651_);
v___x_655_ = v___x_642_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v_val_651_);
v___x_655_ = v_reuseFailAlloc_656_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
return v___x_655_;
}
}
}
case 1:
{
lean_object* v_node_657_; size_t v___x_658_; 
lean_del_object(v___x_642_);
v_node_657_ = lean_ctor_get(v___x_649_, 0);
lean_inc(v_node_657_);
lean_dec_ref(v___x_649_);
v___x_658_ = lean_usize_shift_right(v_x_638_, v___x_645_);
v_x_637_ = v_node_657_;
v_x_638_ = v___x_658_;
goto _start;
}
default: 
{
lean_object* v___x_660_; 
lean_del_object(v___x_642_);
v___x_660_ = lean_box(0);
return v___x_660_;
}
}
}
}
else
{
lean_object* v_ks_662_; lean_object* v_vs_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v_ks_662_ = lean_ctor_get(v_x_637_, 0);
lean_inc_ref(v_ks_662_);
v_vs_663_ = lean_ctor_get(v_x_637_, 1);
lean_inc_ref(v_vs_663_);
lean_dec_ref(v_x_637_);
v___x_664_ = lean_unsigned_to_nat(0u);
v___x_665_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_662_, v_vs_663_, v___x_664_, v_x_639_);
lean_dec_ref(v_vs_663_);
lean_dec_ref(v_ks_662_);
return v___x_665_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_666_, lean_object* v_x_667_, lean_object* v_x_668_){
_start:
{
size_t v_x_960__boxed_669_; lean_object* v_res_670_; 
v_x_960__boxed_669_ = lean_unbox_usize(v_x_667_);
lean_dec(v_x_667_);
v_res_670_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg(v_x_666_, v_x_960__boxed_669_, v_x_668_);
lean_dec_ref(v_x_668_);
return v_res_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(lean_object* v_x_671_, lean_object* v_x_672_){
_start:
{
uint64_t v___x_673_; size_t v___x_674_; lean_object* v___x_675_; 
v___x_673_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_672_);
v___x_674_ = lean_uint64_to_usize(v___x_673_);
v___x_675_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg(v_x_671_, v___x_674_, v_x_672_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg___boxed(lean_object* v_x_676_, lean_object* v_x_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(v_x_676_, v_x_677_);
lean_dec_ref(v_x_677_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg(lean_object* v_e_679_, lean_object* v_a_680_, lean_object* v_a_681_){
_start:
{
lean_object* v___x_683_; 
v___x_683_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_680_, v_a_681_);
if (lean_obj_tag(v___x_683_) == 0)
{
lean_object* v_a_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_693_; 
v_a_684_ = lean_ctor_get(v___x_683_, 0);
v_isSharedCheck_693_ = !lean_is_exclusive(v___x_683_);
if (v_isSharedCheck_693_ == 0)
{
v___x_686_ = v___x_683_;
v_isShared_687_ = v_isSharedCheck_693_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_a_684_);
lean_dec(v___x_683_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_693_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v_exprToRingId_688_; lean_object* v___x_689_; lean_object* v___x_691_; 
v_exprToRingId_688_ = lean_ctor_get(v_a_684_, 2);
lean_inc_ref(v_exprToRingId_688_);
lean_dec(v_a_684_);
v___x_689_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(v_exprToRingId_688_, v_e_679_);
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 0, v___x_689_);
v___x_691_ = v___x_686_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v___x_689_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
return v___x_691_;
}
}
}
else
{
lean_object* v_a_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_701_; 
v_a_694_ = lean_ctor_get(v___x_683_, 0);
v_isSharedCheck_701_ = !lean_is_exclusive(v___x_683_);
if (v_isSharedCheck_701_ == 0)
{
v___x_696_ = v___x_683_;
v_isShared_697_ = v_isSharedCheck_701_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_a_694_);
lean_dec(v___x_683_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_701_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_699_; 
if (v_isShared_697_ == 0)
{
v___x_699_ = v___x_696_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_a_694_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg___boxed(lean_object* v_e_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_){
_start:
{
lean_object* v_res_706_; 
v_res_706_ = l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg(v_e_702_, v_a_703_, v_a_704_);
lean_dec_ref(v_a_704_);
lean_dec(v_a_703_);
lean_dec_ref(v_e_702_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f(lean_object* v_e_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_){
_start:
{
lean_object* v___x_719_; 
v___x_719_ = l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg(v_e_707_, v_a_708_, v_a_716_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___boxed(lean_object* v_e_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f(v_e_720_, v_a_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_);
lean_dec(v_a_730_);
lean_dec_ref(v_a_729_);
lean_dec(v_a_728_);
lean_dec_ref(v_a_727_);
lean_dec(v_a_726_);
lean_dec_ref(v_a_725_);
lean_dec(v_a_724_);
lean_dec_ref(v_a_723_);
lean_dec(v_a_722_);
lean_dec(v_a_721_);
lean_dec_ref(v_e_720_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0(lean_object* v_00_u03b2_733_, lean_object* v_x_734_, lean_object* v_x_735_){
_start:
{
lean_object* v___x_736_; 
v___x_736_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(v_x_734_, v_x_735_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___boxed(lean_object* v_00_u03b2_737_, lean_object* v_x_738_, lean_object* v_x_739_){
_start:
{
lean_object* v_res_740_; 
v_res_740_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0(v_00_u03b2_737_, v_x_738_, v_x_739_);
lean_dec_ref(v_x_739_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_741_, lean_object* v_x_742_, size_t v_x_743_, lean_object* v_x_744_){
_start:
{
lean_object* v___x_745_; 
v___x_745_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg(v_x_742_, v_x_743_, v_x_744_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_746_, lean_object* v_x_747_, lean_object* v_x_748_, lean_object* v_x_749_){
_start:
{
size_t v_x_1125__boxed_750_; lean_object* v_res_751_; 
v_x_1125__boxed_750_ = lean_unbox_usize(v_x_748_);
lean_dec(v_x_748_);
v_res_751_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0(v_00_u03b2_746_, v_x_747_, v_x_1125__boxed_750_, v_x_749_);
lean_dec_ref(v_x_749_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_752_, lean_object* v_keys_753_, lean_object* v_vals_754_, lean_object* v_heq_755_, lean_object* v_i_756_, lean_object* v_k_757_){
_start:
{
lean_object* v___x_758_; 
v___x_758_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_753_, v_vals_754_, v_i_756_, v_k_757_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_759_, lean_object* v_keys_760_, lean_object* v_vals_761_, lean_object* v_heq_762_, lean_object* v_i_763_, lean_object* v_k_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_759_, v_keys_760_, v_vals_761_, v_heq_762_, v_i_763_, v_k_764_);
lean_dec_ref(v_k_764_);
lean_dec_ref(v_vals_761_);
lean_dec_ref(v_keys_760_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg___lam__0(lean_object* v_toPure_766_, lean_object* v_____do__lift_767_){
_start:
{
lean_object* v_charInst_x3f_771_; 
v_charInst_x3f_771_ = lean_ctor_get(v_____do__lift_767_, 5);
lean_inc(v_charInst_x3f_771_);
lean_dec_ref(v_____do__lift_767_);
if (lean_obj_tag(v_charInst_x3f_771_) == 1)
{
lean_object* v_val_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_783_; 
v_val_772_ = lean_ctor_get(v_charInst_x3f_771_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v_charInst_x3f_771_);
if (v_isSharedCheck_783_ == 0)
{
v___x_774_ = v_charInst_x3f_771_;
v_isShared_775_ = v_isSharedCheck_783_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_val_772_);
lean_dec(v_charInst_x3f_771_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_783_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v_snd_776_; lean_object* v___x_777_; uint8_t v___x_778_; 
v_snd_776_ = lean_ctor_get(v_val_772_, 1);
lean_inc(v_snd_776_);
lean_dec(v_val_772_);
v___x_777_ = lean_unsigned_to_nat(0u);
v___x_778_ = lean_nat_dec_eq(v_snd_776_, v___x_777_);
if (v___x_778_ == 0)
{
lean_object* v___x_780_; 
if (v_isShared_775_ == 0)
{
lean_ctor_set(v___x_774_, 0, v_snd_776_);
v___x_780_ = v___x_774_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_snd_776_);
v___x_780_ = v_reuseFailAlloc_782_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
lean_object* v___x_781_; 
v___x_781_ = lean_apply_2(v_toPure_766_, lean_box(0), v___x_780_);
return v___x_781_;
}
}
else
{
lean_dec(v_snd_776_);
lean_del_object(v___x_774_);
goto v___jp_768_;
}
}
}
else
{
lean_dec(v_charInst_x3f_771_);
goto v___jp_768_;
}
v___jp_768_:
{
lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_769_ = lean_box(0);
v___x_770_ = lean_apply_2(v_toPure_766_, lean_box(0), v___x_769_);
return v___x_770_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg(lean_object* v_inst_784_, lean_object* v_inst_785_){
_start:
{
lean_object* v_toApplicative_786_; lean_object* v_toBind_787_; lean_object* v_getRing_788_; lean_object* v_toPure_789_; lean_object* v___f_790_; lean_object* v___x_791_; 
v_toApplicative_786_ = lean_ctor_get(v_inst_784_, 0);
lean_inc_ref(v_toApplicative_786_);
v_toBind_787_ = lean_ctor_get(v_inst_784_, 1);
lean_inc(v_toBind_787_);
lean_dec_ref(v_inst_784_);
v_getRing_788_ = lean_ctor_get(v_inst_785_, 0);
lean_inc(v_getRing_788_);
lean_dec_ref(v_inst_785_);
v_toPure_789_ = lean_ctor_get(v_toApplicative_786_, 1);
lean_inc(v_toPure_789_);
lean_dec_ref(v_toApplicative_786_);
v___f_790_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_790_, 0, v_toPure_789_);
v___x_791_ = lean_apply_4(v_toBind_787_, lean_box(0), lean_box(0), v_getRing_788_, v___f_790_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f(lean_object* v_m_792_, lean_object* v_inst_793_, lean_object* v_inst_794_){
_start:
{
lean_object* v___x_795_; 
v___x_795_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg(v_inst_793_, v_inst_794_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f___redArg___lam__0(lean_object* v_toPure_796_, lean_object* v_____do__lift_797_){
_start:
{
lean_object* v_charInst_x3f_801_; 
v_charInst_x3f_801_ = lean_ctor_get(v_____do__lift_797_, 5);
lean_inc(v_charInst_x3f_801_);
lean_dec_ref(v_____do__lift_797_);
if (lean_obj_tag(v_charInst_x3f_801_) == 1)
{
lean_object* v_val_802_; lean_object* v_snd_803_; lean_object* v___x_804_; uint8_t v___x_805_; 
v_val_802_ = lean_ctor_get(v_charInst_x3f_801_, 0);
v_snd_803_ = lean_ctor_get(v_val_802_, 1);
v___x_804_ = lean_unsigned_to_nat(0u);
v___x_805_ = lean_nat_dec_eq(v_snd_803_, v___x_804_);
if (v___x_805_ == 0)
{
lean_object* v___x_806_; 
v___x_806_ = lean_apply_2(v_toPure_796_, lean_box(0), v_charInst_x3f_801_);
return v___x_806_;
}
else
{
lean_dec_ref(v_charInst_x3f_801_);
goto v___jp_798_;
}
}
else
{
lean_dec(v_charInst_x3f_801_);
goto v___jp_798_;
}
v___jp_798_:
{
lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_799_ = lean_box(0);
v___x_800_ = lean_apply_2(v_toPure_796_, lean_box(0), v___x_799_);
return v___x_800_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f___redArg(lean_object* v_inst_807_, lean_object* v_inst_808_){
_start:
{
lean_object* v_toApplicative_809_; lean_object* v_toBind_810_; lean_object* v_getRing_811_; lean_object* v_toPure_812_; lean_object* v___f_813_; lean_object* v___x_814_; 
v_toApplicative_809_ = lean_ctor_get(v_inst_807_, 0);
lean_inc_ref(v_toApplicative_809_);
v_toBind_810_ = lean_ctor_get(v_inst_807_, 1);
lean_inc(v_toBind_810_);
lean_dec_ref(v_inst_807_);
v_getRing_811_ = lean_ctor_get(v_inst_808_, 0);
lean_inc(v_getRing_811_);
lean_dec_ref(v_inst_808_);
v_toPure_812_ = lean_ctor_get(v_toApplicative_809_, 1);
lean_inc(v_toPure_812_);
lean_dec_ref(v_toApplicative_809_);
v___f_813_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_813_, 0, v_toPure_812_);
v___x_814_ = lean_apply_4(v_toBind_810_, lean_box(0), lean_box(0), v_getRing_811_, v___f_813_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f(lean_object* v_m_815_, lean_object* v_inst_816_, lean_object* v_inst_817_){
_start:
{
lean_object* v___x_818_; 
v___x_818_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f___redArg(v_inst_816_, v_inst_817_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisorsInst_x3f(lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_){
_start:
{
lean_object* v___x_831_; 
v___x_831_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_819_, v_a_820_, v_a_821_, v_a_822_, v_a_823_, v_a_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_, v_a_829_);
if (lean_obj_tag(v___x_831_) == 0)
{
lean_object* v_a_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_840_; 
v_a_832_ = lean_ctor_get(v___x_831_, 0);
v_isSharedCheck_840_ = !lean_is_exclusive(v___x_831_);
if (v_isSharedCheck_840_ == 0)
{
v___x_834_ = v___x_831_;
v_isShared_835_ = v_isSharedCheck_840_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_a_832_);
lean_dec(v___x_831_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_840_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v_noZeroDivInst_x3f_836_; lean_object* v___x_838_; 
v_noZeroDivInst_x3f_836_ = lean_ctor_get(v_a_832_, 5);
lean_inc(v_noZeroDivInst_x3f_836_);
lean_dec(v_a_832_);
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 0, v_noZeroDivInst_x3f_836_);
v___x_838_ = v___x_834_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_noZeroDivInst_x3f_836_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
}
else
{
lean_object* v_a_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_848_; 
v_a_841_ = lean_ctor_get(v___x_831_, 0);
v_isSharedCheck_848_ = !lean_is_exclusive(v___x_831_);
if (v_isSharedCheck_848_ == 0)
{
v___x_843_ = v___x_831_;
v_isShared_844_ = v_isSharedCheck_848_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_a_841_);
lean_dec(v___x_831_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_848_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_846_; 
if (v_isShared_844_ == 0)
{
v___x_846_ = v___x_843_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v_a_841_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisorsInst_x3f___boxed(lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisorsInst_x3f(v_a_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_, v_a_858_, v_a_859_);
lean_dec(v_a_859_);
lean_dec_ref(v_a_858_);
lean_dec(v_a_857_);
lean_dec_ref(v_a_856_);
lean_dec(v_a_855_);
lean_dec_ref(v_a_854_);
lean_dec(v_a_853_);
lean_dec_ref(v_a_852_);
lean_dec(v_a_851_);
lean_dec(v_a_850_);
lean_dec_ref(v_a_849_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisors(lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_){
_start:
{
lean_object* v___x_874_; 
v___x_874_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_);
if (lean_obj_tag(v___x_874_) == 0)
{
lean_object* v_a_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_890_; 
v_a_875_ = lean_ctor_get(v___x_874_, 0);
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_874_);
if (v_isSharedCheck_890_ == 0)
{
v___x_877_ = v___x_874_;
v_isShared_878_ = v_isSharedCheck_890_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_a_875_);
lean_dec(v___x_874_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_890_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v_noZeroDivInst_x3f_879_; 
v_noZeroDivInst_x3f_879_ = lean_ctor_get(v_a_875_, 5);
lean_inc(v_noZeroDivInst_x3f_879_);
lean_dec(v_a_875_);
if (lean_obj_tag(v_noZeroDivInst_x3f_879_) == 0)
{
uint8_t v___x_880_; lean_object* v___x_881_; lean_object* v___x_883_; 
v___x_880_ = 0;
v___x_881_ = lean_box(v___x_880_);
if (v_isShared_878_ == 0)
{
lean_ctor_set(v___x_877_, 0, v___x_881_);
v___x_883_ = v___x_877_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v___x_881_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
else
{
uint8_t v___x_885_; lean_object* v___x_886_; lean_object* v___x_888_; 
lean_dec_ref(v_noZeroDivInst_x3f_879_);
v___x_885_ = 1;
v___x_886_ = lean_box(v___x_885_);
if (v_isShared_878_ == 0)
{
lean_ctor_set(v___x_877_, 0, v___x_886_);
v___x_888_ = v___x_877_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v___x_886_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
}
}
else
{
lean_object* v_a_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_898_; 
v_a_891_ = lean_ctor_get(v___x_874_, 0);
v_isSharedCheck_898_ = !lean_is_exclusive(v___x_874_);
if (v_isSharedCheck_898_ == 0)
{
v___x_893_ = v___x_874_;
v_isShared_894_ = v_isSharedCheck_898_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_a_891_);
lean_dec(v___x_874_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_898_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
lean_object* v___x_896_; 
if (v_isShared_894_ == 0)
{
v___x_896_ = v___x_893_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v_a_891_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisors___boxed(lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisors(v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_);
lean_dec(v_a_909_);
lean_dec_ref(v_a_908_);
lean_dec(v_a_907_);
lean_dec_ref(v_a_906_);
lean_dec(v_a_905_);
lean_dec_ref(v_a_904_);
lean_dec(v_a_903_);
lean_dec_ref(v_a_902_);
lean_dec(v_a_901_);
lean_dec(v_a_900_);
lean_dec_ref(v_a_899_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_hasChar(lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_){
_start:
{
lean_object* v___x_924_; 
v___x_924_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_, v_a_918_, v_a_919_, v_a_920_, v_a_921_, v_a_922_);
if (lean_obj_tag(v___x_924_) == 0)
{
lean_object* v_a_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_941_; 
v_a_925_ = lean_ctor_get(v___x_924_, 0);
v_isSharedCheck_941_ = !lean_is_exclusive(v___x_924_);
if (v_isSharedCheck_941_ == 0)
{
v___x_927_ = v___x_924_;
v_isShared_928_ = v_isSharedCheck_941_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_a_925_);
lean_dec(v___x_924_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_941_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v_toRing_929_; lean_object* v_charInst_x3f_930_; 
v_toRing_929_ = lean_ctor_get(v_a_925_, 0);
lean_inc_ref(v_toRing_929_);
lean_dec(v_a_925_);
v_charInst_x3f_930_ = lean_ctor_get(v_toRing_929_, 5);
lean_inc(v_charInst_x3f_930_);
lean_dec_ref(v_toRing_929_);
if (lean_obj_tag(v_charInst_x3f_930_) == 0)
{
uint8_t v___x_931_; lean_object* v___x_932_; lean_object* v___x_934_; 
v___x_931_ = 0;
v___x_932_ = lean_box(v___x_931_);
if (v_isShared_928_ == 0)
{
lean_ctor_set(v___x_927_, 0, v___x_932_);
v___x_934_ = v___x_927_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v___x_932_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
}
}
else
{
uint8_t v___x_936_; lean_object* v___x_937_; lean_object* v___x_939_; 
lean_dec_ref(v_charInst_x3f_930_);
v___x_936_ = 1;
v___x_937_ = lean_box(v___x_936_);
if (v_isShared_928_ == 0)
{
lean_ctor_set(v___x_927_, 0, v___x_937_);
v___x_939_ = v___x_927_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v___x_937_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
return v___x_939_;
}
}
}
}
else
{
lean_object* v_a_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_949_; 
v_a_942_ = lean_ctor_get(v___x_924_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v___x_924_);
if (v_isSharedCheck_949_ == 0)
{
v___x_944_ = v___x_924_;
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_a_942_);
lean_dec(v___x_924_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_947_; 
if (v_isShared_945_ == 0)
{
v___x_947_ = v___x_944_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v_a_942_);
v___x_947_ = v_reuseFailAlloc_948_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
return v___x_947_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_hasChar___boxed(lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l_Lean_Meta_Grind_Arith_CommRing_hasChar(v_a_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_);
lean_dec(v_a_960_);
lean_dec_ref(v_a_959_);
lean_dec(v_a_958_);
lean_dec_ref(v_a_957_);
lean_dec(v_a_956_);
lean_dec_ref(v_a_955_);
lean_dec(v_a_954_);
lean_dec_ref(v_a_953_);
lean_dec(v_a_952_);
lean_dec(v_a_951_);
lean_dec_ref(v_a_950_);
return v_res_962_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__1(void){
_start:
{
lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_964_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__0));
v___x_965_ = l_Lean_stringToMessageData(v___x_964_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCharInst(lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_){
_start:
{
lean_object* v___x_978_; 
v___x_978_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, v_a_976_);
if (lean_obj_tag(v___x_978_) == 0)
{
lean_object* v_a_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_991_; 
v_a_979_ = lean_ctor_get(v___x_978_, 0);
v_isSharedCheck_991_ = !lean_is_exclusive(v___x_978_);
if (v_isSharedCheck_991_ == 0)
{
v___x_981_ = v___x_978_;
v_isShared_982_ = v_isSharedCheck_991_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_a_979_);
lean_dec(v___x_978_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_991_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v_toRing_983_; lean_object* v_charInst_x3f_984_; 
v_toRing_983_ = lean_ctor_get(v_a_979_, 0);
lean_inc_ref(v_toRing_983_);
lean_dec(v_a_979_);
v_charInst_x3f_984_ = lean_ctor_get(v_toRing_983_, 5);
lean_inc(v_charInst_x3f_984_);
lean_dec_ref(v_toRing_983_);
if (lean_obj_tag(v_charInst_x3f_984_) == 1)
{
lean_object* v_val_985_; lean_object* v___x_987_; 
v_val_985_ = lean_ctor_get(v_charInst_x3f_984_, 0);
lean_inc(v_val_985_);
lean_dec_ref(v_charInst_x3f_984_);
if (v_isShared_982_ == 0)
{
lean_ctor_set(v___x_981_, 0, v_val_985_);
v___x_987_ = v___x_981_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v_val_985_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
return v___x_987_;
}
}
else
{
lean_object* v___x_989_; lean_object* v___x_990_; 
lean_dec(v_charInst_x3f_984_);
lean_del_object(v___x_981_);
v___x_989_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__1);
v___x_990_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg(v___x_989_, v_a_973_, v_a_974_, v_a_975_, v_a_976_);
return v___x_990_;
}
}
}
else
{
lean_object* v_a_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_999_; 
v_a_992_ = lean_ctor_get(v___x_978_, 0);
v_isSharedCheck_999_ = !lean_is_exclusive(v___x_978_);
if (v_isSharedCheck_999_ == 0)
{
v___x_994_ = v___x_978_;
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_a_992_);
lean_dec(v___x_978_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v___x_997_; 
if (v_isShared_995_ == 0)
{
v___x_997_ = v___x_994_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v_a_992_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
return v___x_997_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCharInst___boxed(lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l_Lean_Meta_Grind_Arith_CommRing_getCharInst(v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_);
lean_dec(v_a_1010_);
lean_dec_ref(v_a_1009_);
lean_dec(v_a_1008_);
lean_dec_ref(v_a_1007_);
lean_dec(v_a_1006_);
lean_dec_ref(v_a_1005_);
lean_dec(v_a_1004_);
lean_dec_ref(v_a_1003_);
lean_dec(v_a_1002_);
lean_dec(v_a_1001_);
lean_dec_ref(v_a_1000_);
return v_res_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isField(lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_){
_start:
{
lean_object* v___x_1025_; 
v___x_1025_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_);
if (lean_obj_tag(v___x_1025_) == 0)
{
lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1041_; 
v_a_1026_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1041_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1028_ = v___x_1025_;
v_isShared_1029_ = v_isSharedCheck_1041_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v___x_1025_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1041_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v_fieldInst_x3f_1030_; 
v_fieldInst_x3f_1030_ = lean_ctor_get(v_a_1026_, 6);
lean_inc(v_fieldInst_x3f_1030_);
lean_dec(v_a_1026_);
if (lean_obj_tag(v_fieldInst_x3f_1030_) == 0)
{
uint8_t v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1034_; 
v___x_1031_ = 0;
v___x_1032_ = lean_box(v___x_1031_);
if (v_isShared_1029_ == 0)
{
lean_ctor_set(v___x_1028_, 0, v___x_1032_);
v___x_1034_ = v___x_1028_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v___x_1032_);
v___x_1034_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
return v___x_1034_;
}
}
else
{
uint8_t v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1039_; 
lean_dec_ref(v_fieldInst_x3f_1030_);
v___x_1036_ = 1;
v___x_1037_ = lean_box(v___x_1036_);
if (v_isShared_1029_ == 0)
{
lean_ctor_set(v___x_1028_, 0, v___x_1037_);
v___x_1039_ = v___x_1028_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v___x_1037_);
v___x_1039_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
return v___x_1039_;
}
}
}
}
else
{
lean_object* v_a_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1049_; 
v_a_1042_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1044_ = v___x_1025_;
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_a_1042_);
lean_dec(v___x_1025_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1047_; 
if (v_isShared_1045_ == 0)
{
v___x_1047_ = v___x_1044_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_a_1042_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
return v___x_1047_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isField___boxed(lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_){
_start:
{
lean_object* v_res_1062_; 
v_res_1062_ = l_Lean_Meta_Grind_Arith_CommRing_isField(v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_, v_a_1058_, v_a_1059_, v_a_1060_);
lean_dec(v_a_1060_);
lean_dec_ref(v_a_1059_);
lean_dec(v_a_1058_);
lean_dec_ref(v_a_1057_);
lean_dec(v_a_1056_);
lean_dec_ref(v_a_1055_);
lean_dec(v_a_1054_);
lean_dec_ref(v_a_1053_);
lean_dec(v_a_1052_);
lean_dec(v_a_1051_);
lean_dec_ref(v_a_1050_);
return v_res_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty(lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_){
_start:
{
lean_object* v___x_1075_; 
v___x_1075_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_);
if (lean_obj_tag(v___x_1075_) == 0)
{
lean_object* v_a_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1091_; 
v_a_1076_ = lean_ctor_get(v___x_1075_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_1075_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1078_ = v___x_1075_;
v_isShared_1079_ = v_isSharedCheck_1091_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_a_1076_);
lean_dec(v___x_1075_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1091_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v_queue_1080_; 
v_queue_1080_ = lean_ctor_get(v_a_1076_, 10);
lean_inc(v_queue_1080_);
lean_dec(v_a_1076_);
if (lean_obj_tag(v_queue_1080_) == 0)
{
uint8_t v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1084_; 
lean_dec_ref(v_queue_1080_);
v___x_1081_ = 0;
v___x_1082_ = lean_box(v___x_1081_);
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 0, v___x_1082_);
v___x_1084_ = v___x_1078_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v___x_1082_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
return v___x_1084_;
}
}
else
{
uint8_t v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1089_; 
v___x_1086_ = 1;
v___x_1087_ = lean_box(v___x_1086_);
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 0, v___x_1087_);
v___x_1089_ = v___x_1078_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v___x_1087_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
}
}
}
}
else
{
lean_object* v_a_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1099_; 
v_a_1092_ = lean_ctor_get(v___x_1075_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v___x_1075_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1094_ = v___x_1075_;
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_a_1092_);
lean_dec(v___x_1075_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1097_; 
if (v_isShared_1095_ == 0)
{
v___x_1097_ = v___x_1094_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_a_1092_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
return v___x_1097_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty___boxed(lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_){
_start:
{
lean_object* v_res_1112_; 
v_res_1112_ = l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty(v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_);
lean_dec(v_a_1110_);
lean_dec_ref(v_a_1109_);
lean_dec(v_a_1108_);
lean_dec_ref(v_a_1107_);
lean_dec(v_a_1106_);
lean_dec_ref(v_a_1105_);
lean_dec(v_a_1104_);
lean_dec_ref(v_a_1103_);
lean_dec(v_a_1102_);
lean_dec(v_a_1101_);
lean_dec_ref(v_a_1100_);
return v_res_1112_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(lean_object* v_k_1113_, lean_object* v_t_1114_){
_start:
{
if (lean_obj_tag(v_t_1114_) == 0)
{
lean_object* v_k_1115_; lean_object* v_v_1116_; lean_object* v_l_1117_; lean_object* v_r_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1772_; 
v_k_1115_ = lean_ctor_get(v_t_1114_, 1);
v_v_1116_ = lean_ctor_get(v_t_1114_, 2);
v_l_1117_ = lean_ctor_get(v_t_1114_, 3);
v_r_1118_ = lean_ctor_get(v_t_1114_, 4);
v_isSharedCheck_1772_ = !lean_is_exclusive(v_t_1114_);
if (v_isSharedCheck_1772_ == 0)
{
lean_object* v_unused_1773_; 
v_unused_1773_ = lean_ctor_get(v_t_1114_, 0);
lean_dec(v_unused_1773_);
v___x_1120_ = v_t_1114_;
v_isShared_1121_ = v_isSharedCheck_1772_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_r_1118_);
lean_inc(v_l_1117_);
lean_inc(v_v_1116_);
lean_inc(v_k_1115_);
lean_dec(v_t_1114_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1772_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
uint8_t v___x_1122_; 
v___x_1122_ = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_compare(v_k_1113_, v_k_1115_);
switch(v___x_1122_)
{
case 0:
{
lean_object* v_impl_1123_; lean_object* v___x_1124_; 
v_impl_1123_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_k_1113_, v_l_1117_);
v___x_1124_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1123_) == 0)
{
if (lean_obj_tag(v_r_1118_) == 0)
{
lean_object* v_size_1125_; lean_object* v_size_1126_; lean_object* v_k_1127_; lean_object* v_v_1128_; lean_object* v_l_1129_; lean_object* v_r_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; uint8_t v___x_1133_; 
v_size_1125_ = lean_ctor_get(v_impl_1123_, 0);
lean_inc(v_size_1125_);
v_size_1126_ = lean_ctor_get(v_r_1118_, 0);
v_k_1127_ = lean_ctor_get(v_r_1118_, 1);
v_v_1128_ = lean_ctor_get(v_r_1118_, 2);
v_l_1129_ = lean_ctor_get(v_r_1118_, 3);
lean_inc(v_l_1129_);
v_r_1130_ = lean_ctor_get(v_r_1118_, 4);
v___x_1131_ = lean_unsigned_to_nat(3u);
v___x_1132_ = lean_nat_mul(v___x_1131_, v_size_1125_);
v___x_1133_ = lean_nat_dec_lt(v___x_1132_, v_size_1126_);
lean_dec(v___x_1132_);
if (v___x_1133_ == 0)
{
lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1137_; 
lean_dec(v_l_1129_);
v___x_1134_ = lean_nat_add(v___x_1124_, v_size_1125_);
lean_dec(v_size_1125_);
v___x_1135_ = lean_nat_add(v___x_1134_, v_size_1126_);
lean_dec(v___x_1134_);
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 3, v_impl_1123_);
lean_ctor_set(v___x_1120_, 0, v___x_1135_);
v___x_1137_ = v___x_1120_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v___x_1135_);
lean_ctor_set(v_reuseFailAlloc_1138_, 1, v_k_1115_);
lean_ctor_set(v_reuseFailAlloc_1138_, 2, v_v_1116_);
lean_ctor_set(v_reuseFailAlloc_1138_, 3, v_impl_1123_);
lean_ctor_set(v_reuseFailAlloc_1138_, 4, v_r_1118_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
else
{
lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1202_; 
lean_inc(v_r_1130_);
lean_inc(v_v_1128_);
lean_inc(v_k_1127_);
lean_inc(v_size_1126_);
v_isSharedCheck_1202_ = !lean_is_exclusive(v_r_1118_);
if (v_isSharedCheck_1202_ == 0)
{
lean_object* v_unused_1203_; lean_object* v_unused_1204_; lean_object* v_unused_1205_; lean_object* v_unused_1206_; lean_object* v_unused_1207_; 
v_unused_1203_ = lean_ctor_get(v_r_1118_, 4);
lean_dec(v_unused_1203_);
v_unused_1204_ = lean_ctor_get(v_r_1118_, 3);
lean_dec(v_unused_1204_);
v_unused_1205_ = lean_ctor_get(v_r_1118_, 2);
lean_dec(v_unused_1205_);
v_unused_1206_ = lean_ctor_get(v_r_1118_, 1);
lean_dec(v_unused_1206_);
v_unused_1207_ = lean_ctor_get(v_r_1118_, 0);
lean_dec(v_unused_1207_);
v___x_1140_ = v_r_1118_;
v_isShared_1141_ = v_isSharedCheck_1202_;
goto v_resetjp_1139_;
}
else
{
lean_dec(v_r_1118_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1202_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v_size_1142_; lean_object* v_k_1143_; lean_object* v_v_1144_; lean_object* v_l_1145_; lean_object* v_r_1146_; lean_object* v_size_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; uint8_t v___x_1150_; 
v_size_1142_ = lean_ctor_get(v_l_1129_, 0);
v_k_1143_ = lean_ctor_get(v_l_1129_, 1);
v_v_1144_ = lean_ctor_get(v_l_1129_, 2);
v_l_1145_ = lean_ctor_get(v_l_1129_, 3);
v_r_1146_ = lean_ctor_get(v_l_1129_, 4);
v_size_1147_ = lean_ctor_get(v_r_1130_, 0);
v___x_1148_ = lean_unsigned_to_nat(2u);
v___x_1149_ = lean_nat_mul(v___x_1148_, v_size_1147_);
v___x_1150_ = lean_nat_dec_lt(v_size_1142_, v___x_1149_);
lean_dec(v___x_1149_);
if (v___x_1150_ == 0)
{
lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1178_; 
lean_inc(v_r_1146_);
lean_inc(v_l_1145_);
lean_inc(v_v_1144_);
lean_inc(v_k_1143_);
v_isSharedCheck_1178_ = !lean_is_exclusive(v_l_1129_);
if (v_isSharedCheck_1178_ == 0)
{
lean_object* v_unused_1179_; lean_object* v_unused_1180_; lean_object* v_unused_1181_; lean_object* v_unused_1182_; lean_object* v_unused_1183_; 
v_unused_1179_ = lean_ctor_get(v_l_1129_, 4);
lean_dec(v_unused_1179_);
v_unused_1180_ = lean_ctor_get(v_l_1129_, 3);
lean_dec(v_unused_1180_);
v_unused_1181_ = lean_ctor_get(v_l_1129_, 2);
lean_dec(v_unused_1181_);
v_unused_1182_ = lean_ctor_get(v_l_1129_, 1);
lean_dec(v_unused_1182_);
v_unused_1183_ = lean_ctor_get(v_l_1129_, 0);
lean_dec(v_unused_1183_);
v___x_1152_ = v_l_1129_;
v_isShared_1153_ = v_isSharedCheck_1178_;
goto v_resetjp_1151_;
}
else
{
lean_dec(v_l_1129_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1178_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___y_1157_; lean_object* v___y_1158_; lean_object* v___y_1159_; lean_object* v___y_1168_; 
v___x_1154_ = lean_nat_add(v___x_1124_, v_size_1125_);
lean_dec(v_size_1125_);
v___x_1155_ = lean_nat_add(v___x_1154_, v_size_1126_);
lean_dec(v_size_1126_);
if (lean_obj_tag(v_l_1145_) == 0)
{
lean_object* v_size_1176_; 
v_size_1176_ = lean_ctor_get(v_l_1145_, 0);
lean_inc(v_size_1176_);
v___y_1168_ = v_size_1176_;
goto v___jp_1167_;
}
else
{
lean_object* v___x_1177_; 
v___x_1177_ = lean_unsigned_to_nat(0u);
v___y_1168_ = v___x_1177_;
goto v___jp_1167_;
}
v___jp_1156_:
{
lean_object* v___x_1160_; lean_object* v___x_1162_; 
v___x_1160_ = lean_nat_add(v___y_1158_, v___y_1159_);
lean_dec(v___y_1159_);
lean_dec(v___y_1158_);
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 4, v_r_1130_);
lean_ctor_set(v___x_1152_, 3, v_r_1146_);
lean_ctor_set(v___x_1152_, 2, v_v_1128_);
lean_ctor_set(v___x_1152_, 1, v_k_1127_);
lean_ctor_set(v___x_1152_, 0, v___x_1160_);
v___x_1162_ = v___x_1152_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v___x_1160_);
lean_ctor_set(v_reuseFailAlloc_1166_, 1, v_k_1127_);
lean_ctor_set(v_reuseFailAlloc_1166_, 2, v_v_1128_);
lean_ctor_set(v_reuseFailAlloc_1166_, 3, v_r_1146_);
lean_ctor_set(v_reuseFailAlloc_1166_, 4, v_r_1130_);
v___x_1162_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
lean_object* v___x_1164_; 
if (v_isShared_1141_ == 0)
{
lean_ctor_set(v___x_1140_, 4, v___x_1162_);
lean_ctor_set(v___x_1140_, 3, v___y_1157_);
lean_ctor_set(v___x_1140_, 2, v_v_1144_);
lean_ctor_set(v___x_1140_, 1, v_k_1143_);
lean_ctor_set(v___x_1140_, 0, v___x_1155_);
v___x_1164_ = v___x_1140_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v___x_1155_);
lean_ctor_set(v_reuseFailAlloc_1165_, 1, v_k_1143_);
lean_ctor_set(v_reuseFailAlloc_1165_, 2, v_v_1144_);
lean_ctor_set(v_reuseFailAlloc_1165_, 3, v___y_1157_);
lean_ctor_set(v_reuseFailAlloc_1165_, 4, v___x_1162_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
return v___x_1164_;
}
}
}
v___jp_1167_:
{
lean_object* v___x_1169_; lean_object* v___x_1171_; 
v___x_1169_ = lean_nat_add(v___x_1154_, v___y_1168_);
lean_dec(v___y_1168_);
lean_dec(v___x_1154_);
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 4, v_l_1145_);
lean_ctor_set(v___x_1120_, 3, v_impl_1123_);
lean_ctor_set(v___x_1120_, 0, v___x_1169_);
v___x_1171_ = v___x_1120_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v___x_1169_);
lean_ctor_set(v_reuseFailAlloc_1175_, 1, v_k_1115_);
lean_ctor_set(v_reuseFailAlloc_1175_, 2, v_v_1116_);
lean_ctor_set(v_reuseFailAlloc_1175_, 3, v_impl_1123_);
lean_ctor_set(v_reuseFailAlloc_1175_, 4, v_l_1145_);
v___x_1171_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
lean_object* v___x_1172_; 
v___x_1172_ = lean_nat_add(v___x_1124_, v_size_1147_);
if (lean_obj_tag(v_r_1146_) == 0)
{
lean_object* v_size_1173_; 
v_size_1173_ = lean_ctor_get(v_r_1146_, 0);
lean_inc(v_size_1173_);
v___y_1157_ = v___x_1171_;
v___y_1158_ = v___x_1172_;
v___y_1159_ = v_size_1173_;
goto v___jp_1156_;
}
else
{
lean_object* v___x_1174_; 
v___x_1174_ = lean_unsigned_to_nat(0u);
v___y_1157_ = v___x_1171_;
v___y_1158_ = v___x_1172_;
v___y_1159_ = v___x_1174_;
goto v___jp_1156_;
}
}
}
}
}
else
{
lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1188_; 
lean_del_object(v___x_1120_);
v___x_1184_ = lean_nat_add(v___x_1124_, v_size_1125_);
lean_dec(v_size_1125_);
v___x_1185_ = lean_nat_add(v___x_1184_, v_size_1126_);
lean_dec(v_size_1126_);
v___x_1186_ = lean_nat_add(v___x_1184_, v_size_1142_);
lean_dec(v___x_1184_);
lean_inc_ref(v_impl_1123_);
if (v_isShared_1141_ == 0)
{
lean_ctor_set(v___x_1140_, 4, v_l_1129_);
lean_ctor_set(v___x_1140_, 3, v_impl_1123_);
lean_ctor_set(v___x_1140_, 2, v_v_1116_);
lean_ctor_set(v___x_1140_, 1, v_k_1115_);
lean_ctor_set(v___x_1140_, 0, v___x_1186_);
v___x_1188_ = v___x_1140_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v___x_1186_);
lean_ctor_set(v_reuseFailAlloc_1201_, 1, v_k_1115_);
lean_ctor_set(v_reuseFailAlloc_1201_, 2, v_v_1116_);
lean_ctor_set(v_reuseFailAlloc_1201_, 3, v_impl_1123_);
lean_ctor_set(v_reuseFailAlloc_1201_, 4, v_l_1129_);
v___x_1188_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1195_; 
v_isSharedCheck_1195_ = !lean_is_exclusive(v_impl_1123_);
if (v_isSharedCheck_1195_ == 0)
{
lean_object* v_unused_1196_; lean_object* v_unused_1197_; lean_object* v_unused_1198_; lean_object* v_unused_1199_; lean_object* v_unused_1200_; 
v_unused_1196_ = lean_ctor_get(v_impl_1123_, 4);
lean_dec(v_unused_1196_);
v_unused_1197_ = lean_ctor_get(v_impl_1123_, 3);
lean_dec(v_unused_1197_);
v_unused_1198_ = lean_ctor_get(v_impl_1123_, 2);
lean_dec(v_unused_1198_);
v_unused_1199_ = lean_ctor_get(v_impl_1123_, 1);
lean_dec(v_unused_1199_);
v_unused_1200_ = lean_ctor_get(v_impl_1123_, 0);
lean_dec(v_unused_1200_);
v___x_1190_ = v_impl_1123_;
v_isShared_1191_ = v_isSharedCheck_1195_;
goto v_resetjp_1189_;
}
else
{
lean_dec(v_impl_1123_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1195_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v___x_1193_; 
if (v_isShared_1191_ == 0)
{
lean_ctor_set(v___x_1190_, 4, v_r_1130_);
lean_ctor_set(v___x_1190_, 3, v___x_1188_);
lean_ctor_set(v___x_1190_, 2, v_v_1128_);
lean_ctor_set(v___x_1190_, 1, v_k_1127_);
lean_ctor_set(v___x_1190_, 0, v___x_1185_);
v___x_1193_ = v___x_1190_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v___x_1185_);
lean_ctor_set(v_reuseFailAlloc_1194_, 1, v_k_1127_);
lean_ctor_set(v_reuseFailAlloc_1194_, 2, v_v_1128_);
lean_ctor_set(v_reuseFailAlloc_1194_, 3, v___x_1188_);
lean_ctor_set(v_reuseFailAlloc_1194_, 4, v_r_1130_);
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
}
}
}
else
{
lean_object* v_size_1208_; lean_object* v___x_1209_; lean_object* v___x_1211_; 
v_size_1208_ = lean_ctor_get(v_impl_1123_, 0);
lean_inc(v_size_1208_);
v___x_1209_ = lean_nat_add(v___x_1124_, v_size_1208_);
lean_dec(v_size_1208_);
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 3, v_impl_1123_);
lean_ctor_set(v___x_1120_, 0, v___x_1209_);
v___x_1211_ = v___x_1120_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v___x_1209_);
lean_ctor_set(v_reuseFailAlloc_1212_, 1, v_k_1115_);
lean_ctor_set(v_reuseFailAlloc_1212_, 2, v_v_1116_);
lean_ctor_set(v_reuseFailAlloc_1212_, 3, v_impl_1123_);
lean_ctor_set(v_reuseFailAlloc_1212_, 4, v_r_1118_);
v___x_1211_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
return v___x_1211_;
}
}
}
else
{
if (lean_obj_tag(v_r_1118_) == 0)
{
lean_object* v_l_1213_; 
v_l_1213_ = lean_ctor_get(v_r_1118_, 3);
lean_inc(v_l_1213_);
if (lean_obj_tag(v_l_1213_) == 0)
{
lean_object* v_r_1214_; 
v_r_1214_ = lean_ctor_get(v_r_1118_, 4);
lean_inc(v_r_1214_);
if (lean_obj_tag(v_r_1214_) == 0)
{
lean_object* v_size_1215_; lean_object* v_k_1216_; lean_object* v_v_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1230_; 
v_size_1215_ = lean_ctor_get(v_r_1118_, 0);
v_k_1216_ = lean_ctor_get(v_r_1118_, 1);
v_v_1217_ = lean_ctor_get(v_r_1118_, 2);
v_isSharedCheck_1230_ = !lean_is_exclusive(v_r_1118_);
if (v_isSharedCheck_1230_ == 0)
{
lean_object* v_unused_1231_; lean_object* v_unused_1232_; 
v_unused_1231_ = lean_ctor_get(v_r_1118_, 4);
lean_dec(v_unused_1231_);
v_unused_1232_ = lean_ctor_get(v_r_1118_, 3);
lean_dec(v_unused_1232_);
v___x_1219_ = v_r_1118_;
v_isShared_1220_ = v_isSharedCheck_1230_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_v_1217_);
lean_inc(v_k_1216_);
lean_inc(v_size_1215_);
lean_dec(v_r_1118_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1230_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v_size_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1225_; 
v_size_1221_ = lean_ctor_get(v_l_1213_, 0);
v___x_1222_ = lean_nat_add(v___x_1124_, v_size_1215_);
lean_dec(v_size_1215_);
v___x_1223_ = lean_nat_add(v___x_1124_, v_size_1221_);
if (v_isShared_1220_ == 0)
{
lean_ctor_set(v___x_1219_, 4, v_l_1213_);
lean_ctor_set(v___x_1219_, 3, v_impl_1123_);
lean_ctor_set(v___x_1219_, 2, v_v_1116_);
lean_ctor_set(v___x_1219_, 1, v_k_1115_);
lean_ctor_set(v___x_1219_, 0, v___x_1223_);
v___x_1225_ = v___x_1219_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v___x_1223_);
lean_ctor_set(v_reuseFailAlloc_1229_, 1, v_k_1115_);
lean_ctor_set(v_reuseFailAlloc_1229_, 2, v_v_1116_);
lean_ctor_set(v_reuseFailAlloc_1229_, 3, v_impl_1123_);
lean_ctor_set(v_reuseFailAlloc_1229_, 4, v_l_1213_);
v___x_1225_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
lean_object* v___x_1227_; 
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 4, v_r_1214_);
lean_ctor_set(v___x_1120_, 3, v___x_1225_);
lean_ctor_set(v___x_1120_, 2, v_v_1217_);
lean_ctor_set(v___x_1120_, 1, v_k_1216_);
lean_ctor_set(v___x_1120_, 0, v___x_1222_);
v___x_1227_ = v___x_1120_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v___x_1222_);
lean_ctor_set(v_reuseFailAlloc_1228_, 1, v_k_1216_);
lean_ctor_set(v_reuseFailAlloc_1228_, 2, v_v_1217_);
lean_ctor_set(v_reuseFailAlloc_1228_, 3, v___x_1225_);
lean_ctor_set(v_reuseFailAlloc_1228_, 4, v_r_1214_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
return v___x_1227_;
}
}
}
}
else
{
lean_object* v_k_1233_; lean_object* v_v_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1257_; 
v_k_1233_ = lean_ctor_get(v_r_1118_, 1);
v_v_1234_ = lean_ctor_get(v_r_1118_, 2);
v_isSharedCheck_1257_ = !lean_is_exclusive(v_r_1118_);
if (v_isSharedCheck_1257_ == 0)
{
lean_object* v_unused_1258_; lean_object* v_unused_1259_; lean_object* v_unused_1260_; 
v_unused_1258_ = lean_ctor_get(v_r_1118_, 4);
lean_dec(v_unused_1258_);
v_unused_1259_ = lean_ctor_get(v_r_1118_, 3);
lean_dec(v_unused_1259_);
v_unused_1260_ = lean_ctor_get(v_r_1118_, 0);
lean_dec(v_unused_1260_);
v___x_1236_ = v_r_1118_;
v_isShared_1237_ = v_isSharedCheck_1257_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_v_1234_);
lean_inc(v_k_1233_);
lean_dec(v_r_1118_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1257_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v_k_1238_; lean_object* v_v_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1253_; 
v_k_1238_ = lean_ctor_get(v_l_1213_, 1);
v_v_1239_ = lean_ctor_get(v_l_1213_, 2);
v_isSharedCheck_1253_ = !lean_is_exclusive(v_l_1213_);
if (v_isSharedCheck_1253_ == 0)
{
lean_object* v_unused_1254_; lean_object* v_unused_1255_; lean_object* v_unused_1256_; 
v_unused_1254_ = lean_ctor_get(v_l_1213_, 4);
lean_dec(v_unused_1254_);
v_unused_1255_ = lean_ctor_get(v_l_1213_, 3);
lean_dec(v_unused_1255_);
v_unused_1256_ = lean_ctor_get(v_l_1213_, 0);
lean_dec(v_unused_1256_);
v___x_1241_ = v_l_1213_;
v_isShared_1242_ = v_isSharedCheck_1253_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_v_1239_);
lean_inc(v_k_1238_);
lean_dec(v_l_1213_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1253_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v___x_1243_; lean_object* v___x_1245_; 
v___x_1243_ = lean_unsigned_to_nat(3u);
if (v_isShared_1242_ == 0)
{
lean_ctor_set(v___x_1241_, 4, v_r_1214_);
lean_ctor_set(v___x_1241_, 3, v_r_1214_);
lean_ctor_set(v___x_1241_, 2, v_v_1116_);
lean_ctor_set(v___x_1241_, 1, v_k_1115_);
lean_ctor_set(v___x_1241_, 0, v___x_1124_);
v___x_1245_ = v___x_1241_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v___x_1124_);
lean_ctor_set(v_reuseFailAlloc_1252_, 1, v_k_1115_);
lean_ctor_set(v_reuseFailAlloc_1252_, 2, v_v_1116_);
lean_ctor_set(v_reuseFailAlloc_1252_, 3, v_r_1214_);
lean_ctor_set(v_reuseFailAlloc_1252_, 4, v_r_1214_);
v___x_1245_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
lean_object* v___x_1247_; 
if (v_isShared_1237_ == 0)
{
lean_ctor_set(v___x_1236_, 3, v_r_1214_);
lean_ctor_set(v___x_1236_, 0, v___x_1124_);
v___x_1247_ = v___x_1236_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v___x_1124_);
lean_ctor_set(v_reuseFailAlloc_1251_, 1, v_k_1233_);
lean_ctor_set(v_reuseFailAlloc_1251_, 2, v_v_1234_);
lean_ctor_set(v_reuseFailAlloc_1251_, 3, v_r_1214_);
lean_ctor_set(v_reuseFailAlloc_1251_, 4, v_r_1214_);
v___x_1247_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
lean_object* v___x_1249_; 
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 4, v___x_1247_);
lean_ctor_set(v___x_1120_, 3, v___x_1245_);
lean_ctor_set(v___x_1120_, 2, v_v_1239_);
lean_ctor_set(v___x_1120_, 1, v_k_1238_);
lean_ctor_set(v___x_1120_, 0, v___x_1243_);
v___x_1249_ = v___x_1120_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v___x_1243_);
lean_ctor_set(v_reuseFailAlloc_1250_, 1, v_k_1238_);
lean_ctor_set(v_reuseFailAlloc_1250_, 2, v_v_1239_);
lean_ctor_set(v_reuseFailAlloc_1250_, 3, v___x_1245_);
lean_ctor_set(v_reuseFailAlloc_1250_, 4, v___x_1247_);
v___x_1249_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
return v___x_1249_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_1261_; 
v_r_1261_ = lean_ctor_get(v_r_1118_, 4);
lean_inc(v_r_1261_);
if (lean_obj_tag(v_r_1261_) == 0)
{
lean_object* v_k_1262_; lean_object* v_v_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1274_; 
v_k_1262_ = lean_ctor_get(v_r_1118_, 1);
v_v_1263_ = lean_ctor_get(v_r_1118_, 2);
v_isSharedCheck_1274_ = !lean_is_exclusive(v_r_1118_);
if (v_isSharedCheck_1274_ == 0)
{
lean_object* v_unused_1275_; lean_object* v_unused_1276_; lean_object* v_unused_1277_; 
v_unused_1275_ = lean_ctor_get(v_r_1118_, 4);
lean_dec(v_unused_1275_);
v_unused_1276_ = lean_ctor_get(v_r_1118_, 3);
lean_dec(v_unused_1276_);
v_unused_1277_ = lean_ctor_get(v_r_1118_, 0);
lean_dec(v_unused_1277_);
v___x_1265_ = v_r_1118_;
v_isShared_1266_ = v_isSharedCheck_1274_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_v_1263_);
lean_inc(v_k_1262_);
lean_dec(v_r_1118_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1274_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v___x_1267_; lean_object* v___x_1269_; 
v___x_1267_ = lean_unsigned_to_nat(3u);
if (v_isShared_1266_ == 0)
{
lean_ctor_set(v___x_1265_, 4, v_l_1213_);
lean_ctor_set(v___x_1265_, 2, v_v_1116_);
lean_ctor_set(v___x_1265_, 1, v_k_1115_);
lean_ctor_set(v___x_1265_, 0, v___x_1124_);
v___x_1269_ = v___x_1265_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v___x_1124_);
lean_ctor_set(v_reuseFailAlloc_1273_, 1, v_k_1115_);
lean_ctor_set(v_reuseFailAlloc_1273_, 2, v_v_1116_);
lean_ctor_set(v_reuseFailAlloc_1273_, 3, v_l_1213_);
lean_ctor_set(v_reuseFailAlloc_1273_, 4, v_l_1213_);
v___x_1269_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
lean_object* v___x_1271_; 
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 4, v_r_1261_);
lean_ctor_set(v___x_1120_, 3, v___x_1269_);
lean_ctor_set(v___x_1120_, 2, v_v_1263_);
lean_ctor_set(v___x_1120_, 1, v_k_1262_);
lean_ctor_set(v___x_1120_, 0, v___x_1267_);
v___x_1271_ = v___x_1120_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v___x_1267_);
lean_ctor_set(v_reuseFailAlloc_1272_, 1, v_k_1262_);
lean_ctor_set(v_reuseFailAlloc_1272_, 2, v_v_1263_);
lean_ctor_set(v_reuseFailAlloc_1272_, 3, v___x_1269_);
lean_ctor_set(v_reuseFailAlloc_1272_, 4, v_r_1261_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
}
else
{
lean_object* v_size_1278_; lean_object* v_k_1279_; lean_object* v_v_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1291_; 
v_size_1278_ = lean_ctor_get(v_r_1118_, 0);
v_k_1279_ = lean_ctor_get(v_r_1118_, 1);
v_v_1280_ = lean_ctor_get(v_r_1118_, 2);
v_isSharedCheck_1291_ = !lean_is_exclusive(v_r_1118_);
if (v_isSharedCheck_1291_ == 0)
{
lean_object* v_unused_1292_; lean_object* v_unused_1293_; 
v_unused_1292_ = lean_ctor_get(v_r_1118_, 4);
lean_dec(v_unused_1292_);
v_unused_1293_ = lean_ctor_get(v_r_1118_, 3);
lean_dec(v_unused_1293_);
v___x_1282_ = v_r_1118_;
v_isShared_1283_ = v_isSharedCheck_1291_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_v_1280_);
lean_inc(v_k_1279_);
lean_inc(v_size_1278_);
lean_dec(v_r_1118_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1291_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v___x_1285_; 
if (v_isShared_1283_ == 0)
{
lean_ctor_set(v___x_1282_, 3, v_r_1261_);
v___x_1285_ = v___x_1282_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_size_1278_);
lean_ctor_set(v_reuseFailAlloc_1290_, 1, v_k_1279_);
lean_ctor_set(v_reuseFailAlloc_1290_, 2, v_v_1280_);
lean_ctor_set(v_reuseFailAlloc_1290_, 3, v_r_1261_);
lean_ctor_set(v_reuseFailAlloc_1290_, 4, v_r_1261_);
v___x_1285_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
lean_object* v___x_1286_; lean_object* v___x_1288_; 
v___x_1286_ = lean_unsigned_to_nat(2u);
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 4, v___x_1285_);
lean_ctor_set(v___x_1120_, 3, v_r_1261_);
lean_ctor_set(v___x_1120_, 0, v___x_1286_);
v___x_1288_ = v___x_1120_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v___x_1286_);
lean_ctor_set(v_reuseFailAlloc_1289_, 1, v_k_1115_);
lean_ctor_set(v_reuseFailAlloc_1289_, 2, v_v_1116_);
lean_ctor_set(v_reuseFailAlloc_1289_, 3, v_r_1261_);
lean_ctor_set(v_reuseFailAlloc_1289_, 4, v___x_1285_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
return v___x_1288_;
}
}
}
}
}
}
else
{
lean_object* v___x_1295_; 
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 3, v_r_1118_);
lean_ctor_set(v___x_1120_, 0, v___x_1124_);
v___x_1295_ = v___x_1120_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v___x_1124_);
lean_ctor_set(v_reuseFailAlloc_1296_, 1, v_k_1115_);
lean_ctor_set(v_reuseFailAlloc_1296_, 2, v_v_1116_);
lean_ctor_set(v_reuseFailAlloc_1296_, 3, v_r_1118_);
lean_ctor_set(v_reuseFailAlloc_1296_, 4, v_r_1118_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
}
}
case 1:
{
lean_del_object(v___x_1120_);
lean_dec(v_v_1116_);
lean_dec(v_k_1115_);
if (lean_obj_tag(v_l_1117_) == 0)
{
if (lean_obj_tag(v_r_1118_) == 0)
{
lean_object* v_size_1297_; lean_object* v_k_1298_; lean_object* v_v_1299_; lean_object* v_l_1300_; lean_object* v_r_1301_; lean_object* v_size_1302_; lean_object* v_k_1303_; lean_object* v_v_1304_; lean_object* v_l_1305_; lean_object* v_r_1306_; lean_object* v___x_1307_; uint8_t v___x_1308_; 
v_size_1297_ = lean_ctor_get(v_l_1117_, 0);
v_k_1298_ = lean_ctor_get(v_l_1117_, 1);
v_v_1299_ = lean_ctor_get(v_l_1117_, 2);
v_l_1300_ = lean_ctor_get(v_l_1117_, 3);
v_r_1301_ = lean_ctor_get(v_l_1117_, 4);
lean_inc(v_r_1301_);
v_size_1302_ = lean_ctor_get(v_r_1118_, 0);
v_k_1303_ = lean_ctor_get(v_r_1118_, 1);
v_v_1304_ = lean_ctor_get(v_r_1118_, 2);
v_l_1305_ = lean_ctor_get(v_r_1118_, 3);
lean_inc(v_l_1305_);
v_r_1306_ = lean_ctor_get(v_r_1118_, 4);
v___x_1307_ = lean_unsigned_to_nat(1u);
v___x_1308_ = lean_nat_dec_lt(v_size_1297_, v_size_1302_);
if (v___x_1308_ == 0)
{
lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1444_; 
lean_inc(v_l_1300_);
lean_inc(v_v_1299_);
lean_inc(v_k_1298_);
v_isSharedCheck_1444_ = !lean_is_exclusive(v_l_1117_);
if (v_isSharedCheck_1444_ == 0)
{
lean_object* v_unused_1445_; lean_object* v_unused_1446_; lean_object* v_unused_1447_; lean_object* v_unused_1448_; lean_object* v_unused_1449_; 
v_unused_1445_ = lean_ctor_get(v_l_1117_, 4);
lean_dec(v_unused_1445_);
v_unused_1446_ = lean_ctor_get(v_l_1117_, 3);
lean_dec(v_unused_1446_);
v_unused_1447_ = lean_ctor_get(v_l_1117_, 2);
lean_dec(v_unused_1447_);
v_unused_1448_ = lean_ctor_get(v_l_1117_, 1);
lean_dec(v_unused_1448_);
v_unused_1449_ = lean_ctor_get(v_l_1117_, 0);
lean_dec(v_unused_1449_);
v___x_1310_ = v_l_1117_;
v_isShared_1311_ = v_isSharedCheck_1444_;
goto v_resetjp_1309_;
}
else
{
lean_dec(v_l_1117_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1444_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
lean_object* v___x_1312_; lean_object* v_tree_1313_; 
v___x_1312_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_1298_, v_v_1299_, v_l_1300_, v_r_1301_);
v_tree_1313_ = lean_ctor_get(v___x_1312_, 2);
lean_inc(v_tree_1313_);
if (lean_obj_tag(v_tree_1313_) == 0)
{
lean_object* v_k_1314_; lean_object* v_v_1315_; lean_object* v_size_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; uint8_t v___x_1319_; 
v_k_1314_ = lean_ctor_get(v___x_1312_, 0);
lean_inc(v_k_1314_);
v_v_1315_ = lean_ctor_get(v___x_1312_, 1);
lean_inc(v_v_1315_);
lean_dec_ref(v___x_1312_);
v_size_1316_ = lean_ctor_get(v_tree_1313_, 0);
v___x_1317_ = lean_unsigned_to_nat(3u);
v___x_1318_ = lean_nat_mul(v___x_1317_, v_size_1316_);
v___x_1319_ = lean_nat_dec_lt(v___x_1318_, v_size_1302_);
lean_dec(v___x_1318_);
if (v___x_1319_ == 0)
{
lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1323_; 
lean_dec(v_l_1305_);
v___x_1320_ = lean_nat_add(v___x_1307_, v_size_1316_);
v___x_1321_ = lean_nat_add(v___x_1320_, v_size_1302_);
lean_dec(v___x_1320_);
if (v_isShared_1311_ == 0)
{
lean_ctor_set(v___x_1310_, 4, v_r_1118_);
lean_ctor_set(v___x_1310_, 3, v_tree_1313_);
lean_ctor_set(v___x_1310_, 2, v_v_1315_);
lean_ctor_set(v___x_1310_, 1, v_k_1314_);
lean_ctor_set(v___x_1310_, 0, v___x_1321_);
v___x_1323_ = v___x_1310_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v___x_1321_);
lean_ctor_set(v_reuseFailAlloc_1324_, 1, v_k_1314_);
lean_ctor_set(v_reuseFailAlloc_1324_, 2, v_v_1315_);
lean_ctor_set(v_reuseFailAlloc_1324_, 3, v_tree_1313_);
lean_ctor_set(v_reuseFailAlloc_1324_, 4, v_r_1118_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
return v___x_1323_;
}
}
else
{
lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1379_; 
lean_inc(v_r_1306_);
lean_inc(v_v_1304_);
lean_inc(v_k_1303_);
lean_inc(v_size_1302_);
v_isSharedCheck_1379_ = !lean_is_exclusive(v_r_1118_);
if (v_isSharedCheck_1379_ == 0)
{
lean_object* v_unused_1380_; lean_object* v_unused_1381_; lean_object* v_unused_1382_; lean_object* v_unused_1383_; lean_object* v_unused_1384_; 
v_unused_1380_ = lean_ctor_get(v_r_1118_, 4);
lean_dec(v_unused_1380_);
v_unused_1381_ = lean_ctor_get(v_r_1118_, 3);
lean_dec(v_unused_1381_);
v_unused_1382_ = lean_ctor_get(v_r_1118_, 2);
lean_dec(v_unused_1382_);
v_unused_1383_ = lean_ctor_get(v_r_1118_, 1);
lean_dec(v_unused_1383_);
v_unused_1384_ = lean_ctor_get(v_r_1118_, 0);
lean_dec(v_unused_1384_);
v___x_1326_ = v_r_1118_;
v_isShared_1327_ = v_isSharedCheck_1379_;
goto v_resetjp_1325_;
}
else
{
lean_dec(v_r_1118_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1379_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v_size_1328_; lean_object* v_k_1329_; lean_object* v_v_1330_; lean_object* v_l_1331_; lean_object* v_r_1332_; lean_object* v_size_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; uint8_t v___x_1336_; 
v_size_1328_ = lean_ctor_get(v_l_1305_, 0);
v_k_1329_ = lean_ctor_get(v_l_1305_, 1);
v_v_1330_ = lean_ctor_get(v_l_1305_, 2);
v_l_1331_ = lean_ctor_get(v_l_1305_, 3);
v_r_1332_ = lean_ctor_get(v_l_1305_, 4);
v_size_1333_ = lean_ctor_get(v_r_1306_, 0);
v___x_1334_ = lean_unsigned_to_nat(2u);
v___x_1335_ = lean_nat_mul(v___x_1334_, v_size_1333_);
v___x_1336_ = lean_nat_dec_lt(v_size_1328_, v___x_1335_);
lean_dec(v___x_1335_);
if (v___x_1336_ == 0)
{
lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1364_; 
lean_inc(v_r_1332_);
lean_inc(v_l_1331_);
lean_inc(v_v_1330_);
lean_inc(v_k_1329_);
v_isSharedCheck_1364_ = !lean_is_exclusive(v_l_1305_);
if (v_isSharedCheck_1364_ == 0)
{
lean_object* v_unused_1365_; lean_object* v_unused_1366_; lean_object* v_unused_1367_; lean_object* v_unused_1368_; lean_object* v_unused_1369_; 
v_unused_1365_ = lean_ctor_get(v_l_1305_, 4);
lean_dec(v_unused_1365_);
v_unused_1366_ = lean_ctor_get(v_l_1305_, 3);
lean_dec(v_unused_1366_);
v_unused_1367_ = lean_ctor_get(v_l_1305_, 2);
lean_dec(v_unused_1367_);
v_unused_1368_ = lean_ctor_get(v_l_1305_, 1);
lean_dec(v_unused_1368_);
v_unused_1369_ = lean_ctor_get(v_l_1305_, 0);
lean_dec(v_unused_1369_);
v___x_1338_ = v_l_1305_;
v_isShared_1339_ = v_isSharedCheck_1364_;
goto v_resetjp_1337_;
}
else
{
lean_dec(v_l_1305_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1364_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___y_1343_; lean_object* v___y_1344_; lean_object* v___y_1345_; lean_object* v___y_1354_; 
v___x_1340_ = lean_nat_add(v___x_1307_, v_size_1316_);
v___x_1341_ = lean_nat_add(v___x_1340_, v_size_1302_);
lean_dec(v_size_1302_);
if (lean_obj_tag(v_l_1331_) == 0)
{
lean_object* v_size_1362_; 
v_size_1362_ = lean_ctor_get(v_l_1331_, 0);
lean_inc(v_size_1362_);
v___y_1354_ = v_size_1362_;
goto v___jp_1353_;
}
else
{
lean_object* v___x_1363_; 
v___x_1363_ = lean_unsigned_to_nat(0u);
v___y_1354_ = v___x_1363_;
goto v___jp_1353_;
}
v___jp_1342_:
{
lean_object* v___x_1346_; lean_object* v___x_1348_; 
v___x_1346_ = lean_nat_add(v___y_1344_, v___y_1345_);
lean_dec(v___y_1345_);
lean_dec(v___y_1344_);
if (v_isShared_1339_ == 0)
{
lean_ctor_set(v___x_1338_, 4, v_r_1306_);
lean_ctor_set(v___x_1338_, 3, v_r_1332_);
lean_ctor_set(v___x_1338_, 2, v_v_1304_);
lean_ctor_set(v___x_1338_, 1, v_k_1303_);
lean_ctor_set(v___x_1338_, 0, v___x_1346_);
v___x_1348_ = v___x_1338_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v___x_1346_);
lean_ctor_set(v_reuseFailAlloc_1352_, 1, v_k_1303_);
lean_ctor_set(v_reuseFailAlloc_1352_, 2, v_v_1304_);
lean_ctor_set(v_reuseFailAlloc_1352_, 3, v_r_1332_);
lean_ctor_set(v_reuseFailAlloc_1352_, 4, v_r_1306_);
v___x_1348_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
lean_object* v___x_1350_; 
if (v_isShared_1327_ == 0)
{
lean_ctor_set(v___x_1326_, 4, v___x_1348_);
lean_ctor_set(v___x_1326_, 3, v___y_1343_);
lean_ctor_set(v___x_1326_, 2, v_v_1330_);
lean_ctor_set(v___x_1326_, 1, v_k_1329_);
lean_ctor_set(v___x_1326_, 0, v___x_1341_);
v___x_1350_ = v___x_1326_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v___x_1341_);
lean_ctor_set(v_reuseFailAlloc_1351_, 1, v_k_1329_);
lean_ctor_set(v_reuseFailAlloc_1351_, 2, v_v_1330_);
lean_ctor_set(v_reuseFailAlloc_1351_, 3, v___y_1343_);
lean_ctor_set(v_reuseFailAlloc_1351_, 4, v___x_1348_);
v___x_1350_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
return v___x_1350_;
}
}
}
v___jp_1353_:
{
lean_object* v___x_1355_; lean_object* v___x_1357_; 
v___x_1355_ = lean_nat_add(v___x_1340_, v___y_1354_);
lean_dec(v___y_1354_);
lean_dec(v___x_1340_);
if (v_isShared_1311_ == 0)
{
lean_ctor_set(v___x_1310_, 4, v_l_1331_);
lean_ctor_set(v___x_1310_, 3, v_tree_1313_);
lean_ctor_set(v___x_1310_, 2, v_v_1315_);
lean_ctor_set(v___x_1310_, 1, v_k_1314_);
lean_ctor_set(v___x_1310_, 0, v___x_1355_);
v___x_1357_ = v___x_1310_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v___x_1355_);
lean_ctor_set(v_reuseFailAlloc_1361_, 1, v_k_1314_);
lean_ctor_set(v_reuseFailAlloc_1361_, 2, v_v_1315_);
lean_ctor_set(v_reuseFailAlloc_1361_, 3, v_tree_1313_);
lean_ctor_set(v_reuseFailAlloc_1361_, 4, v_l_1331_);
v___x_1357_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
lean_object* v___x_1358_; 
v___x_1358_ = lean_nat_add(v___x_1307_, v_size_1333_);
if (lean_obj_tag(v_r_1332_) == 0)
{
lean_object* v_size_1359_; 
v_size_1359_ = lean_ctor_get(v_r_1332_, 0);
lean_inc(v_size_1359_);
v___y_1343_ = v___x_1357_;
v___y_1344_ = v___x_1358_;
v___y_1345_ = v_size_1359_;
goto v___jp_1342_;
}
else
{
lean_object* v___x_1360_; 
v___x_1360_ = lean_unsigned_to_nat(0u);
v___y_1343_ = v___x_1357_;
v___y_1344_ = v___x_1358_;
v___y_1345_ = v___x_1360_;
goto v___jp_1342_;
}
}
}
}
}
else
{
lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1374_; 
v___x_1370_ = lean_nat_add(v___x_1307_, v_size_1316_);
v___x_1371_ = lean_nat_add(v___x_1370_, v_size_1302_);
lean_dec(v_size_1302_);
v___x_1372_ = lean_nat_add(v___x_1370_, v_size_1328_);
lean_dec(v___x_1370_);
if (v_isShared_1327_ == 0)
{
lean_ctor_set(v___x_1326_, 4, v_l_1305_);
lean_ctor_set(v___x_1326_, 3, v_tree_1313_);
lean_ctor_set(v___x_1326_, 2, v_v_1315_);
lean_ctor_set(v___x_1326_, 1, v_k_1314_);
lean_ctor_set(v___x_1326_, 0, v___x_1372_);
v___x_1374_ = v___x_1326_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v___x_1372_);
lean_ctor_set(v_reuseFailAlloc_1378_, 1, v_k_1314_);
lean_ctor_set(v_reuseFailAlloc_1378_, 2, v_v_1315_);
lean_ctor_set(v_reuseFailAlloc_1378_, 3, v_tree_1313_);
lean_ctor_set(v_reuseFailAlloc_1378_, 4, v_l_1305_);
v___x_1374_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
lean_object* v___x_1376_; 
if (v_isShared_1311_ == 0)
{
lean_ctor_set(v___x_1310_, 4, v_r_1306_);
lean_ctor_set(v___x_1310_, 3, v___x_1374_);
lean_ctor_set(v___x_1310_, 2, v_v_1304_);
lean_ctor_set(v___x_1310_, 1, v_k_1303_);
lean_ctor_set(v___x_1310_, 0, v___x_1371_);
v___x_1376_ = v___x_1310_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v___x_1371_);
lean_ctor_set(v_reuseFailAlloc_1377_, 1, v_k_1303_);
lean_ctor_set(v_reuseFailAlloc_1377_, 2, v_v_1304_);
lean_ctor_set(v_reuseFailAlloc_1377_, 3, v___x_1374_);
lean_ctor_set(v_reuseFailAlloc_1377_, 4, v_r_1306_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
}
}
}
else
{
lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1438_; 
lean_inc(v_r_1306_);
lean_inc(v_v_1304_);
lean_inc(v_k_1303_);
lean_inc(v_size_1302_);
v_isSharedCheck_1438_ = !lean_is_exclusive(v_r_1118_);
if (v_isSharedCheck_1438_ == 0)
{
lean_object* v_unused_1439_; lean_object* v_unused_1440_; lean_object* v_unused_1441_; lean_object* v_unused_1442_; lean_object* v_unused_1443_; 
v_unused_1439_ = lean_ctor_get(v_r_1118_, 4);
lean_dec(v_unused_1439_);
v_unused_1440_ = lean_ctor_get(v_r_1118_, 3);
lean_dec(v_unused_1440_);
v_unused_1441_ = lean_ctor_get(v_r_1118_, 2);
lean_dec(v_unused_1441_);
v_unused_1442_ = lean_ctor_get(v_r_1118_, 1);
lean_dec(v_unused_1442_);
v_unused_1443_ = lean_ctor_get(v_r_1118_, 0);
lean_dec(v_unused_1443_);
v___x_1386_ = v_r_1118_;
v_isShared_1387_ = v_isSharedCheck_1438_;
goto v_resetjp_1385_;
}
else
{
lean_dec(v_r_1118_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1438_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
if (lean_obj_tag(v_l_1305_) == 0)
{
if (lean_obj_tag(v_r_1306_) == 0)
{
lean_object* v_k_1388_; lean_object* v_v_1389_; lean_object* v_size_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1394_; 
v_k_1388_ = lean_ctor_get(v___x_1312_, 0);
lean_inc(v_k_1388_);
v_v_1389_ = lean_ctor_get(v___x_1312_, 1);
lean_inc(v_v_1389_);
lean_dec_ref(v___x_1312_);
v_size_1390_ = lean_ctor_get(v_l_1305_, 0);
v___x_1391_ = lean_nat_add(v___x_1307_, v_size_1302_);
lean_dec(v_size_1302_);
v___x_1392_ = lean_nat_add(v___x_1307_, v_size_1390_);
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 4, v_l_1305_);
lean_ctor_set(v___x_1386_, 3, v_tree_1313_);
lean_ctor_set(v___x_1386_, 2, v_v_1389_);
lean_ctor_set(v___x_1386_, 1, v_k_1388_);
lean_ctor_set(v___x_1386_, 0, v___x_1392_);
v___x_1394_ = v___x_1386_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v___x_1392_);
lean_ctor_set(v_reuseFailAlloc_1398_, 1, v_k_1388_);
lean_ctor_set(v_reuseFailAlloc_1398_, 2, v_v_1389_);
lean_ctor_set(v_reuseFailAlloc_1398_, 3, v_tree_1313_);
lean_ctor_set(v_reuseFailAlloc_1398_, 4, v_l_1305_);
v___x_1394_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
lean_object* v___x_1396_; 
if (v_isShared_1311_ == 0)
{
lean_ctor_set(v___x_1310_, 4, v_r_1306_);
lean_ctor_set(v___x_1310_, 3, v___x_1394_);
lean_ctor_set(v___x_1310_, 2, v_v_1304_);
lean_ctor_set(v___x_1310_, 1, v_k_1303_);
lean_ctor_set(v___x_1310_, 0, v___x_1391_);
v___x_1396_ = v___x_1310_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v___x_1391_);
lean_ctor_set(v_reuseFailAlloc_1397_, 1, v_k_1303_);
lean_ctor_set(v_reuseFailAlloc_1397_, 2, v_v_1304_);
lean_ctor_set(v_reuseFailAlloc_1397_, 3, v___x_1394_);
lean_ctor_set(v_reuseFailAlloc_1397_, 4, v_r_1306_);
v___x_1396_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
return v___x_1396_;
}
}
}
else
{
lean_object* v_k_1399_; lean_object* v_v_1400_; lean_object* v_k_1401_; lean_object* v_v_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1416_; 
lean_dec(v_size_1302_);
v_k_1399_ = lean_ctor_get(v___x_1312_, 0);
lean_inc(v_k_1399_);
v_v_1400_ = lean_ctor_get(v___x_1312_, 1);
lean_inc(v_v_1400_);
lean_dec_ref(v___x_1312_);
v_k_1401_ = lean_ctor_get(v_l_1305_, 1);
v_v_1402_ = lean_ctor_get(v_l_1305_, 2);
v_isSharedCheck_1416_ = !lean_is_exclusive(v_l_1305_);
if (v_isSharedCheck_1416_ == 0)
{
lean_object* v_unused_1417_; lean_object* v_unused_1418_; lean_object* v_unused_1419_; 
v_unused_1417_ = lean_ctor_get(v_l_1305_, 4);
lean_dec(v_unused_1417_);
v_unused_1418_ = lean_ctor_get(v_l_1305_, 3);
lean_dec(v_unused_1418_);
v_unused_1419_ = lean_ctor_get(v_l_1305_, 0);
lean_dec(v_unused_1419_);
v___x_1404_ = v_l_1305_;
v_isShared_1405_ = v_isSharedCheck_1416_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_v_1402_);
lean_inc(v_k_1401_);
lean_dec(v_l_1305_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1416_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v___x_1406_; lean_object* v___x_1408_; 
v___x_1406_ = lean_unsigned_to_nat(3u);
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 4, v_r_1306_);
lean_ctor_set(v___x_1404_, 3, v_r_1306_);
lean_ctor_set(v___x_1404_, 2, v_v_1400_);
lean_ctor_set(v___x_1404_, 1, v_k_1399_);
lean_ctor_set(v___x_1404_, 0, v___x_1307_);
v___x_1408_ = v___x_1404_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v___x_1307_);
lean_ctor_set(v_reuseFailAlloc_1415_, 1, v_k_1399_);
lean_ctor_set(v_reuseFailAlloc_1415_, 2, v_v_1400_);
lean_ctor_set(v_reuseFailAlloc_1415_, 3, v_r_1306_);
lean_ctor_set(v_reuseFailAlloc_1415_, 4, v_r_1306_);
v___x_1408_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
lean_object* v___x_1410_; 
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 3, v_r_1306_);
lean_ctor_set(v___x_1386_, 0, v___x_1307_);
v___x_1410_ = v___x_1386_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v___x_1307_);
lean_ctor_set(v_reuseFailAlloc_1414_, 1, v_k_1303_);
lean_ctor_set(v_reuseFailAlloc_1414_, 2, v_v_1304_);
lean_ctor_set(v_reuseFailAlloc_1414_, 3, v_r_1306_);
lean_ctor_set(v_reuseFailAlloc_1414_, 4, v_r_1306_);
v___x_1410_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
lean_object* v___x_1412_; 
if (v_isShared_1311_ == 0)
{
lean_ctor_set(v___x_1310_, 4, v___x_1410_);
lean_ctor_set(v___x_1310_, 3, v___x_1408_);
lean_ctor_set(v___x_1310_, 2, v_v_1402_);
lean_ctor_set(v___x_1310_, 1, v_k_1401_);
lean_ctor_set(v___x_1310_, 0, v___x_1406_);
v___x_1412_ = v___x_1310_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v___x_1406_);
lean_ctor_set(v_reuseFailAlloc_1413_, 1, v_k_1401_);
lean_ctor_set(v_reuseFailAlloc_1413_, 2, v_v_1402_);
lean_ctor_set(v_reuseFailAlloc_1413_, 3, v___x_1408_);
lean_ctor_set(v_reuseFailAlloc_1413_, 4, v___x_1410_);
v___x_1412_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
return v___x_1412_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1306_) == 0)
{
lean_object* v_k_1420_; lean_object* v_v_1421_; lean_object* v___x_1422_; lean_object* v___x_1424_; 
lean_dec(v_size_1302_);
v_k_1420_ = lean_ctor_get(v___x_1312_, 0);
lean_inc(v_k_1420_);
v_v_1421_ = lean_ctor_get(v___x_1312_, 1);
lean_inc(v_v_1421_);
lean_dec_ref(v___x_1312_);
v___x_1422_ = lean_unsigned_to_nat(3u);
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 4, v_l_1305_);
lean_ctor_set(v___x_1386_, 2, v_v_1421_);
lean_ctor_set(v___x_1386_, 1, v_k_1420_);
lean_ctor_set(v___x_1386_, 0, v___x_1307_);
v___x_1424_ = v___x_1386_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v___x_1307_);
lean_ctor_set(v_reuseFailAlloc_1428_, 1, v_k_1420_);
lean_ctor_set(v_reuseFailAlloc_1428_, 2, v_v_1421_);
lean_ctor_set(v_reuseFailAlloc_1428_, 3, v_l_1305_);
lean_ctor_set(v_reuseFailAlloc_1428_, 4, v_l_1305_);
v___x_1424_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
lean_object* v___x_1426_; 
if (v_isShared_1311_ == 0)
{
lean_ctor_set(v___x_1310_, 4, v_r_1306_);
lean_ctor_set(v___x_1310_, 3, v___x_1424_);
lean_ctor_set(v___x_1310_, 2, v_v_1304_);
lean_ctor_set(v___x_1310_, 1, v_k_1303_);
lean_ctor_set(v___x_1310_, 0, v___x_1422_);
v___x_1426_ = v___x_1310_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v___x_1422_);
lean_ctor_set(v_reuseFailAlloc_1427_, 1, v_k_1303_);
lean_ctor_set(v_reuseFailAlloc_1427_, 2, v_v_1304_);
lean_ctor_set(v_reuseFailAlloc_1427_, 3, v___x_1424_);
lean_ctor_set(v_reuseFailAlloc_1427_, 4, v_r_1306_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
return v___x_1426_;
}
}
}
else
{
lean_object* v_k_1429_; lean_object* v_v_1430_; lean_object* v___x_1432_; 
v_k_1429_ = lean_ctor_get(v___x_1312_, 0);
lean_inc(v_k_1429_);
v_v_1430_ = lean_ctor_get(v___x_1312_, 1);
lean_inc(v_v_1430_);
lean_dec_ref(v___x_1312_);
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 3, v_r_1306_);
v___x_1432_ = v___x_1386_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v_size_1302_);
lean_ctor_set(v_reuseFailAlloc_1437_, 1, v_k_1303_);
lean_ctor_set(v_reuseFailAlloc_1437_, 2, v_v_1304_);
lean_ctor_set(v_reuseFailAlloc_1437_, 3, v_r_1306_);
lean_ctor_set(v_reuseFailAlloc_1437_, 4, v_r_1306_);
v___x_1432_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
lean_object* v___x_1433_; lean_object* v___x_1435_; 
v___x_1433_ = lean_unsigned_to_nat(2u);
if (v_isShared_1311_ == 0)
{
lean_ctor_set(v___x_1310_, 4, v___x_1432_);
lean_ctor_set(v___x_1310_, 3, v_r_1306_);
lean_ctor_set(v___x_1310_, 2, v_v_1430_);
lean_ctor_set(v___x_1310_, 1, v_k_1429_);
lean_ctor_set(v___x_1310_, 0, v___x_1433_);
v___x_1435_ = v___x_1310_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v___x_1433_);
lean_ctor_set(v_reuseFailAlloc_1436_, 1, v_k_1429_);
lean_ctor_set(v_reuseFailAlloc_1436_, 2, v_v_1430_);
lean_ctor_set(v_reuseFailAlloc_1436_, 3, v_r_1306_);
lean_ctor_set(v_reuseFailAlloc_1436_, 4, v___x_1432_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1602_; 
lean_inc(v_r_1306_);
lean_inc(v_v_1304_);
lean_inc(v_k_1303_);
v_isSharedCheck_1602_ = !lean_is_exclusive(v_r_1118_);
if (v_isSharedCheck_1602_ == 0)
{
lean_object* v_unused_1603_; lean_object* v_unused_1604_; lean_object* v_unused_1605_; lean_object* v_unused_1606_; lean_object* v_unused_1607_; 
v_unused_1603_ = lean_ctor_get(v_r_1118_, 4);
lean_dec(v_unused_1603_);
v_unused_1604_ = lean_ctor_get(v_r_1118_, 3);
lean_dec(v_unused_1604_);
v_unused_1605_ = lean_ctor_get(v_r_1118_, 2);
lean_dec(v_unused_1605_);
v_unused_1606_ = lean_ctor_get(v_r_1118_, 1);
lean_dec(v_unused_1606_);
v_unused_1607_ = lean_ctor_get(v_r_1118_, 0);
lean_dec(v_unused_1607_);
v___x_1451_ = v_r_1118_;
v_isShared_1452_ = v_isSharedCheck_1602_;
goto v_resetjp_1450_;
}
else
{
lean_dec(v_r_1118_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1602_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1453_; lean_object* v_tree_1454_; 
v___x_1453_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_1303_, v_v_1304_, v_l_1305_, v_r_1306_);
v_tree_1454_ = lean_ctor_get(v___x_1453_, 2);
lean_inc(v_tree_1454_);
if (lean_obj_tag(v_tree_1454_) == 0)
{
lean_object* v_k_1455_; lean_object* v_v_1456_; lean_object* v_size_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; uint8_t v___x_1460_; 
v_k_1455_ = lean_ctor_get(v___x_1453_, 0);
lean_inc(v_k_1455_);
v_v_1456_ = lean_ctor_get(v___x_1453_, 1);
lean_inc(v_v_1456_);
lean_dec_ref(v___x_1453_);
v_size_1457_ = lean_ctor_get(v_tree_1454_, 0);
v___x_1458_ = lean_unsigned_to_nat(3u);
v___x_1459_ = lean_nat_mul(v___x_1458_, v_size_1457_);
v___x_1460_ = lean_nat_dec_lt(v___x_1459_, v_size_1297_);
lean_dec(v___x_1459_);
if (v___x_1460_ == 0)
{
lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1464_; 
lean_dec(v_r_1301_);
v___x_1461_ = lean_nat_add(v___x_1307_, v_size_1297_);
v___x_1462_ = lean_nat_add(v___x_1461_, v_size_1457_);
lean_dec(v___x_1461_);
if (v_isShared_1452_ == 0)
{
lean_ctor_set(v___x_1451_, 4, v_tree_1454_);
lean_ctor_set(v___x_1451_, 3, v_l_1117_);
lean_ctor_set(v___x_1451_, 2, v_v_1456_);
lean_ctor_set(v___x_1451_, 1, v_k_1455_);
lean_ctor_set(v___x_1451_, 0, v___x_1462_);
v___x_1464_ = v___x_1451_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v___x_1462_);
lean_ctor_set(v_reuseFailAlloc_1465_, 1, v_k_1455_);
lean_ctor_set(v_reuseFailAlloc_1465_, 2, v_v_1456_);
lean_ctor_set(v_reuseFailAlloc_1465_, 3, v_l_1117_);
lean_ctor_set(v_reuseFailAlloc_1465_, 4, v_tree_1454_);
v___x_1464_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
return v___x_1464_;
}
}
else
{
lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1531_; 
lean_inc(v_l_1300_);
lean_inc(v_v_1299_);
lean_inc(v_k_1298_);
lean_inc(v_size_1297_);
v_isSharedCheck_1531_ = !lean_is_exclusive(v_l_1117_);
if (v_isSharedCheck_1531_ == 0)
{
lean_object* v_unused_1532_; lean_object* v_unused_1533_; lean_object* v_unused_1534_; lean_object* v_unused_1535_; lean_object* v_unused_1536_; 
v_unused_1532_ = lean_ctor_get(v_l_1117_, 4);
lean_dec(v_unused_1532_);
v_unused_1533_ = lean_ctor_get(v_l_1117_, 3);
lean_dec(v_unused_1533_);
v_unused_1534_ = lean_ctor_get(v_l_1117_, 2);
lean_dec(v_unused_1534_);
v_unused_1535_ = lean_ctor_get(v_l_1117_, 1);
lean_dec(v_unused_1535_);
v_unused_1536_ = lean_ctor_get(v_l_1117_, 0);
lean_dec(v_unused_1536_);
v___x_1467_ = v_l_1117_;
v_isShared_1468_ = v_isSharedCheck_1531_;
goto v_resetjp_1466_;
}
else
{
lean_dec(v_l_1117_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1531_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v_size_1469_; lean_object* v_size_1470_; lean_object* v_k_1471_; lean_object* v_v_1472_; lean_object* v_l_1473_; lean_object* v_r_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; uint8_t v___x_1477_; 
v_size_1469_ = lean_ctor_get(v_l_1300_, 0);
v_size_1470_ = lean_ctor_get(v_r_1301_, 0);
v_k_1471_ = lean_ctor_get(v_r_1301_, 1);
v_v_1472_ = lean_ctor_get(v_r_1301_, 2);
v_l_1473_ = lean_ctor_get(v_r_1301_, 3);
v_r_1474_ = lean_ctor_get(v_r_1301_, 4);
v___x_1475_ = lean_unsigned_to_nat(2u);
v___x_1476_ = lean_nat_mul(v___x_1475_, v_size_1469_);
v___x_1477_ = lean_nat_dec_lt(v_size_1470_, v___x_1476_);
lean_dec(v___x_1476_);
if (v___x_1477_ == 0)
{
lean_object* v___x_1479_; uint8_t v_isShared_1480_; uint8_t v_isSharedCheck_1515_; 
lean_inc(v_r_1474_);
lean_inc(v_l_1473_);
lean_inc(v_v_1472_);
lean_inc(v_k_1471_);
lean_del_object(v___x_1467_);
v_isSharedCheck_1515_ = !lean_is_exclusive(v_r_1301_);
if (v_isSharedCheck_1515_ == 0)
{
lean_object* v_unused_1516_; lean_object* v_unused_1517_; lean_object* v_unused_1518_; lean_object* v_unused_1519_; lean_object* v_unused_1520_; 
v_unused_1516_ = lean_ctor_get(v_r_1301_, 4);
lean_dec(v_unused_1516_);
v_unused_1517_ = lean_ctor_get(v_r_1301_, 3);
lean_dec(v_unused_1517_);
v_unused_1518_ = lean_ctor_get(v_r_1301_, 2);
lean_dec(v_unused_1518_);
v_unused_1519_ = lean_ctor_get(v_r_1301_, 1);
lean_dec(v_unused_1519_);
v_unused_1520_ = lean_ctor_get(v_r_1301_, 0);
lean_dec(v_unused_1520_);
v___x_1479_ = v_r_1301_;
v_isShared_1480_ = v_isSharedCheck_1515_;
goto v_resetjp_1478_;
}
else
{
lean_dec(v_r_1301_);
v___x_1479_ = lean_box(0);
v_isShared_1480_ = v_isSharedCheck_1515_;
goto v_resetjp_1478_;
}
v_resetjp_1478_:
{
lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___y_1484_; lean_object* v___y_1485_; lean_object* v___y_1486_; lean_object* v___x_1503_; lean_object* v___y_1505_; 
v___x_1481_ = lean_nat_add(v___x_1307_, v_size_1297_);
lean_dec(v_size_1297_);
v___x_1482_ = lean_nat_add(v___x_1481_, v_size_1457_);
lean_dec(v___x_1481_);
v___x_1503_ = lean_nat_add(v___x_1307_, v_size_1469_);
if (lean_obj_tag(v_l_1473_) == 0)
{
lean_object* v_size_1513_; 
v_size_1513_ = lean_ctor_get(v_l_1473_, 0);
lean_inc(v_size_1513_);
v___y_1505_ = v_size_1513_;
goto v___jp_1504_;
}
else
{
lean_object* v___x_1514_; 
v___x_1514_ = lean_unsigned_to_nat(0u);
v___y_1505_ = v___x_1514_;
goto v___jp_1504_;
}
v___jp_1483_:
{
lean_object* v___x_1487_; lean_object* v___x_1489_; 
v___x_1487_ = lean_nat_add(v___y_1485_, v___y_1486_);
lean_dec(v___y_1486_);
lean_dec(v___y_1485_);
lean_inc_ref(v_tree_1454_);
if (v_isShared_1480_ == 0)
{
lean_ctor_set(v___x_1479_, 4, v_tree_1454_);
lean_ctor_set(v___x_1479_, 3, v_r_1474_);
lean_ctor_set(v___x_1479_, 2, v_v_1456_);
lean_ctor_set(v___x_1479_, 1, v_k_1455_);
lean_ctor_set(v___x_1479_, 0, v___x_1487_);
v___x_1489_ = v___x_1479_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v___x_1487_);
lean_ctor_set(v_reuseFailAlloc_1502_, 1, v_k_1455_);
lean_ctor_set(v_reuseFailAlloc_1502_, 2, v_v_1456_);
lean_ctor_set(v_reuseFailAlloc_1502_, 3, v_r_1474_);
lean_ctor_set(v_reuseFailAlloc_1502_, 4, v_tree_1454_);
v___x_1489_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1496_; 
v_isSharedCheck_1496_ = !lean_is_exclusive(v_tree_1454_);
if (v_isSharedCheck_1496_ == 0)
{
lean_object* v_unused_1497_; lean_object* v_unused_1498_; lean_object* v_unused_1499_; lean_object* v_unused_1500_; lean_object* v_unused_1501_; 
v_unused_1497_ = lean_ctor_get(v_tree_1454_, 4);
lean_dec(v_unused_1497_);
v_unused_1498_ = lean_ctor_get(v_tree_1454_, 3);
lean_dec(v_unused_1498_);
v_unused_1499_ = lean_ctor_get(v_tree_1454_, 2);
lean_dec(v_unused_1499_);
v_unused_1500_ = lean_ctor_get(v_tree_1454_, 1);
lean_dec(v_unused_1500_);
v_unused_1501_ = lean_ctor_get(v_tree_1454_, 0);
lean_dec(v_unused_1501_);
v___x_1491_ = v_tree_1454_;
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
else
{
lean_dec(v_tree_1454_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v___x_1494_; 
if (v_isShared_1492_ == 0)
{
lean_ctor_set(v___x_1491_, 4, v___x_1489_);
lean_ctor_set(v___x_1491_, 3, v___y_1484_);
lean_ctor_set(v___x_1491_, 2, v_v_1472_);
lean_ctor_set(v___x_1491_, 1, v_k_1471_);
lean_ctor_set(v___x_1491_, 0, v___x_1482_);
v___x_1494_ = v___x_1491_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v___x_1482_);
lean_ctor_set(v_reuseFailAlloc_1495_, 1, v_k_1471_);
lean_ctor_set(v_reuseFailAlloc_1495_, 2, v_v_1472_);
lean_ctor_set(v_reuseFailAlloc_1495_, 3, v___y_1484_);
lean_ctor_set(v_reuseFailAlloc_1495_, 4, v___x_1489_);
v___x_1494_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
return v___x_1494_;
}
}
}
}
v___jp_1504_:
{
lean_object* v___x_1506_; lean_object* v___x_1508_; 
v___x_1506_ = lean_nat_add(v___x_1503_, v___y_1505_);
lean_dec(v___y_1505_);
lean_dec(v___x_1503_);
if (v_isShared_1452_ == 0)
{
lean_ctor_set(v___x_1451_, 4, v_l_1473_);
lean_ctor_set(v___x_1451_, 3, v_l_1300_);
lean_ctor_set(v___x_1451_, 2, v_v_1299_);
lean_ctor_set(v___x_1451_, 1, v_k_1298_);
lean_ctor_set(v___x_1451_, 0, v___x_1506_);
v___x_1508_ = v___x_1451_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v___x_1506_);
lean_ctor_set(v_reuseFailAlloc_1512_, 1, v_k_1298_);
lean_ctor_set(v_reuseFailAlloc_1512_, 2, v_v_1299_);
lean_ctor_set(v_reuseFailAlloc_1512_, 3, v_l_1300_);
lean_ctor_set(v_reuseFailAlloc_1512_, 4, v_l_1473_);
v___x_1508_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
lean_object* v___x_1509_; 
v___x_1509_ = lean_nat_add(v___x_1307_, v_size_1457_);
if (lean_obj_tag(v_r_1474_) == 0)
{
lean_object* v_size_1510_; 
v_size_1510_ = lean_ctor_get(v_r_1474_, 0);
lean_inc(v_size_1510_);
v___y_1484_ = v___x_1508_;
v___y_1485_ = v___x_1509_;
v___y_1486_ = v_size_1510_;
goto v___jp_1483_;
}
else
{
lean_object* v___x_1511_; 
v___x_1511_ = lean_unsigned_to_nat(0u);
v___y_1484_ = v___x_1508_;
v___y_1485_ = v___x_1509_;
v___y_1486_ = v___x_1511_;
goto v___jp_1483_;
}
}
}
}
}
else
{
lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1526_; 
v___x_1521_ = lean_nat_add(v___x_1307_, v_size_1297_);
lean_dec(v_size_1297_);
v___x_1522_ = lean_nat_add(v___x_1521_, v_size_1457_);
lean_dec(v___x_1521_);
v___x_1523_ = lean_nat_add(v___x_1307_, v_size_1457_);
v___x_1524_ = lean_nat_add(v___x_1523_, v_size_1470_);
lean_dec(v___x_1523_);
if (v_isShared_1452_ == 0)
{
lean_ctor_set(v___x_1451_, 4, v_tree_1454_);
lean_ctor_set(v___x_1451_, 3, v_r_1301_);
lean_ctor_set(v___x_1451_, 2, v_v_1456_);
lean_ctor_set(v___x_1451_, 1, v_k_1455_);
lean_ctor_set(v___x_1451_, 0, v___x_1524_);
v___x_1526_ = v___x_1451_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v___x_1524_);
lean_ctor_set(v_reuseFailAlloc_1530_, 1, v_k_1455_);
lean_ctor_set(v_reuseFailAlloc_1530_, 2, v_v_1456_);
lean_ctor_set(v_reuseFailAlloc_1530_, 3, v_r_1301_);
lean_ctor_set(v_reuseFailAlloc_1530_, 4, v_tree_1454_);
v___x_1526_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
lean_object* v___x_1528_; 
if (v_isShared_1468_ == 0)
{
lean_ctor_set(v___x_1467_, 4, v___x_1526_);
lean_ctor_set(v___x_1467_, 0, v___x_1522_);
v___x_1528_ = v___x_1467_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v___x_1522_);
lean_ctor_set(v_reuseFailAlloc_1529_, 1, v_k_1298_);
lean_ctor_set(v_reuseFailAlloc_1529_, 2, v_v_1299_);
lean_ctor_set(v_reuseFailAlloc_1529_, 3, v_l_1300_);
lean_ctor_set(v_reuseFailAlloc_1529_, 4, v___x_1526_);
v___x_1528_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
return v___x_1528_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_1300_) == 0)
{
lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1560_; 
lean_inc_ref(v_l_1300_);
lean_inc(v_v_1299_);
lean_inc(v_k_1298_);
lean_inc(v_size_1297_);
v_isSharedCheck_1560_ = !lean_is_exclusive(v_l_1117_);
if (v_isSharedCheck_1560_ == 0)
{
lean_object* v_unused_1561_; lean_object* v_unused_1562_; lean_object* v_unused_1563_; lean_object* v_unused_1564_; lean_object* v_unused_1565_; 
v_unused_1561_ = lean_ctor_get(v_l_1117_, 4);
lean_dec(v_unused_1561_);
v_unused_1562_ = lean_ctor_get(v_l_1117_, 3);
lean_dec(v_unused_1562_);
v_unused_1563_ = lean_ctor_get(v_l_1117_, 2);
lean_dec(v_unused_1563_);
v_unused_1564_ = lean_ctor_get(v_l_1117_, 1);
lean_dec(v_unused_1564_);
v_unused_1565_ = lean_ctor_get(v_l_1117_, 0);
lean_dec(v_unused_1565_);
v___x_1538_ = v_l_1117_;
v_isShared_1539_ = v_isSharedCheck_1560_;
goto v_resetjp_1537_;
}
else
{
lean_dec(v_l_1117_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1560_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
if (lean_obj_tag(v_r_1301_) == 0)
{
lean_object* v_k_1540_; lean_object* v_v_1541_; lean_object* v_size_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1546_; 
v_k_1540_ = lean_ctor_get(v___x_1453_, 0);
lean_inc(v_k_1540_);
v_v_1541_ = lean_ctor_get(v___x_1453_, 1);
lean_inc(v_v_1541_);
lean_dec_ref(v___x_1453_);
v_size_1542_ = lean_ctor_get(v_r_1301_, 0);
v___x_1543_ = lean_nat_add(v___x_1307_, v_size_1297_);
lean_dec(v_size_1297_);
v___x_1544_ = lean_nat_add(v___x_1307_, v_size_1542_);
if (v_isShared_1452_ == 0)
{
lean_ctor_set(v___x_1451_, 4, v_tree_1454_);
lean_ctor_set(v___x_1451_, 3, v_r_1301_);
lean_ctor_set(v___x_1451_, 2, v_v_1541_);
lean_ctor_set(v___x_1451_, 1, v_k_1540_);
lean_ctor_set(v___x_1451_, 0, v___x_1544_);
v___x_1546_ = v___x_1451_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v___x_1544_);
lean_ctor_set(v_reuseFailAlloc_1550_, 1, v_k_1540_);
lean_ctor_set(v_reuseFailAlloc_1550_, 2, v_v_1541_);
lean_ctor_set(v_reuseFailAlloc_1550_, 3, v_r_1301_);
lean_ctor_set(v_reuseFailAlloc_1550_, 4, v_tree_1454_);
v___x_1546_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
lean_object* v___x_1548_; 
if (v_isShared_1539_ == 0)
{
lean_ctor_set(v___x_1538_, 4, v___x_1546_);
lean_ctor_set(v___x_1538_, 0, v___x_1543_);
v___x_1548_ = v___x_1538_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v___x_1543_);
lean_ctor_set(v_reuseFailAlloc_1549_, 1, v_k_1298_);
lean_ctor_set(v_reuseFailAlloc_1549_, 2, v_v_1299_);
lean_ctor_set(v_reuseFailAlloc_1549_, 3, v_l_1300_);
lean_ctor_set(v_reuseFailAlloc_1549_, 4, v___x_1546_);
v___x_1548_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
return v___x_1548_;
}
}
}
else
{
lean_object* v_k_1551_; lean_object* v_v_1552_; lean_object* v___x_1553_; lean_object* v___x_1555_; 
lean_dec(v_size_1297_);
v_k_1551_ = lean_ctor_get(v___x_1453_, 0);
lean_inc(v_k_1551_);
v_v_1552_ = lean_ctor_get(v___x_1453_, 1);
lean_inc(v_v_1552_);
lean_dec_ref(v___x_1453_);
v___x_1553_ = lean_unsigned_to_nat(3u);
if (v_isShared_1452_ == 0)
{
lean_ctor_set(v___x_1451_, 4, v_r_1301_);
lean_ctor_set(v___x_1451_, 3, v_r_1301_);
lean_ctor_set(v___x_1451_, 2, v_v_1552_);
lean_ctor_set(v___x_1451_, 1, v_k_1551_);
lean_ctor_set(v___x_1451_, 0, v___x_1307_);
v___x_1555_ = v___x_1451_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v___x_1307_);
lean_ctor_set(v_reuseFailAlloc_1559_, 1, v_k_1551_);
lean_ctor_set(v_reuseFailAlloc_1559_, 2, v_v_1552_);
lean_ctor_set(v_reuseFailAlloc_1559_, 3, v_r_1301_);
lean_ctor_set(v_reuseFailAlloc_1559_, 4, v_r_1301_);
v___x_1555_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
lean_object* v___x_1557_; 
if (v_isShared_1539_ == 0)
{
lean_ctor_set(v___x_1538_, 4, v___x_1555_);
lean_ctor_set(v___x_1538_, 0, v___x_1553_);
v___x_1557_ = v___x_1538_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v___x_1553_);
lean_ctor_set(v_reuseFailAlloc_1558_, 1, v_k_1298_);
lean_ctor_set(v_reuseFailAlloc_1558_, 2, v_v_1299_);
lean_ctor_set(v_reuseFailAlloc_1558_, 3, v_l_1300_);
lean_ctor_set(v_reuseFailAlloc_1558_, 4, v___x_1555_);
v___x_1557_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
return v___x_1557_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1301_) == 0)
{
lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1590_; 
lean_inc(v_l_1300_);
lean_inc(v_v_1299_);
lean_inc(v_k_1298_);
v_isSharedCheck_1590_ = !lean_is_exclusive(v_l_1117_);
if (v_isSharedCheck_1590_ == 0)
{
lean_object* v_unused_1591_; lean_object* v_unused_1592_; lean_object* v_unused_1593_; lean_object* v_unused_1594_; lean_object* v_unused_1595_; 
v_unused_1591_ = lean_ctor_get(v_l_1117_, 4);
lean_dec(v_unused_1591_);
v_unused_1592_ = lean_ctor_get(v_l_1117_, 3);
lean_dec(v_unused_1592_);
v_unused_1593_ = lean_ctor_get(v_l_1117_, 2);
lean_dec(v_unused_1593_);
v_unused_1594_ = lean_ctor_get(v_l_1117_, 1);
lean_dec(v_unused_1594_);
v_unused_1595_ = lean_ctor_get(v_l_1117_, 0);
lean_dec(v_unused_1595_);
v___x_1567_ = v_l_1117_;
v_isShared_1568_ = v_isSharedCheck_1590_;
goto v_resetjp_1566_;
}
else
{
lean_dec(v_l_1117_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1590_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
lean_object* v_k_1569_; lean_object* v_v_1570_; lean_object* v_k_1571_; lean_object* v_v_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1586_; 
v_k_1569_ = lean_ctor_get(v___x_1453_, 0);
lean_inc(v_k_1569_);
v_v_1570_ = lean_ctor_get(v___x_1453_, 1);
lean_inc(v_v_1570_);
lean_dec_ref(v___x_1453_);
v_k_1571_ = lean_ctor_get(v_r_1301_, 1);
v_v_1572_ = lean_ctor_get(v_r_1301_, 2);
v_isSharedCheck_1586_ = !lean_is_exclusive(v_r_1301_);
if (v_isSharedCheck_1586_ == 0)
{
lean_object* v_unused_1587_; lean_object* v_unused_1588_; lean_object* v_unused_1589_; 
v_unused_1587_ = lean_ctor_get(v_r_1301_, 4);
lean_dec(v_unused_1587_);
v_unused_1588_ = lean_ctor_get(v_r_1301_, 3);
lean_dec(v_unused_1588_);
v_unused_1589_ = lean_ctor_get(v_r_1301_, 0);
lean_dec(v_unused_1589_);
v___x_1574_ = v_r_1301_;
v_isShared_1575_ = v_isSharedCheck_1586_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_v_1572_);
lean_inc(v_k_1571_);
lean_dec(v_r_1301_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1586_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v___x_1576_; lean_object* v___x_1578_; 
v___x_1576_ = lean_unsigned_to_nat(3u);
if (v_isShared_1575_ == 0)
{
lean_ctor_set(v___x_1574_, 4, v_l_1300_);
lean_ctor_set(v___x_1574_, 3, v_l_1300_);
lean_ctor_set(v___x_1574_, 2, v_v_1299_);
lean_ctor_set(v___x_1574_, 1, v_k_1298_);
lean_ctor_set(v___x_1574_, 0, v___x_1307_);
v___x_1578_ = v___x_1574_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v___x_1307_);
lean_ctor_set(v_reuseFailAlloc_1585_, 1, v_k_1298_);
lean_ctor_set(v_reuseFailAlloc_1585_, 2, v_v_1299_);
lean_ctor_set(v_reuseFailAlloc_1585_, 3, v_l_1300_);
lean_ctor_set(v_reuseFailAlloc_1585_, 4, v_l_1300_);
v___x_1578_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
lean_object* v___x_1580_; 
if (v_isShared_1452_ == 0)
{
lean_ctor_set(v___x_1451_, 4, v_l_1300_);
lean_ctor_set(v___x_1451_, 3, v_l_1300_);
lean_ctor_set(v___x_1451_, 2, v_v_1570_);
lean_ctor_set(v___x_1451_, 1, v_k_1569_);
lean_ctor_set(v___x_1451_, 0, v___x_1307_);
v___x_1580_ = v___x_1451_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v___x_1307_);
lean_ctor_set(v_reuseFailAlloc_1584_, 1, v_k_1569_);
lean_ctor_set(v_reuseFailAlloc_1584_, 2, v_v_1570_);
lean_ctor_set(v_reuseFailAlloc_1584_, 3, v_l_1300_);
lean_ctor_set(v_reuseFailAlloc_1584_, 4, v_l_1300_);
v___x_1580_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
lean_object* v___x_1582_; 
if (v_isShared_1568_ == 0)
{
lean_ctor_set(v___x_1567_, 4, v___x_1580_);
lean_ctor_set(v___x_1567_, 3, v___x_1578_);
lean_ctor_set(v___x_1567_, 2, v_v_1572_);
lean_ctor_set(v___x_1567_, 1, v_k_1571_);
lean_ctor_set(v___x_1567_, 0, v___x_1576_);
v___x_1582_ = v___x_1567_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v___x_1576_);
lean_ctor_set(v_reuseFailAlloc_1583_, 1, v_k_1571_);
lean_ctor_set(v_reuseFailAlloc_1583_, 2, v_v_1572_);
lean_ctor_set(v_reuseFailAlloc_1583_, 3, v___x_1578_);
lean_ctor_set(v_reuseFailAlloc_1583_, 4, v___x_1580_);
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
}
}
else
{
lean_object* v_k_1596_; lean_object* v_v_1597_; lean_object* v___x_1598_; lean_object* v___x_1600_; 
v_k_1596_ = lean_ctor_get(v___x_1453_, 0);
lean_inc(v_k_1596_);
v_v_1597_ = lean_ctor_get(v___x_1453_, 1);
lean_inc(v_v_1597_);
lean_dec_ref(v___x_1453_);
v___x_1598_ = lean_unsigned_to_nat(2u);
if (v_isShared_1452_ == 0)
{
lean_ctor_set(v___x_1451_, 4, v_r_1301_);
lean_ctor_set(v___x_1451_, 3, v_l_1117_);
lean_ctor_set(v___x_1451_, 2, v_v_1597_);
lean_ctor_set(v___x_1451_, 1, v_k_1596_);
lean_ctor_set(v___x_1451_, 0, v___x_1598_);
v___x_1600_ = v___x_1451_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v___x_1598_);
lean_ctor_set(v_reuseFailAlloc_1601_, 1, v_k_1596_);
lean_ctor_set(v_reuseFailAlloc_1601_, 2, v_v_1597_);
lean_ctor_set(v_reuseFailAlloc_1601_, 3, v_l_1117_);
lean_ctor_set(v_reuseFailAlloc_1601_, 4, v_r_1301_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
}
}
}
}
}
}
}
else
{
return v_l_1117_;
}
}
else
{
return v_r_1118_;
}
}
default: 
{
lean_object* v_impl_1608_; lean_object* v___x_1609_; 
v_impl_1608_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_k_1113_, v_r_1118_);
v___x_1609_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1608_) == 0)
{
if (lean_obj_tag(v_l_1117_) == 0)
{
lean_object* v_size_1610_; lean_object* v_size_1611_; lean_object* v_k_1612_; lean_object* v_v_1613_; lean_object* v_l_1614_; lean_object* v_r_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; uint8_t v___x_1618_; 
v_size_1610_ = lean_ctor_get(v_impl_1608_, 0);
lean_inc(v_size_1610_);
v_size_1611_ = lean_ctor_get(v_l_1117_, 0);
v_k_1612_ = lean_ctor_get(v_l_1117_, 1);
v_v_1613_ = lean_ctor_get(v_l_1117_, 2);
v_l_1614_ = lean_ctor_get(v_l_1117_, 3);
v_r_1615_ = lean_ctor_get(v_l_1117_, 4);
lean_inc(v_r_1615_);
v___x_1616_ = lean_unsigned_to_nat(3u);
v___x_1617_ = lean_nat_mul(v___x_1616_, v_size_1610_);
v___x_1618_ = lean_nat_dec_lt(v___x_1617_, v_size_1611_);
lean_dec(v___x_1617_);
if (v___x_1618_ == 0)
{
lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1622_; 
lean_dec(v_r_1615_);
v___x_1619_ = lean_nat_add(v___x_1609_, v_size_1611_);
v___x_1620_ = lean_nat_add(v___x_1619_, v_size_1610_);
lean_dec(v_size_1610_);
lean_dec(v___x_1619_);
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 4, v_impl_1608_);
lean_ctor_set(v___x_1120_, 0, v___x_1620_);
v___x_1622_ = v___x_1120_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v___x_1620_);
lean_ctor_set(v_reuseFailAlloc_1623_, 1, v_k_1115_);
lean_ctor_set(v_reuseFailAlloc_1623_, 2, v_v_1116_);
lean_ctor_set(v_reuseFailAlloc_1623_, 3, v_l_1117_);
lean_ctor_set(v_reuseFailAlloc_1623_, 4, v_impl_1608_);
v___x_1622_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
return v___x_1622_;
}
}
else
{
lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1689_; 
lean_inc(v_l_1614_);
lean_inc(v_v_1613_);
lean_inc(v_k_1612_);
lean_inc(v_size_1611_);
v_isSharedCheck_1689_ = !lean_is_exclusive(v_l_1117_);
if (v_isSharedCheck_1689_ == 0)
{
lean_object* v_unused_1690_; lean_object* v_unused_1691_; lean_object* v_unused_1692_; lean_object* v_unused_1693_; lean_object* v_unused_1694_; 
v_unused_1690_ = lean_ctor_get(v_l_1117_, 4);
lean_dec(v_unused_1690_);
v_unused_1691_ = lean_ctor_get(v_l_1117_, 3);
lean_dec(v_unused_1691_);
v_unused_1692_ = lean_ctor_get(v_l_1117_, 2);
lean_dec(v_unused_1692_);
v_unused_1693_ = lean_ctor_get(v_l_1117_, 1);
lean_dec(v_unused_1693_);
v_unused_1694_ = lean_ctor_get(v_l_1117_, 0);
lean_dec(v_unused_1694_);
v___x_1625_ = v_l_1117_;
v_isShared_1626_ = v_isSharedCheck_1689_;
goto v_resetjp_1624_;
}
else
{
lean_dec(v_l_1117_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1689_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v_size_1627_; lean_object* v_size_1628_; lean_object* v_k_1629_; lean_object* v_v_1630_; lean_object* v_l_1631_; lean_object* v_r_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; uint8_t v___x_1635_; 
v_size_1627_ = lean_ctor_get(v_l_1614_, 0);
v_size_1628_ = lean_ctor_get(v_r_1615_, 0);
v_k_1629_ = lean_ctor_get(v_r_1615_, 1);
v_v_1630_ = lean_ctor_get(v_r_1615_, 2);
v_l_1631_ = lean_ctor_get(v_r_1615_, 3);
v_r_1632_ = lean_ctor_get(v_r_1615_, 4);
v___x_1633_ = lean_unsigned_to_nat(2u);
v___x_1634_ = lean_nat_mul(v___x_1633_, v_size_1627_);
v___x_1635_ = lean_nat_dec_lt(v_size_1628_, v___x_1634_);
lean_dec(v___x_1634_);
if (v___x_1635_ == 0)
{
lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1664_; 
lean_inc(v_r_1632_);
lean_inc(v_l_1631_);
lean_inc(v_v_1630_);
lean_inc(v_k_1629_);
v_isSharedCheck_1664_ = !lean_is_exclusive(v_r_1615_);
if (v_isSharedCheck_1664_ == 0)
{
lean_object* v_unused_1665_; lean_object* v_unused_1666_; lean_object* v_unused_1667_; lean_object* v_unused_1668_; lean_object* v_unused_1669_; 
v_unused_1665_ = lean_ctor_get(v_r_1615_, 4);
lean_dec(v_unused_1665_);
v_unused_1666_ = lean_ctor_get(v_r_1615_, 3);
lean_dec(v_unused_1666_);
v_unused_1667_ = lean_ctor_get(v_r_1615_, 2);
lean_dec(v_unused_1667_);
v_unused_1668_ = lean_ctor_get(v_r_1615_, 1);
lean_dec(v_unused_1668_);
v_unused_1669_ = lean_ctor_get(v_r_1615_, 0);
lean_dec(v_unused_1669_);
v___x_1637_ = v_r_1615_;
v_isShared_1638_ = v_isSharedCheck_1664_;
goto v_resetjp_1636_;
}
else
{
lean_dec(v_r_1615_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1664_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___y_1642_; lean_object* v___y_1643_; lean_object* v___y_1644_; lean_object* v___x_1652_; lean_object* v___y_1654_; 
v___x_1639_ = lean_nat_add(v___x_1609_, v_size_1611_);
lean_dec(v_size_1611_);
v___x_1640_ = lean_nat_add(v___x_1639_, v_size_1610_);
lean_dec(v___x_1639_);
v___x_1652_ = lean_nat_add(v___x_1609_, v_size_1627_);
if (lean_obj_tag(v_l_1631_) == 0)
{
lean_object* v_size_1662_; 
v_size_1662_ = lean_ctor_get(v_l_1631_, 0);
lean_inc(v_size_1662_);
v___y_1654_ = v_size_1662_;
goto v___jp_1653_;
}
else
{
lean_object* v___x_1663_; 
v___x_1663_ = lean_unsigned_to_nat(0u);
v___y_1654_ = v___x_1663_;
goto v___jp_1653_;
}
v___jp_1641_:
{
lean_object* v___x_1645_; lean_object* v___x_1647_; 
v___x_1645_ = lean_nat_add(v___y_1642_, v___y_1644_);
lean_dec(v___y_1644_);
lean_dec(v___y_1642_);
if (v_isShared_1638_ == 0)
{
lean_ctor_set(v___x_1637_, 4, v_impl_1608_);
lean_ctor_set(v___x_1637_, 3, v_r_1632_);
lean_ctor_set(v___x_1637_, 2, v_v_1116_);
lean_ctor_set(v___x_1637_, 1, v_k_1115_);
lean_ctor_set(v___x_1637_, 0, v___x_1645_);
v___x_1647_ = v___x_1637_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v___x_1645_);
lean_ctor_set(v_reuseFailAlloc_1651_, 1, v_k_1115_);
lean_ctor_set(v_reuseFailAlloc_1651_, 2, v_v_1116_);
lean_ctor_set(v_reuseFailAlloc_1651_, 3, v_r_1632_);
lean_ctor_set(v_reuseFailAlloc_1651_, 4, v_impl_1608_);
v___x_1647_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
lean_object* v___x_1649_; 
if (v_isShared_1626_ == 0)
{
lean_ctor_set(v___x_1625_, 4, v___x_1647_);
lean_ctor_set(v___x_1625_, 3, v___y_1643_);
lean_ctor_set(v___x_1625_, 2, v_v_1630_);
lean_ctor_set(v___x_1625_, 1, v_k_1629_);
lean_ctor_set(v___x_1625_, 0, v___x_1640_);
v___x_1649_ = v___x_1625_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v___x_1640_);
lean_ctor_set(v_reuseFailAlloc_1650_, 1, v_k_1629_);
lean_ctor_set(v_reuseFailAlloc_1650_, 2, v_v_1630_);
lean_ctor_set(v_reuseFailAlloc_1650_, 3, v___y_1643_);
lean_ctor_set(v_reuseFailAlloc_1650_, 4, v___x_1647_);
v___x_1649_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
return v___x_1649_;
}
}
}
v___jp_1653_:
{
lean_object* v___x_1655_; lean_object* v___x_1657_; 
v___x_1655_ = lean_nat_add(v___x_1652_, v___y_1654_);
lean_dec(v___y_1654_);
lean_dec(v___x_1652_);
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 4, v_l_1631_);
lean_ctor_set(v___x_1120_, 3, v_l_1614_);
lean_ctor_set(v___x_1120_, 2, v_v_1613_);
lean_ctor_set(v___x_1120_, 1, v_k_1612_);
lean_ctor_set(v___x_1120_, 0, v___x_1655_);
v___x_1657_ = v___x_1120_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v___x_1655_);
lean_ctor_set(v_reuseFailAlloc_1661_, 1, v_k_1612_);
lean_ctor_set(v_reuseFailAlloc_1661_, 2, v_v_1613_);
lean_ctor_set(v_reuseFailAlloc_1661_, 3, v_l_1614_);
lean_ctor_set(v_reuseFailAlloc_1661_, 4, v_l_1631_);
v___x_1657_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
lean_object* v___x_1658_; 
v___x_1658_ = lean_nat_add(v___x_1609_, v_size_1610_);
lean_dec(v_size_1610_);
if (lean_obj_tag(v_r_1632_) == 0)
{
lean_object* v_size_1659_; 
v_size_1659_ = lean_ctor_get(v_r_1632_, 0);
lean_inc(v_size_1659_);
v___y_1642_ = v___x_1658_;
v___y_1643_ = v___x_1657_;
v___y_1644_ = v_size_1659_;
goto v___jp_1641_;
}
else
{
lean_object* v___x_1660_; 
v___x_1660_ = lean_unsigned_to_nat(0u);
v___y_1642_ = v___x_1658_;
v___y_1643_ = v___x_1657_;
v___y_1644_ = v___x_1660_;
goto v___jp_1641_;
}
}
}
}
}
else
{
lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1675_; 
lean_del_object(v___x_1120_);
v___x_1670_ = lean_nat_add(v___x_1609_, v_size_1611_);
lean_dec(v_size_1611_);
v___x_1671_ = lean_nat_add(v___x_1670_, v_size_1610_);
lean_dec(v___x_1670_);
v___x_1672_ = lean_nat_add(v___x_1609_, v_size_1610_);
lean_dec(v_size_1610_);
v___x_1673_ = lean_nat_add(v___x_1672_, v_size_1628_);
lean_dec(v___x_1672_);
lean_inc_ref(v_impl_1608_);
if (v_isShared_1626_ == 0)
{
lean_ctor_set(v___x_1625_, 4, v_impl_1608_);
lean_ctor_set(v___x_1625_, 3, v_r_1615_);
lean_ctor_set(v___x_1625_, 2, v_v_1116_);
lean_ctor_set(v___x_1625_, 1, v_k_1115_);
lean_ctor_set(v___x_1625_, 0, v___x_1673_);
v___x_1675_ = v___x_1625_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v___x_1673_);
lean_ctor_set(v_reuseFailAlloc_1688_, 1, v_k_1115_);
lean_ctor_set(v_reuseFailAlloc_1688_, 2, v_v_1116_);
lean_ctor_set(v_reuseFailAlloc_1688_, 3, v_r_1615_);
lean_ctor_set(v_reuseFailAlloc_1688_, 4, v_impl_1608_);
v___x_1675_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1682_; 
v_isSharedCheck_1682_ = !lean_is_exclusive(v_impl_1608_);
if (v_isSharedCheck_1682_ == 0)
{
lean_object* v_unused_1683_; lean_object* v_unused_1684_; lean_object* v_unused_1685_; lean_object* v_unused_1686_; lean_object* v_unused_1687_; 
v_unused_1683_ = lean_ctor_get(v_impl_1608_, 4);
lean_dec(v_unused_1683_);
v_unused_1684_ = lean_ctor_get(v_impl_1608_, 3);
lean_dec(v_unused_1684_);
v_unused_1685_ = lean_ctor_get(v_impl_1608_, 2);
lean_dec(v_unused_1685_);
v_unused_1686_ = lean_ctor_get(v_impl_1608_, 1);
lean_dec(v_unused_1686_);
v_unused_1687_ = lean_ctor_get(v_impl_1608_, 0);
lean_dec(v_unused_1687_);
v___x_1677_ = v_impl_1608_;
v_isShared_1678_ = v_isSharedCheck_1682_;
goto v_resetjp_1676_;
}
else
{
lean_dec(v_impl_1608_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1682_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
lean_object* v___x_1680_; 
if (v_isShared_1678_ == 0)
{
lean_ctor_set(v___x_1677_, 4, v___x_1675_);
lean_ctor_set(v___x_1677_, 3, v_l_1614_);
lean_ctor_set(v___x_1677_, 2, v_v_1613_);
lean_ctor_set(v___x_1677_, 1, v_k_1612_);
lean_ctor_set(v___x_1677_, 0, v___x_1671_);
v___x_1680_ = v___x_1677_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v___x_1671_);
lean_ctor_set(v_reuseFailAlloc_1681_, 1, v_k_1612_);
lean_ctor_set(v_reuseFailAlloc_1681_, 2, v_v_1613_);
lean_ctor_set(v_reuseFailAlloc_1681_, 3, v_l_1614_);
lean_ctor_set(v_reuseFailAlloc_1681_, 4, v___x_1675_);
v___x_1680_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
return v___x_1680_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1695_; lean_object* v___x_1696_; lean_object* v___x_1698_; 
v_size_1695_ = lean_ctor_get(v_impl_1608_, 0);
lean_inc(v_size_1695_);
v___x_1696_ = lean_nat_add(v___x_1609_, v_size_1695_);
lean_dec(v_size_1695_);
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 4, v_impl_1608_);
lean_ctor_set(v___x_1120_, 0, v___x_1696_);
v___x_1698_ = v___x_1120_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v___x_1696_);
lean_ctor_set(v_reuseFailAlloc_1699_, 1, v_k_1115_);
lean_ctor_set(v_reuseFailAlloc_1699_, 2, v_v_1116_);
lean_ctor_set(v_reuseFailAlloc_1699_, 3, v_l_1117_);
lean_ctor_set(v_reuseFailAlloc_1699_, 4, v_impl_1608_);
v___x_1698_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
return v___x_1698_;
}
}
}
else
{
if (lean_obj_tag(v_l_1117_) == 0)
{
lean_object* v_l_1700_; 
v_l_1700_ = lean_ctor_get(v_l_1117_, 3);
if (lean_obj_tag(v_l_1700_) == 0)
{
lean_object* v_r_1701_; 
lean_inc_ref(v_l_1700_);
v_r_1701_ = lean_ctor_get(v_l_1117_, 4);
lean_inc(v_r_1701_);
if (lean_obj_tag(v_r_1701_) == 0)
{
lean_object* v_size_1702_; lean_object* v_k_1703_; lean_object* v_v_1704_; lean_object* v___x_1706_; uint8_t v_isShared_1707_; uint8_t v_isSharedCheck_1717_; 
v_size_1702_ = lean_ctor_get(v_l_1117_, 0);
v_k_1703_ = lean_ctor_get(v_l_1117_, 1);
v_v_1704_ = lean_ctor_get(v_l_1117_, 2);
v_isSharedCheck_1717_ = !lean_is_exclusive(v_l_1117_);
if (v_isSharedCheck_1717_ == 0)
{
lean_object* v_unused_1718_; lean_object* v_unused_1719_; 
v_unused_1718_ = lean_ctor_get(v_l_1117_, 4);
lean_dec(v_unused_1718_);
v_unused_1719_ = lean_ctor_get(v_l_1117_, 3);
lean_dec(v_unused_1719_);
v___x_1706_ = v_l_1117_;
v_isShared_1707_ = v_isSharedCheck_1717_;
goto v_resetjp_1705_;
}
else
{
lean_inc(v_v_1704_);
lean_inc(v_k_1703_);
lean_inc(v_size_1702_);
lean_dec(v_l_1117_);
v___x_1706_ = lean_box(0);
v_isShared_1707_ = v_isSharedCheck_1717_;
goto v_resetjp_1705_;
}
v_resetjp_1705_:
{
lean_object* v_size_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1712_; 
v_size_1708_ = lean_ctor_get(v_r_1701_, 0);
v___x_1709_ = lean_nat_add(v___x_1609_, v_size_1702_);
lean_dec(v_size_1702_);
v___x_1710_ = lean_nat_add(v___x_1609_, v_size_1708_);
if (v_isShared_1707_ == 0)
{
lean_ctor_set(v___x_1706_, 4, v_impl_1608_);
lean_ctor_set(v___x_1706_, 3, v_r_1701_);
lean_ctor_set(v___x_1706_, 2, v_v_1116_);
lean_ctor_set(v___x_1706_, 1, v_k_1115_);
lean_ctor_set(v___x_1706_, 0, v___x_1710_);
v___x_1712_ = v___x_1706_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v___x_1710_);
lean_ctor_set(v_reuseFailAlloc_1716_, 1, v_k_1115_);
lean_ctor_set(v_reuseFailAlloc_1716_, 2, v_v_1116_);
lean_ctor_set(v_reuseFailAlloc_1716_, 3, v_r_1701_);
lean_ctor_set(v_reuseFailAlloc_1716_, 4, v_impl_1608_);
v___x_1712_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
lean_object* v___x_1714_; 
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 4, v___x_1712_);
lean_ctor_set(v___x_1120_, 3, v_l_1700_);
lean_ctor_set(v___x_1120_, 2, v_v_1704_);
lean_ctor_set(v___x_1120_, 1, v_k_1703_);
lean_ctor_set(v___x_1120_, 0, v___x_1709_);
v___x_1714_ = v___x_1120_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v___x_1709_);
lean_ctor_set(v_reuseFailAlloc_1715_, 1, v_k_1703_);
lean_ctor_set(v_reuseFailAlloc_1715_, 2, v_v_1704_);
lean_ctor_set(v_reuseFailAlloc_1715_, 3, v_l_1700_);
lean_ctor_set(v_reuseFailAlloc_1715_, 4, v___x_1712_);
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
lean_object* v_k_1720_; lean_object* v_v_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1732_; 
v_k_1720_ = lean_ctor_get(v_l_1117_, 1);
v_v_1721_ = lean_ctor_get(v_l_1117_, 2);
v_isSharedCheck_1732_ = !lean_is_exclusive(v_l_1117_);
if (v_isSharedCheck_1732_ == 0)
{
lean_object* v_unused_1733_; lean_object* v_unused_1734_; lean_object* v_unused_1735_; 
v_unused_1733_ = lean_ctor_get(v_l_1117_, 4);
lean_dec(v_unused_1733_);
v_unused_1734_ = lean_ctor_get(v_l_1117_, 3);
lean_dec(v_unused_1734_);
v_unused_1735_ = lean_ctor_get(v_l_1117_, 0);
lean_dec(v_unused_1735_);
v___x_1723_ = v_l_1117_;
v_isShared_1724_ = v_isSharedCheck_1732_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_v_1721_);
lean_inc(v_k_1720_);
lean_dec(v_l_1117_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1732_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v___x_1725_; lean_object* v___x_1727_; 
v___x_1725_ = lean_unsigned_to_nat(3u);
if (v_isShared_1724_ == 0)
{
lean_ctor_set(v___x_1723_, 3, v_r_1701_);
lean_ctor_set(v___x_1723_, 2, v_v_1116_);
lean_ctor_set(v___x_1723_, 1, v_k_1115_);
lean_ctor_set(v___x_1723_, 0, v___x_1609_);
v___x_1727_ = v___x_1723_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v___x_1609_);
lean_ctor_set(v_reuseFailAlloc_1731_, 1, v_k_1115_);
lean_ctor_set(v_reuseFailAlloc_1731_, 2, v_v_1116_);
lean_ctor_set(v_reuseFailAlloc_1731_, 3, v_r_1701_);
lean_ctor_set(v_reuseFailAlloc_1731_, 4, v_r_1701_);
v___x_1727_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
lean_object* v___x_1729_; 
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 4, v___x_1727_);
lean_ctor_set(v___x_1120_, 3, v_l_1700_);
lean_ctor_set(v___x_1120_, 2, v_v_1721_);
lean_ctor_set(v___x_1120_, 1, v_k_1720_);
lean_ctor_set(v___x_1120_, 0, v___x_1725_);
v___x_1729_ = v___x_1120_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v___x_1725_);
lean_ctor_set(v_reuseFailAlloc_1730_, 1, v_k_1720_);
lean_ctor_set(v_reuseFailAlloc_1730_, 2, v_v_1721_);
lean_ctor_set(v_reuseFailAlloc_1730_, 3, v_l_1700_);
lean_ctor_set(v_reuseFailAlloc_1730_, 4, v___x_1727_);
v___x_1729_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
return v___x_1729_;
}
}
}
}
}
else
{
lean_object* v_r_1736_; 
v_r_1736_ = lean_ctor_get(v_l_1117_, 4);
lean_inc(v_r_1736_);
if (lean_obj_tag(v_r_1736_) == 0)
{
lean_object* v_k_1737_; lean_object* v_v_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1761_; 
lean_inc(v_l_1700_);
v_k_1737_ = lean_ctor_get(v_l_1117_, 1);
v_v_1738_ = lean_ctor_get(v_l_1117_, 2);
v_isSharedCheck_1761_ = !lean_is_exclusive(v_l_1117_);
if (v_isSharedCheck_1761_ == 0)
{
lean_object* v_unused_1762_; lean_object* v_unused_1763_; lean_object* v_unused_1764_; 
v_unused_1762_ = lean_ctor_get(v_l_1117_, 4);
lean_dec(v_unused_1762_);
v_unused_1763_ = lean_ctor_get(v_l_1117_, 3);
lean_dec(v_unused_1763_);
v_unused_1764_ = lean_ctor_get(v_l_1117_, 0);
lean_dec(v_unused_1764_);
v___x_1740_ = v_l_1117_;
v_isShared_1741_ = v_isSharedCheck_1761_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_v_1738_);
lean_inc(v_k_1737_);
lean_dec(v_l_1117_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1761_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
lean_object* v_k_1742_; lean_object* v_v_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1757_; 
v_k_1742_ = lean_ctor_get(v_r_1736_, 1);
v_v_1743_ = lean_ctor_get(v_r_1736_, 2);
v_isSharedCheck_1757_ = !lean_is_exclusive(v_r_1736_);
if (v_isSharedCheck_1757_ == 0)
{
lean_object* v_unused_1758_; lean_object* v_unused_1759_; lean_object* v_unused_1760_; 
v_unused_1758_ = lean_ctor_get(v_r_1736_, 4);
lean_dec(v_unused_1758_);
v_unused_1759_ = lean_ctor_get(v_r_1736_, 3);
lean_dec(v_unused_1759_);
v_unused_1760_ = lean_ctor_get(v_r_1736_, 0);
lean_dec(v_unused_1760_);
v___x_1745_ = v_r_1736_;
v_isShared_1746_ = v_isSharedCheck_1757_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_v_1743_);
lean_inc(v_k_1742_);
lean_dec(v_r_1736_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1757_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
lean_object* v___x_1747_; lean_object* v___x_1749_; 
v___x_1747_ = lean_unsigned_to_nat(3u);
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 4, v_l_1700_);
lean_ctor_set(v___x_1745_, 3, v_l_1700_);
lean_ctor_set(v___x_1745_, 2, v_v_1738_);
lean_ctor_set(v___x_1745_, 1, v_k_1737_);
lean_ctor_set(v___x_1745_, 0, v___x_1609_);
v___x_1749_ = v___x_1745_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v___x_1609_);
lean_ctor_set(v_reuseFailAlloc_1756_, 1, v_k_1737_);
lean_ctor_set(v_reuseFailAlloc_1756_, 2, v_v_1738_);
lean_ctor_set(v_reuseFailAlloc_1756_, 3, v_l_1700_);
lean_ctor_set(v_reuseFailAlloc_1756_, 4, v_l_1700_);
v___x_1749_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
lean_object* v___x_1751_; 
if (v_isShared_1741_ == 0)
{
lean_ctor_set(v___x_1740_, 4, v_l_1700_);
lean_ctor_set(v___x_1740_, 2, v_v_1116_);
lean_ctor_set(v___x_1740_, 1, v_k_1115_);
lean_ctor_set(v___x_1740_, 0, v___x_1609_);
v___x_1751_ = v___x_1740_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v___x_1609_);
lean_ctor_set(v_reuseFailAlloc_1755_, 1, v_k_1115_);
lean_ctor_set(v_reuseFailAlloc_1755_, 2, v_v_1116_);
lean_ctor_set(v_reuseFailAlloc_1755_, 3, v_l_1700_);
lean_ctor_set(v_reuseFailAlloc_1755_, 4, v_l_1700_);
v___x_1751_ = v_reuseFailAlloc_1755_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
lean_object* v___x_1753_; 
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 4, v___x_1751_);
lean_ctor_set(v___x_1120_, 3, v___x_1749_);
lean_ctor_set(v___x_1120_, 2, v_v_1743_);
lean_ctor_set(v___x_1120_, 1, v_k_1742_);
lean_ctor_set(v___x_1120_, 0, v___x_1747_);
v___x_1753_ = v___x_1120_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1754_, 0, v___x_1747_);
lean_ctor_set(v_reuseFailAlloc_1754_, 1, v_k_1742_);
lean_ctor_set(v_reuseFailAlloc_1754_, 2, v_v_1743_);
lean_ctor_set(v_reuseFailAlloc_1754_, 3, v___x_1749_);
lean_ctor_set(v_reuseFailAlloc_1754_, 4, v___x_1751_);
v___x_1753_ = v_reuseFailAlloc_1754_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
return v___x_1753_;
}
}
}
}
}
}
else
{
lean_object* v___x_1765_; lean_object* v___x_1767_; 
v___x_1765_ = lean_unsigned_to_nat(2u);
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 4, v_r_1736_);
lean_ctor_set(v___x_1120_, 0, v___x_1765_);
v___x_1767_ = v___x_1120_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v___x_1765_);
lean_ctor_set(v_reuseFailAlloc_1768_, 1, v_k_1115_);
lean_ctor_set(v_reuseFailAlloc_1768_, 2, v_v_1116_);
lean_ctor_set(v_reuseFailAlloc_1768_, 3, v_l_1117_);
lean_ctor_set(v_reuseFailAlloc_1768_, 4, v_r_1736_);
v___x_1767_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
return v___x_1767_;
}
}
}
}
else
{
lean_object* v___x_1770_; 
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 4, v_l_1117_);
lean_ctor_set(v___x_1120_, 0, v___x_1609_);
v___x_1770_ = v___x_1120_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v___x_1609_);
lean_ctor_set(v_reuseFailAlloc_1771_, 1, v_k_1115_);
lean_ctor_set(v_reuseFailAlloc_1771_, 2, v_v_1116_);
lean_ctor_set(v_reuseFailAlloc_1771_, 3, v_l_1117_);
lean_ctor_set(v_reuseFailAlloc_1771_, 4, v_l_1117_);
v___x_1770_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
return v___x_1770_;
}
}
}
}
}
}
}
else
{
return v_t_1114_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg___boxed(lean_object* v_k_1774_, lean_object* v_t_1775_){
_start:
{
lean_object* v_res_1776_; 
v_res_1776_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_k_1774_, v_t_1775_);
lean_dec_ref(v_k_1774_);
return v_res_1776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___lam__0(lean_object* v_val_1777_, lean_object* v_s_1778_){
_start:
{
lean_object* v_toRing_1779_; lean_object* v_invFn_x3f_1780_; lean_object* v_semiringId_x3f_1781_; lean_object* v_commSemiringInst_1782_; lean_object* v_commRingInst_1783_; lean_object* v_noZeroDivInst_x3f_1784_; lean_object* v_fieldInst_x3f_1785_; lean_object* v_denoteEntries_1786_; lean_object* v_nextId_1787_; lean_object* v_steps_1788_; lean_object* v_queue_1789_; lean_object* v_basis_1790_; lean_object* v_diseqs_1791_; uint8_t v_recheck_1792_; lean_object* v_invSet_1793_; lean_object* v_numEq0_x3f_1794_; uint8_t v_numEq0Updated_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1803_; 
v_toRing_1779_ = lean_ctor_get(v_s_1778_, 0);
v_invFn_x3f_1780_ = lean_ctor_get(v_s_1778_, 1);
v_semiringId_x3f_1781_ = lean_ctor_get(v_s_1778_, 2);
v_commSemiringInst_1782_ = lean_ctor_get(v_s_1778_, 3);
v_commRingInst_1783_ = lean_ctor_get(v_s_1778_, 4);
v_noZeroDivInst_x3f_1784_ = lean_ctor_get(v_s_1778_, 5);
v_fieldInst_x3f_1785_ = lean_ctor_get(v_s_1778_, 6);
v_denoteEntries_1786_ = lean_ctor_get(v_s_1778_, 7);
v_nextId_1787_ = lean_ctor_get(v_s_1778_, 8);
v_steps_1788_ = lean_ctor_get(v_s_1778_, 9);
v_queue_1789_ = lean_ctor_get(v_s_1778_, 10);
v_basis_1790_ = lean_ctor_get(v_s_1778_, 11);
v_diseqs_1791_ = lean_ctor_get(v_s_1778_, 12);
v_recheck_1792_ = lean_ctor_get_uint8(v_s_1778_, sizeof(void*)*15);
v_invSet_1793_ = lean_ctor_get(v_s_1778_, 13);
v_numEq0_x3f_1794_ = lean_ctor_get(v_s_1778_, 14);
v_numEq0Updated_1795_ = lean_ctor_get_uint8(v_s_1778_, sizeof(void*)*15 + 1);
v_isSharedCheck_1803_ = !lean_is_exclusive(v_s_1778_);
if (v_isSharedCheck_1803_ == 0)
{
v___x_1797_ = v_s_1778_;
v_isShared_1798_ = v_isSharedCheck_1803_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_numEq0_x3f_1794_);
lean_inc(v_invSet_1793_);
lean_inc(v_diseqs_1791_);
lean_inc(v_basis_1790_);
lean_inc(v_queue_1789_);
lean_inc(v_steps_1788_);
lean_inc(v_nextId_1787_);
lean_inc(v_denoteEntries_1786_);
lean_inc(v_fieldInst_x3f_1785_);
lean_inc(v_noZeroDivInst_x3f_1784_);
lean_inc(v_commRingInst_1783_);
lean_inc(v_commSemiringInst_1782_);
lean_inc(v_semiringId_x3f_1781_);
lean_inc(v_invFn_x3f_1780_);
lean_inc(v_toRing_1779_);
lean_dec(v_s_1778_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1803_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v___x_1799_; lean_object* v___x_1801_; 
v___x_1799_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_val_1777_, v_queue_1789_);
if (v_isShared_1798_ == 0)
{
lean_ctor_set(v___x_1797_, 10, v___x_1799_);
v___x_1801_ = v___x_1797_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(0, 15, 2);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v_toRing_1779_);
lean_ctor_set(v_reuseFailAlloc_1802_, 1, v_invFn_x3f_1780_);
lean_ctor_set(v_reuseFailAlloc_1802_, 2, v_semiringId_x3f_1781_);
lean_ctor_set(v_reuseFailAlloc_1802_, 3, v_commSemiringInst_1782_);
lean_ctor_set(v_reuseFailAlloc_1802_, 4, v_commRingInst_1783_);
lean_ctor_set(v_reuseFailAlloc_1802_, 5, v_noZeroDivInst_x3f_1784_);
lean_ctor_set(v_reuseFailAlloc_1802_, 6, v_fieldInst_x3f_1785_);
lean_ctor_set(v_reuseFailAlloc_1802_, 7, v_denoteEntries_1786_);
lean_ctor_set(v_reuseFailAlloc_1802_, 8, v_nextId_1787_);
lean_ctor_set(v_reuseFailAlloc_1802_, 9, v_steps_1788_);
lean_ctor_set(v_reuseFailAlloc_1802_, 10, v___x_1799_);
lean_ctor_set(v_reuseFailAlloc_1802_, 11, v_basis_1790_);
lean_ctor_set(v_reuseFailAlloc_1802_, 12, v_diseqs_1791_);
lean_ctor_set(v_reuseFailAlloc_1802_, 13, v_invSet_1793_);
lean_ctor_set(v_reuseFailAlloc_1802_, 14, v_numEq0_x3f_1794_);
lean_ctor_set_uint8(v_reuseFailAlloc_1802_, sizeof(void*)*15, v_recheck_1792_);
lean_ctor_set_uint8(v_reuseFailAlloc_1802_, sizeof(void*)*15 + 1, v_numEq0Updated_1795_);
v___x_1801_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1800_;
}
v_reusejp_1800_:
{
return v___x_1801_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___lam__0___boxed(lean_object* v_val_1804_, lean_object* v_s_1805_){
_start:
{
lean_object* v_res_1806_; 
v_res_1806_ = l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___lam__0(v_val_1804_, v_s_1805_);
lean_dec_ref(v_val_1804_);
return v_res_1806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f(lean_object* v_a_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_){
_start:
{
lean_object* v___x_1819_; 
v___x_1819_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_);
if (lean_obj_tag(v___x_1819_) == 0)
{
lean_object* v_a_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1858_; 
v_a_1820_ = lean_ctor_get(v___x_1819_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1819_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1822_ = v___x_1819_;
v_isShared_1823_ = v_isSharedCheck_1858_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_a_1820_);
lean_dec(v___x_1819_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1858_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v_queue_1824_; lean_object* v___x_1825_; 
v_queue_1824_ = lean_ctor_get(v_a_1820_, 10);
lean_inc(v_queue_1824_);
lean_dec(v_a_1820_);
v___x_1825_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_queue_1824_);
lean_dec(v_queue_1824_);
if (lean_obj_tag(v___x_1825_) == 1)
{
lean_object* v_val_1826_; lean_object* v___f_1827_; lean_object* v___x_1828_; 
lean_del_object(v___x_1822_);
v_val_1826_ = lean_ctor_get(v___x_1825_, 0);
lean_inc(v_val_1826_);
v___f_1827_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1827_, 0, v_val_1826_);
v___x_1828_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_1827_, v_a_1807_, v_a_1808_);
if (lean_obj_tag(v___x_1828_) == 0)
{
lean_object* v___x_1829_; 
lean_dec_ref(v___x_1828_);
v___x_1829_ = l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg(v_a_1808_);
if (lean_obj_tag(v___x_1829_) == 0)
{
lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1836_; 
v_isSharedCheck_1836_ = !lean_is_exclusive(v___x_1829_);
if (v_isSharedCheck_1836_ == 0)
{
lean_object* v_unused_1837_; 
v_unused_1837_ = lean_ctor_get(v___x_1829_, 0);
lean_dec(v_unused_1837_);
v___x_1831_ = v___x_1829_;
v_isShared_1832_ = v_isSharedCheck_1836_;
goto v_resetjp_1830_;
}
else
{
lean_dec(v___x_1829_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1836_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v___x_1834_; 
if (v_isShared_1832_ == 0)
{
lean_ctor_set(v___x_1831_, 0, v___x_1825_);
v___x_1834_ = v___x_1831_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v___x_1825_);
v___x_1834_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
return v___x_1834_;
}
}
}
else
{
lean_object* v_a_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1845_; 
lean_dec_ref(v___x_1825_);
v_a_1838_ = lean_ctor_get(v___x_1829_, 0);
v_isSharedCheck_1845_ = !lean_is_exclusive(v___x_1829_);
if (v_isSharedCheck_1845_ == 0)
{
v___x_1840_ = v___x_1829_;
v_isShared_1841_ = v_isSharedCheck_1845_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_a_1838_);
lean_dec(v___x_1829_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1845_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v___x_1843_; 
if (v_isShared_1841_ == 0)
{
v___x_1843_ = v___x_1840_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v_a_1838_);
v___x_1843_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
return v___x_1843_;
}
}
}
}
else
{
lean_object* v_a_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1853_; 
lean_dec_ref(v___x_1825_);
v_a_1846_ = lean_ctor_get(v___x_1828_, 0);
v_isSharedCheck_1853_ = !lean_is_exclusive(v___x_1828_);
if (v_isSharedCheck_1853_ == 0)
{
v___x_1848_ = v___x_1828_;
v_isShared_1849_ = v_isSharedCheck_1853_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_a_1846_);
lean_dec(v___x_1828_);
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
lean_object* v___x_1854_; lean_object* v___x_1856_; 
lean_dec(v___x_1825_);
lean_dec_ref(v_a_1807_);
v___x_1854_ = lean_box(0);
if (v_isShared_1823_ == 0)
{
lean_ctor_set(v___x_1822_, 0, v___x_1854_);
v___x_1856_ = v___x_1822_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v___x_1854_);
v___x_1856_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
return v___x_1856_;
}
}
}
}
else
{
lean_object* v_a_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1866_; 
lean_dec_ref(v_a_1807_);
v_a_1859_ = lean_ctor_get(v___x_1819_, 0);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1819_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1861_ = v___x_1819_;
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_a_1859_);
lean_dec(v___x_1819_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v___x_1864_; 
if (v_isShared_1862_ == 0)
{
v___x_1864_ = v___x_1861_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v_a_1859_);
v___x_1864_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
return v___x_1864_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___boxed(lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_){
_start:
{
lean_object* v_res_1879_; 
v_res_1879_ = l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f(v_a_1867_, v_a_1868_, v_a_1869_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_, v_a_1874_, v_a_1875_, v_a_1876_, v_a_1877_);
lean_dec(v_a_1877_);
lean_dec_ref(v_a_1876_);
lean_dec(v_a_1875_);
lean_dec_ref(v_a_1874_);
lean_dec(v_a_1873_);
lean_dec_ref(v_a_1872_);
lean_dec(v_a_1871_);
lean_dec_ref(v_a_1870_);
lean_dec(v_a_1869_);
lean_dec(v_a_1868_);
return v_res_1879_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0(lean_object* v_00_u03b2_1880_, lean_object* v_k_1881_, lean_object* v_t_1882_, lean_object* v_h_1883_){
_start:
{
lean_object* v___x_1884_; 
v___x_1884_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_k_1881_, v_t_1882_);
return v___x_1884_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___boxed(lean_object* v_00_u03b2_1885_, lean_object* v_k_1886_, lean_object* v_t_1887_, lean_object* v_h_1888_){
_start:
{
lean_object* v_res_1889_; 
v_res_1889_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0(v_00_u03b2_1885_, v_k_1886_, v_t_1887_, v_h_1888_);
lean_dec_ref(v_k_1886_);
return v_res_1889_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_1890_, lean_object* v_x_1891_, lean_object* v_x_1892_, lean_object* v_x_1893_){
_start:
{
lean_object* v_ks_1894_; lean_object* v_vs_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1919_; 
v_ks_1894_ = lean_ctor_get(v_x_1890_, 0);
v_vs_1895_ = lean_ctor_get(v_x_1890_, 1);
v_isSharedCheck_1919_ = !lean_is_exclusive(v_x_1890_);
if (v_isSharedCheck_1919_ == 0)
{
v___x_1897_ = v_x_1890_;
v_isShared_1898_ = v_isSharedCheck_1919_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_vs_1895_);
lean_inc(v_ks_1894_);
lean_dec(v_x_1890_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1919_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
lean_object* v___x_1899_; uint8_t v___x_1900_; 
v___x_1899_ = lean_array_get_size(v_ks_1894_);
v___x_1900_ = lean_nat_dec_lt(v_x_1891_, v___x_1899_);
if (v___x_1900_ == 0)
{
lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1904_; 
lean_dec(v_x_1891_);
v___x_1901_ = lean_array_push(v_ks_1894_, v_x_1892_);
v___x_1902_ = lean_array_push(v_vs_1895_, v_x_1893_);
if (v_isShared_1898_ == 0)
{
lean_ctor_set(v___x_1897_, 1, v___x_1902_);
lean_ctor_set(v___x_1897_, 0, v___x_1901_);
v___x_1904_ = v___x_1897_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v___x_1901_);
lean_ctor_set(v_reuseFailAlloc_1905_, 1, v___x_1902_);
v___x_1904_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
return v___x_1904_;
}
}
else
{
lean_object* v_k_x27_1906_; uint8_t v___x_1907_; 
v_k_x27_1906_ = lean_array_fget_borrowed(v_ks_1894_, v_x_1891_);
v___x_1907_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_1892_, v_k_x27_1906_);
if (v___x_1907_ == 0)
{
lean_object* v___x_1909_; 
if (v_isShared_1898_ == 0)
{
v___x_1909_ = v___x_1897_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_ks_1894_);
lean_ctor_set(v_reuseFailAlloc_1913_, 1, v_vs_1895_);
v___x_1909_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
lean_object* v___x_1910_; lean_object* v___x_1911_; 
v___x_1910_ = lean_unsigned_to_nat(1u);
v___x_1911_ = lean_nat_add(v_x_1891_, v___x_1910_);
lean_dec(v_x_1891_);
v_x_1890_ = v___x_1909_;
v_x_1891_ = v___x_1911_;
goto _start;
}
}
else
{
lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1917_; 
v___x_1914_ = lean_array_fset(v_ks_1894_, v_x_1891_, v_x_1892_);
v___x_1915_ = lean_array_fset(v_vs_1895_, v_x_1891_, v_x_1893_);
lean_dec(v_x_1891_);
if (v_isShared_1898_ == 0)
{
lean_ctor_set(v___x_1897_, 1, v___x_1915_);
lean_ctor_set(v___x_1897_, 0, v___x_1914_);
v___x_1917_ = v___x_1897_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v___x_1914_);
lean_ctor_set(v_reuseFailAlloc_1918_, 1, v___x_1915_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1___redArg(lean_object* v_n_1920_, lean_object* v_k_1921_, lean_object* v_v_1922_){
_start:
{
lean_object* v___x_1923_; lean_object* v___x_1924_; 
v___x_1923_ = lean_unsigned_to_nat(0u);
v___x_1924_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1920_, v___x_1923_, v_k_1921_, v_v_1922_);
return v___x_1924_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1925_; 
v___x_1925_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1925_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(lean_object* v_x_1926_, size_t v_x_1927_, size_t v_x_1928_, lean_object* v_x_1929_, lean_object* v_x_1930_){
_start:
{
if (lean_obj_tag(v_x_1926_) == 0)
{
lean_object* v_es_1931_; size_t v___x_1932_; size_t v___x_1933_; size_t v___x_1934_; size_t v___x_1935_; lean_object* v_j_1936_; lean_object* v___x_1937_; uint8_t v___x_1938_; 
v_es_1931_ = lean_ctor_get(v_x_1926_, 0);
v___x_1932_ = ((size_t)5ULL);
v___x_1933_ = ((size_t)1ULL);
v___x_1934_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__1);
v___x_1935_ = lean_usize_land(v_x_1927_, v___x_1934_);
v_j_1936_ = lean_usize_to_nat(v___x_1935_);
v___x_1937_ = lean_array_get_size(v_es_1931_);
v___x_1938_ = lean_nat_dec_lt(v_j_1936_, v___x_1937_);
if (v___x_1938_ == 0)
{
lean_dec(v_j_1936_);
lean_dec(v_x_1930_);
lean_dec_ref(v_x_1929_);
return v_x_1926_;
}
else
{
lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1975_; 
lean_inc_ref(v_es_1931_);
v_isSharedCheck_1975_ = !lean_is_exclusive(v_x_1926_);
if (v_isSharedCheck_1975_ == 0)
{
lean_object* v_unused_1976_; 
v_unused_1976_ = lean_ctor_get(v_x_1926_, 0);
lean_dec(v_unused_1976_);
v___x_1940_ = v_x_1926_;
v_isShared_1941_ = v_isSharedCheck_1975_;
goto v_resetjp_1939_;
}
else
{
lean_dec(v_x_1926_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1975_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v_v_1942_; lean_object* v___x_1943_; lean_object* v_xs_x27_1944_; lean_object* v___y_1946_; 
v_v_1942_ = lean_array_fget(v_es_1931_, v_j_1936_);
v___x_1943_ = lean_box(0);
v_xs_x27_1944_ = lean_array_fset(v_es_1931_, v_j_1936_, v___x_1943_);
switch(lean_obj_tag(v_v_1942_))
{
case 0:
{
lean_object* v_key_1951_; lean_object* v_val_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1962_; 
v_key_1951_ = lean_ctor_get(v_v_1942_, 0);
v_val_1952_ = lean_ctor_get(v_v_1942_, 1);
v_isSharedCheck_1962_ = !lean_is_exclusive(v_v_1942_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1954_ = v_v_1942_;
v_isShared_1955_ = v_isSharedCheck_1962_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_val_1952_);
lean_inc(v_key_1951_);
lean_dec(v_v_1942_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1962_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
uint8_t v___x_1956_; 
v___x_1956_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_1929_, v_key_1951_);
if (v___x_1956_ == 0)
{
lean_object* v___x_1957_; lean_object* v___x_1958_; 
lean_del_object(v___x_1954_);
v___x_1957_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1951_, v_val_1952_, v_x_1929_, v_x_1930_);
v___x_1958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1958_, 0, v___x_1957_);
v___y_1946_ = v___x_1958_;
goto v___jp_1945_;
}
else
{
lean_object* v___x_1960_; 
lean_dec(v_val_1952_);
lean_dec(v_key_1951_);
if (v_isShared_1955_ == 0)
{
lean_ctor_set(v___x_1954_, 1, v_x_1930_);
lean_ctor_set(v___x_1954_, 0, v_x_1929_);
v___x_1960_ = v___x_1954_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v_x_1929_);
lean_ctor_set(v_reuseFailAlloc_1961_, 1, v_x_1930_);
v___x_1960_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
v___y_1946_ = v___x_1960_;
goto v___jp_1945_;
}
}
}
}
case 1:
{
lean_object* v_node_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_1973_; 
v_node_1963_ = lean_ctor_get(v_v_1942_, 0);
v_isSharedCheck_1973_ = !lean_is_exclusive(v_v_1942_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1965_ = v_v_1942_;
v_isShared_1966_ = v_isSharedCheck_1973_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_node_1963_);
lean_dec(v_v_1942_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_1973_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
size_t v___x_1967_; size_t v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1971_; 
v___x_1967_ = lean_usize_shift_right(v_x_1927_, v___x_1932_);
v___x_1968_ = lean_usize_add(v_x_1928_, v___x_1933_);
v___x_1969_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_node_1963_, v___x_1967_, v___x_1968_, v_x_1929_, v_x_1930_);
if (v_isShared_1966_ == 0)
{
lean_ctor_set(v___x_1965_, 0, v___x_1969_);
v___x_1971_ = v___x_1965_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v___x_1969_);
v___x_1971_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
v___y_1946_ = v___x_1971_;
goto v___jp_1945_;
}
}
}
default: 
{
lean_object* v___x_1974_; 
v___x_1974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1974_, 0, v_x_1929_);
lean_ctor_set(v___x_1974_, 1, v_x_1930_);
v___y_1946_ = v___x_1974_;
goto v___jp_1945_;
}
}
v___jp_1945_:
{
lean_object* v___x_1947_; lean_object* v___x_1949_; 
v___x_1947_ = lean_array_fset(v_xs_x27_1944_, v_j_1936_, v___y_1946_);
lean_dec(v_j_1936_);
if (v_isShared_1941_ == 0)
{
lean_ctor_set(v___x_1940_, 0, v___x_1947_);
v___x_1949_ = v___x_1940_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v___x_1947_);
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
lean_object* v_ks_1977_; lean_object* v_vs_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_1998_; 
v_ks_1977_ = lean_ctor_get(v_x_1926_, 0);
v_vs_1978_ = lean_ctor_get(v_x_1926_, 1);
v_isSharedCheck_1998_ = !lean_is_exclusive(v_x_1926_);
if (v_isSharedCheck_1998_ == 0)
{
v___x_1980_ = v_x_1926_;
v_isShared_1981_ = v_isSharedCheck_1998_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_vs_1978_);
lean_inc(v_ks_1977_);
lean_dec(v_x_1926_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_1998_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v___x_1983_; 
if (v_isShared_1981_ == 0)
{
v___x_1983_ = v___x_1980_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v_ks_1977_);
lean_ctor_set(v_reuseFailAlloc_1997_, 1, v_vs_1978_);
v___x_1983_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
lean_object* v_newNode_1984_; uint8_t v___y_1986_; size_t v___x_1992_; uint8_t v___x_1993_; 
v_newNode_1984_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1___redArg(v___x_1983_, v_x_1929_, v_x_1930_);
v___x_1992_ = ((size_t)7ULL);
v___x_1993_ = lean_usize_dec_le(v___x_1992_, v_x_1928_);
if (v___x_1993_ == 0)
{
lean_object* v___x_1994_; lean_object* v___x_1995_; uint8_t v___x_1996_; 
v___x_1994_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1984_);
v___x_1995_ = lean_unsigned_to_nat(4u);
v___x_1996_ = lean_nat_dec_lt(v___x_1994_, v___x_1995_);
lean_dec(v___x_1994_);
v___y_1986_ = v___x_1996_;
goto v___jp_1985_;
}
else
{
v___y_1986_ = v___x_1993_;
goto v___jp_1985_;
}
v___jp_1985_:
{
if (v___y_1986_ == 0)
{
lean_object* v_ks_1987_; lean_object* v_vs_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; 
v_ks_1987_ = lean_ctor_get(v_newNode_1984_, 0);
lean_inc_ref(v_ks_1987_);
v_vs_1988_ = lean_ctor_get(v_newNode_1984_, 1);
lean_inc_ref(v_vs_1988_);
lean_dec_ref(v_newNode_1984_);
v___x_1989_ = lean_unsigned_to_nat(0u);
v___x_1990_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0);
v___x_1991_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg(v_x_1928_, v_ks_1987_, v_vs_1988_, v___x_1989_, v___x_1990_);
lean_dec_ref(v_vs_1988_);
lean_dec_ref(v_ks_1987_);
return v___x_1991_;
}
else
{
return v_newNode_1984_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg(size_t v_depth_1999_, lean_object* v_keys_2000_, lean_object* v_vals_2001_, lean_object* v_i_2002_, lean_object* v_entries_2003_){
_start:
{
lean_object* v___x_2004_; uint8_t v___x_2005_; 
v___x_2004_ = lean_array_get_size(v_keys_2000_);
v___x_2005_ = lean_nat_dec_lt(v_i_2002_, v___x_2004_);
if (v___x_2005_ == 0)
{
lean_dec(v_i_2002_);
return v_entries_2003_;
}
else
{
lean_object* v_k_2006_; lean_object* v_v_2007_; uint64_t v___x_2008_; size_t v_h_2009_; size_t v___x_2010_; lean_object* v___x_2011_; size_t v___x_2012_; size_t v___x_2013_; size_t v___x_2014_; size_t v_h_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; 
v_k_2006_ = lean_array_fget_borrowed(v_keys_2000_, v_i_2002_);
v_v_2007_ = lean_array_fget_borrowed(v_vals_2001_, v_i_2002_);
v___x_2008_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_2006_);
v_h_2009_ = lean_uint64_to_usize(v___x_2008_);
v___x_2010_ = ((size_t)5ULL);
v___x_2011_ = lean_unsigned_to_nat(1u);
v___x_2012_ = ((size_t)1ULL);
v___x_2013_ = lean_usize_sub(v_depth_1999_, v___x_2012_);
v___x_2014_ = lean_usize_mul(v___x_2010_, v___x_2013_);
v_h_2015_ = lean_usize_shift_right(v_h_2009_, v___x_2014_);
v___x_2016_ = lean_nat_add(v_i_2002_, v___x_2011_);
lean_dec(v_i_2002_);
lean_inc(v_v_2007_);
lean_inc(v_k_2006_);
v___x_2017_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_entries_2003_, v_h_2015_, v_depth_1999_, v_k_2006_, v_v_2007_);
v_i_2002_ = v___x_2016_;
v_entries_2003_ = v___x_2017_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_2019_, lean_object* v_keys_2020_, lean_object* v_vals_2021_, lean_object* v_i_2022_, lean_object* v_entries_2023_){
_start:
{
size_t v_depth_boxed_2024_; lean_object* v_res_2025_; 
v_depth_boxed_2024_ = lean_unbox_usize(v_depth_2019_);
lean_dec(v_depth_2019_);
v_res_2025_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg(v_depth_boxed_2024_, v_keys_2020_, v_vals_2021_, v_i_2022_, v_entries_2023_);
lean_dec_ref(v_vals_2021_);
lean_dec_ref(v_keys_2020_);
return v_res_2025_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___boxed(lean_object* v_x_2026_, lean_object* v_x_2027_, lean_object* v_x_2028_, lean_object* v_x_2029_, lean_object* v_x_2030_){
_start:
{
size_t v_x_8479__boxed_2031_; size_t v_x_8480__boxed_2032_; lean_object* v_res_2033_; 
v_x_8479__boxed_2031_ = lean_unbox_usize(v_x_2027_);
lean_dec(v_x_2027_);
v_x_8480__boxed_2032_ = lean_unbox_usize(v_x_2028_);
lean_dec(v_x_2028_);
v_res_2033_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_x_2026_, v_x_8479__boxed_2031_, v_x_8480__boxed_2032_, v_x_2029_, v_x_2030_);
return v_res_2033_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0___redArg(lean_object* v_x_2034_, lean_object* v_x_2035_, lean_object* v_x_2036_){
_start:
{
uint64_t v___x_2037_; size_t v___x_2038_; size_t v___x_2039_; lean_object* v___x_2040_; 
v___x_2037_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_2035_);
v___x_2038_ = lean_uint64_to_usize(v___x_2037_);
v___x_2039_ = ((size_t)1ULL);
v___x_2040_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_x_2034_, v___x_2038_, v___x_2039_, v_x_2035_, v_x_2036_);
return v___x_2040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___lam__0(lean_object* v_e_2041_, lean_object* v_ringId_2042_, lean_object* v_s_2043_){
_start:
{
lean_object* v_rings_2044_; lean_object* v_typeIdOf_2045_; lean_object* v_exprToRingId_2046_; lean_object* v_semirings_2047_; lean_object* v_stypeIdOf_2048_; lean_object* v_exprToSemiringId_2049_; lean_object* v_ncRings_2050_; lean_object* v_exprToNCRingId_2051_; lean_object* v_nctypeIdOf_2052_; lean_object* v_ncSemirings_2053_; lean_object* v_exprToNCSemiringId_2054_; lean_object* v_ncstypeIdOf_2055_; lean_object* v_steps_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2064_; 
v_rings_2044_ = lean_ctor_get(v_s_2043_, 0);
v_typeIdOf_2045_ = lean_ctor_get(v_s_2043_, 1);
v_exprToRingId_2046_ = lean_ctor_get(v_s_2043_, 2);
v_semirings_2047_ = lean_ctor_get(v_s_2043_, 3);
v_stypeIdOf_2048_ = lean_ctor_get(v_s_2043_, 4);
v_exprToSemiringId_2049_ = lean_ctor_get(v_s_2043_, 5);
v_ncRings_2050_ = lean_ctor_get(v_s_2043_, 6);
v_exprToNCRingId_2051_ = lean_ctor_get(v_s_2043_, 7);
v_nctypeIdOf_2052_ = lean_ctor_get(v_s_2043_, 8);
v_ncSemirings_2053_ = lean_ctor_get(v_s_2043_, 9);
v_exprToNCSemiringId_2054_ = lean_ctor_get(v_s_2043_, 10);
v_ncstypeIdOf_2055_ = lean_ctor_get(v_s_2043_, 11);
v_steps_2056_ = lean_ctor_get(v_s_2043_, 12);
v_isSharedCheck_2064_ = !lean_is_exclusive(v_s_2043_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2058_ = v_s_2043_;
v_isShared_2059_ = v_isSharedCheck_2064_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_steps_2056_);
lean_inc(v_ncstypeIdOf_2055_);
lean_inc(v_exprToNCSemiringId_2054_);
lean_inc(v_ncSemirings_2053_);
lean_inc(v_nctypeIdOf_2052_);
lean_inc(v_exprToNCRingId_2051_);
lean_inc(v_ncRings_2050_);
lean_inc(v_exprToSemiringId_2049_);
lean_inc(v_stypeIdOf_2048_);
lean_inc(v_semirings_2047_);
lean_inc(v_exprToRingId_2046_);
lean_inc(v_typeIdOf_2045_);
lean_inc(v_rings_2044_);
lean_dec(v_s_2043_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2064_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v___x_2060_; lean_object* v___x_2062_; 
v___x_2060_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0___redArg(v_exprToRingId_2046_, v_e_2041_, v_ringId_2042_);
if (v_isShared_2059_ == 0)
{
lean_ctor_set(v___x_2058_, 2, v___x_2060_);
v___x_2062_ = v___x_2058_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v_rings_2044_);
lean_ctor_set(v_reuseFailAlloc_2063_, 1, v_typeIdOf_2045_);
lean_ctor_set(v_reuseFailAlloc_2063_, 2, v___x_2060_);
lean_ctor_set(v_reuseFailAlloc_2063_, 3, v_semirings_2047_);
lean_ctor_set(v_reuseFailAlloc_2063_, 4, v_stypeIdOf_2048_);
lean_ctor_set(v_reuseFailAlloc_2063_, 5, v_exprToSemiringId_2049_);
lean_ctor_set(v_reuseFailAlloc_2063_, 6, v_ncRings_2050_);
lean_ctor_set(v_reuseFailAlloc_2063_, 7, v_exprToNCRingId_2051_);
lean_ctor_set(v_reuseFailAlloc_2063_, 8, v_nctypeIdOf_2052_);
lean_ctor_set(v_reuseFailAlloc_2063_, 9, v_ncSemirings_2053_);
lean_ctor_set(v_reuseFailAlloc_2063_, 10, v_exprToNCSemiringId_2054_);
lean_ctor_set(v_reuseFailAlloc_2063_, 11, v_ncstypeIdOf_2055_);
lean_ctor_set(v_reuseFailAlloc_2063_, 12, v_steps_2056_);
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
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___closed__1(void){
_start:
{
lean_object* v___x_2066_; lean_object* v___x_2067_; 
v___x_2066_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___closed__0));
v___x_2067_ = l_Lean_stringToMessageData(v___x_2066_);
return v___x_2067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId(lean_object* v_e_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_, lean_object* v_a_2073_, lean_object* v_a_2074_, lean_object* v_a_2075_, lean_object* v_a_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_){
_start:
{
lean_object* v___x_2084_; 
v___x_2084_ = l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg(v_e_2068_, v_a_2070_, v_a_2078_);
if (lean_obj_tag(v___x_2084_) == 0)
{
lean_object* v_a_2085_; 
v_a_2085_ = lean_ctor_get(v___x_2084_, 0);
lean_inc(v_a_2085_);
lean_dec_ref(v___x_2084_);
if (lean_obj_tag(v_a_2085_) == 1)
{
lean_object* v_ringId_2086_; lean_object* v_val_2087_; uint8_t v___x_2088_; 
v_ringId_2086_ = lean_ctor_get(v_a_2069_, 0);
lean_inc(v_ringId_2086_);
lean_dec_ref(v_a_2069_);
v_val_2087_ = lean_ctor_get(v_a_2085_, 0);
lean_inc(v_val_2087_);
lean_dec_ref(v_a_2085_);
v___x_2088_ = lean_nat_dec_eq(v_val_2087_, v_ringId_2086_);
lean_dec(v_ringId_2086_);
lean_dec(v_val_2087_);
if (v___x_2088_ == 0)
{
lean_object* v___x_2089_; 
v___x_2089_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_2072_);
if (lean_obj_tag(v___x_2089_) == 0)
{
lean_object* v_a_2090_; uint8_t v_verbose_2091_; 
v_a_2090_ = lean_ctor_get(v___x_2089_, 0);
lean_inc(v_a_2090_);
lean_dec_ref(v___x_2089_);
v_verbose_2091_ = lean_ctor_get_uint8(v_a_2090_, sizeof(void*)*11 + 15);
lean_dec(v_a_2090_);
if (v_verbose_2091_ == 0)
{
lean_dec_ref(v_e_2068_);
goto v___jp_2081_;
}
else
{
lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; 
v___x_2092_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___closed__1);
v___x_2093_ = l_Lean_indentExpr(v_e_2068_);
v___x_2094_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2094_, 0, v___x_2092_);
lean_ctor_set(v___x_2094_, 1, v___x_2093_);
v___x_2095_ = l_Lean_Meta_Grind_reportIssue(v___x_2094_, v_a_2071_, v_a_2072_, v_a_2073_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_);
if (lean_obj_tag(v___x_2095_) == 0)
{
lean_dec_ref(v___x_2095_);
goto v___jp_2081_;
}
else
{
return v___x_2095_;
}
}
}
else
{
lean_object* v_a_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2103_; 
lean_dec_ref(v_e_2068_);
v_a_2096_ = lean_ctor_get(v___x_2089_, 0);
v_isSharedCheck_2103_ = !lean_is_exclusive(v___x_2089_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_2098_ = v___x_2089_;
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_a_2096_);
lean_dec(v___x_2089_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
lean_object* v___x_2101_; 
if (v_isShared_2099_ == 0)
{
v___x_2101_ = v___x_2098_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v_a_2096_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
return v___x_2101_;
}
}
}
}
else
{
lean_dec_ref(v_e_2068_);
goto v___jp_2081_;
}
}
else
{
lean_object* v_ringId_2104_; lean_object* v___f_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; 
lean_dec(v_a_2085_);
v_ringId_2104_ = lean_ctor_get(v_a_2069_, 0);
lean_inc(v_ringId_2104_);
lean_dec_ref(v_a_2069_);
v___f_2105_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___lam__0), 3, 2);
lean_closure_set(v___f_2105_, 0, v_e_2068_);
lean_closure_set(v___f_2105_, 1, v_ringId_2104_);
v___x_2106_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_2107_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2106_, v___f_2105_, v_a_2070_);
return v___x_2107_;
}
}
else
{
lean_object* v_a_2108_; lean_object* v___x_2110_; uint8_t v_isShared_2111_; uint8_t v_isSharedCheck_2115_; 
lean_dec_ref(v_a_2069_);
lean_dec_ref(v_e_2068_);
v_a_2108_ = lean_ctor_get(v___x_2084_, 0);
v_isSharedCheck_2115_ = !lean_is_exclusive(v___x_2084_);
if (v_isSharedCheck_2115_ == 0)
{
v___x_2110_ = v___x_2084_;
v_isShared_2111_ = v_isSharedCheck_2115_;
goto v_resetjp_2109_;
}
else
{
lean_inc(v_a_2108_);
lean_dec(v___x_2084_);
v___x_2110_ = lean_box(0);
v_isShared_2111_ = v_isSharedCheck_2115_;
goto v_resetjp_2109_;
}
v_resetjp_2109_:
{
lean_object* v___x_2113_; 
if (v_isShared_2111_ == 0)
{
v___x_2113_ = v___x_2110_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v_a_2108_);
v___x_2113_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
return v___x_2113_;
}
}
}
v___jp_2081_:
{
lean_object* v___x_2082_; lean_object* v___x_2083_; 
v___x_2082_ = lean_box(0);
v___x_2083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2083_, 0, v___x_2082_);
return v___x_2083_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___boxed(lean_object* v_e_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_){
_start:
{
lean_object* v_res_2129_; 
v_res_2129_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId(v_e_2116_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_, v_a_2122_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_);
lean_dec(v_a_2127_);
lean_dec_ref(v_a_2126_);
lean_dec(v_a_2125_);
lean_dec_ref(v_a_2124_);
lean_dec(v_a_2123_);
lean_dec_ref(v_a_2122_);
lean_dec(v_a_2121_);
lean_dec_ref(v_a_2120_);
lean_dec(v_a_2119_);
lean_dec(v_a_2118_);
return v_res_2129_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0(lean_object* v_00_u03b2_2130_, lean_object* v_x_2131_, lean_object* v_x_2132_, lean_object* v_x_2133_){
_start:
{
lean_object* v___x_2134_; 
v___x_2134_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0___redArg(v_x_2131_, v_x_2132_, v_x_2133_);
return v___x_2134_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0(lean_object* v_00_u03b2_2135_, lean_object* v_x_2136_, size_t v_x_2137_, size_t v_x_2138_, lean_object* v_x_2139_, lean_object* v_x_2140_){
_start:
{
lean_object* v___x_2141_; 
v___x_2141_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_x_2136_, v_x_2137_, v_x_2138_, v_x_2139_, v_x_2140_);
return v___x_2141_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2142_, lean_object* v_x_2143_, lean_object* v_x_2144_, lean_object* v_x_2145_, lean_object* v_x_2146_, lean_object* v_x_2147_){
_start:
{
size_t v_x_8784__boxed_2148_; size_t v_x_8785__boxed_2149_; lean_object* v_res_2150_; 
v_x_8784__boxed_2148_ = lean_unbox_usize(v_x_2144_);
lean_dec(v_x_2144_);
v_x_8785__boxed_2149_ = lean_unbox_usize(v_x_2145_);
lean_dec(v_x_2145_);
v_res_2150_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0(v_00_u03b2_2142_, v_x_2143_, v_x_8784__boxed_2148_, v_x_8785__boxed_2149_, v_x_2146_, v_x_2147_);
return v_res_2150_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2151_, lean_object* v_n_2152_, lean_object* v_k_2153_, lean_object* v_v_2154_){
_start:
{
lean_object* v___x_2155_; 
v___x_2155_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1___redArg(v_n_2152_, v_k_2153_, v_v_2154_);
return v___x_2155_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_2156_, size_t v_depth_2157_, lean_object* v_keys_2158_, lean_object* v_vals_2159_, lean_object* v_heq_2160_, lean_object* v_i_2161_, lean_object* v_entries_2162_){
_start:
{
lean_object* v___x_2163_; 
v___x_2163_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg(v_depth_2157_, v_keys_2158_, v_vals_2159_, v_i_2161_, v_entries_2162_);
return v___x_2163_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2164_, lean_object* v_depth_2165_, lean_object* v_keys_2166_, lean_object* v_vals_2167_, lean_object* v_heq_2168_, lean_object* v_i_2169_, lean_object* v_entries_2170_){
_start:
{
size_t v_depth_boxed_2171_; lean_object* v_res_2172_; 
v_depth_boxed_2171_ = lean_unbox_usize(v_depth_2165_);
lean_dec(v_depth_2165_);
v_res_2172_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2(v_00_u03b2_2164_, v_depth_boxed_2171_, v_keys_2166_, v_vals_2167_, v_heq_2168_, v_i_2169_, v_entries_2170_);
lean_dec_ref(v_vals_2167_);
lean_dec_ref(v_keys_2166_);
return v_res_2172_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2173_, lean_object* v_x_2174_, lean_object* v_x_2175_, lean_object* v_x_2176_, lean_object* v_x_2177_){
_start:
{
lean_object* v___x_2178_; 
v___x_2178_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1_spec__2___redArg(v_x_2174_, v_x_2175_, v_x_2176_, v_x_2177_);
return v___x_2178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__0(lean_object* v_e_2179_, lean_object* v___f_2180_, lean_object* v___f_2181_, lean_object* v_size_2182_, lean_object* v_s_2183_){
_start:
{
lean_object* v_id_2184_; lean_object* v_type_2185_; lean_object* v_u_2186_; lean_object* v_ringInst_2187_; lean_object* v_semiringInst_2188_; lean_object* v_charInst_x3f_2189_; lean_object* v_addFn_x3f_2190_; lean_object* v_mulFn_x3f_2191_; lean_object* v_subFn_x3f_2192_; lean_object* v_negFn_x3f_2193_; lean_object* v_powFn_x3f_2194_; lean_object* v_intCastFn_x3f_2195_; lean_object* v_natCastFn_x3f_2196_; lean_object* v_one_x3f_2197_; lean_object* v_vars_2198_; lean_object* v_varMap_2199_; lean_object* v_denote_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2209_; 
v_id_2184_ = lean_ctor_get(v_s_2183_, 0);
v_type_2185_ = lean_ctor_get(v_s_2183_, 1);
v_u_2186_ = lean_ctor_get(v_s_2183_, 2);
v_ringInst_2187_ = lean_ctor_get(v_s_2183_, 3);
v_semiringInst_2188_ = lean_ctor_get(v_s_2183_, 4);
v_charInst_x3f_2189_ = lean_ctor_get(v_s_2183_, 5);
v_addFn_x3f_2190_ = lean_ctor_get(v_s_2183_, 6);
v_mulFn_x3f_2191_ = lean_ctor_get(v_s_2183_, 7);
v_subFn_x3f_2192_ = lean_ctor_get(v_s_2183_, 8);
v_negFn_x3f_2193_ = lean_ctor_get(v_s_2183_, 9);
v_powFn_x3f_2194_ = lean_ctor_get(v_s_2183_, 10);
v_intCastFn_x3f_2195_ = lean_ctor_get(v_s_2183_, 11);
v_natCastFn_x3f_2196_ = lean_ctor_get(v_s_2183_, 12);
v_one_x3f_2197_ = lean_ctor_get(v_s_2183_, 13);
v_vars_2198_ = lean_ctor_get(v_s_2183_, 14);
v_varMap_2199_ = lean_ctor_get(v_s_2183_, 15);
v_denote_2200_ = lean_ctor_get(v_s_2183_, 16);
v_isSharedCheck_2209_ = !lean_is_exclusive(v_s_2183_);
if (v_isSharedCheck_2209_ == 0)
{
v___x_2202_ = v_s_2183_;
v_isShared_2203_ = v_isSharedCheck_2209_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_denote_2200_);
lean_inc(v_varMap_2199_);
lean_inc(v_vars_2198_);
lean_inc(v_one_x3f_2197_);
lean_inc(v_natCastFn_x3f_2196_);
lean_inc(v_intCastFn_x3f_2195_);
lean_inc(v_powFn_x3f_2194_);
lean_inc(v_negFn_x3f_2193_);
lean_inc(v_subFn_x3f_2192_);
lean_inc(v_mulFn_x3f_2191_);
lean_inc(v_addFn_x3f_2190_);
lean_inc(v_charInst_x3f_2189_);
lean_inc(v_semiringInst_2188_);
lean_inc(v_ringInst_2187_);
lean_inc(v_u_2186_);
lean_inc(v_type_2185_);
lean_inc(v_id_2184_);
lean_dec(v_s_2183_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2209_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2207_; 
lean_inc_ref(v_e_2179_);
v___x_2204_ = l_Lean_PersistentArray_push___redArg(v_vars_2198_, v_e_2179_);
v___x_2205_ = l_Lean_PersistentHashMap_insert___redArg(v___f_2180_, v___f_2181_, v_varMap_2199_, v_e_2179_, v_size_2182_);
if (v_isShared_2203_ == 0)
{
lean_ctor_set(v___x_2202_, 15, v___x_2205_);
lean_ctor_set(v___x_2202_, 14, v___x_2204_);
v___x_2207_ = v___x_2202_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v_id_2184_);
lean_ctor_set(v_reuseFailAlloc_2208_, 1, v_type_2185_);
lean_ctor_set(v_reuseFailAlloc_2208_, 2, v_u_2186_);
lean_ctor_set(v_reuseFailAlloc_2208_, 3, v_ringInst_2187_);
lean_ctor_set(v_reuseFailAlloc_2208_, 4, v_semiringInst_2188_);
lean_ctor_set(v_reuseFailAlloc_2208_, 5, v_charInst_x3f_2189_);
lean_ctor_set(v_reuseFailAlloc_2208_, 6, v_addFn_x3f_2190_);
lean_ctor_set(v_reuseFailAlloc_2208_, 7, v_mulFn_x3f_2191_);
lean_ctor_set(v_reuseFailAlloc_2208_, 8, v_subFn_x3f_2192_);
lean_ctor_set(v_reuseFailAlloc_2208_, 9, v_negFn_x3f_2193_);
lean_ctor_set(v_reuseFailAlloc_2208_, 10, v_powFn_x3f_2194_);
lean_ctor_set(v_reuseFailAlloc_2208_, 11, v_intCastFn_x3f_2195_);
lean_ctor_set(v_reuseFailAlloc_2208_, 12, v_natCastFn_x3f_2196_);
lean_ctor_set(v_reuseFailAlloc_2208_, 13, v_one_x3f_2197_);
lean_ctor_set(v_reuseFailAlloc_2208_, 14, v___x_2204_);
lean_ctor_set(v_reuseFailAlloc_2208_, 15, v___x_2205_);
lean_ctor_set(v_reuseFailAlloc_2208_, 16, v_denote_2200_);
v___x_2207_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
return v___x_2207_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__1(lean_object* v_toPure_2210_, lean_object* v_size_2211_, lean_object* v_____r_2212_){
_start:
{
lean_object* v___x_2213_; 
v___x_2213_ = lean_apply_2(v_toPure_2210_, lean_box(0), v_size_2211_);
return v___x_2213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__2(lean_object* v_e_2214_, lean_object* v_inst_2215_, lean_object* v_toBind_2216_, lean_object* v___f_2217_, lean_object* v_____r_2218_){
_start:
{
lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; 
v___x_2219_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_2220_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_SolverExtension_markTerm___boxed), 14, 3);
lean_closure_set(v___x_2220_, 0, lean_box(0));
lean_closure_set(v___x_2220_, 1, v___x_2219_);
lean_closure_set(v___x_2220_, 2, v_e_2214_);
v___x_2221_ = lean_apply_2(v_inst_2215_, lean_box(0), v___x_2220_);
v___x_2222_ = lean_apply_4(v_toBind_2216_, lean_box(0), lean_box(0), v___x_2221_, v___f_2217_);
return v___x_2222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__3(lean_object* v_inst_2223_, lean_object* v_e_2224_, lean_object* v_toBind_2225_, lean_object* v___f_2226_, lean_object* v_____r_2227_){
_start:
{
lean_object* v___x_2228_; lean_object* v___x_2229_; 
v___x_2228_ = lean_apply_1(v_inst_2223_, v_e_2224_);
v___x_2229_ = lean_apply_4(v_toBind_2225_, lean_box(0), lean_box(0), v___x_2228_, v___f_2226_);
return v___x_2229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__4(lean_object* v___f_2230_, lean_object* v___f_2231_, lean_object* v_e_2232_, lean_object* v_toPure_2233_, lean_object* v_inst_2234_, lean_object* v_toBind_2235_, lean_object* v_inst_2236_, lean_object* v_modifyRing_2237_, lean_object* v_s_2238_){
_start:
{
lean_object* v_vars_2239_; lean_object* v_varMap_2240_; lean_object* v___x_2241_; 
v_vars_2239_ = lean_ctor_get(v_s_2238_, 14);
lean_inc_ref(v_vars_2239_);
v_varMap_2240_ = lean_ctor_get(v_s_2238_, 15);
lean_inc_ref(v_varMap_2240_);
lean_dec_ref(v_s_2238_);
lean_inc_ref(v_e_2232_);
lean_inc_ref(v___f_2231_);
lean_inc_ref(v___f_2230_);
v___x_2241_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_2230_, v___f_2231_, v_varMap_2240_, v_e_2232_);
if (lean_obj_tag(v___x_2241_) == 1)
{
lean_object* v_val_2242_; lean_object* v___x_2243_; 
lean_dec_ref(v_vars_2239_);
lean_dec(v_modifyRing_2237_);
lean_dec(v_inst_2236_);
lean_dec(v_toBind_2235_);
lean_dec(v_inst_2234_);
lean_dec_ref(v_e_2232_);
lean_dec_ref(v___f_2231_);
lean_dec_ref(v___f_2230_);
v_val_2242_ = lean_ctor_get(v___x_2241_, 0);
lean_inc(v_val_2242_);
lean_dec_ref(v___x_2241_);
v___x_2243_ = lean_apply_2(v_toPure_2233_, lean_box(0), v_val_2242_);
return v___x_2243_;
}
else
{
lean_object* v_size_2244_; lean_object* v___f_2245_; lean_object* v___f_2246_; lean_object* v___f_2247_; lean_object* v___f_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; 
lean_dec(v___x_2241_);
v_size_2244_ = lean_ctor_get(v_vars_2239_, 2);
lean_inc(v_size_2244_);
lean_dec_ref(v_vars_2239_);
lean_inc(v_size_2244_);
lean_inc_ref(v_e_2232_);
v___f_2245_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2245_, 0, v_e_2232_);
lean_closure_set(v___f_2245_, 1, v___f_2230_);
lean_closure_set(v___f_2245_, 2, v___f_2231_);
lean_closure_set(v___f_2245_, 3, v_size_2244_);
v___f_2246_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2246_, 0, v_toPure_2233_);
lean_closure_set(v___f_2246_, 1, v_size_2244_);
lean_inc(v_toBind_2235_);
lean_inc_ref(v_e_2232_);
v___f_2247_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2247_, 0, v_e_2232_);
lean_closure_set(v___f_2247_, 1, v_inst_2234_);
lean_closure_set(v___f_2247_, 2, v_toBind_2235_);
lean_closure_set(v___f_2247_, 3, v___f_2246_);
lean_inc(v_toBind_2235_);
v___f_2248_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__3), 5, 4);
lean_closure_set(v___f_2248_, 0, v_inst_2236_);
lean_closure_set(v___f_2248_, 1, v_e_2232_);
lean_closure_set(v___f_2248_, 2, v_toBind_2235_);
lean_closure_set(v___f_2248_, 3, v___f_2247_);
v___x_2249_ = lean_apply_1(v_modifyRing_2237_, v___f_2245_);
v___x_2250_ = lean_apply_4(v_toBind_2235_, lean_box(0), lean_box(0), v___x_2249_, v___f_2248_);
return v___x_2250_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg(lean_object* v_inst_2253_, lean_object* v_inst_2254_, lean_object* v_inst_2255_, lean_object* v_inst_2256_, lean_object* v_e_2257_){
_start:
{
lean_object* v_toApplicative_2258_; lean_object* v_toBind_2259_; lean_object* v_getRing_2260_; lean_object* v_modifyRing_2261_; lean_object* v_toPure_2262_; lean_object* v___f_2263_; lean_object* v___f_2264_; lean_object* v___f_2265_; lean_object* v___x_2266_; 
v_toApplicative_2258_ = lean_ctor_get(v_inst_2254_, 0);
lean_inc_ref(v_toApplicative_2258_);
v_toBind_2259_ = lean_ctor_get(v_inst_2254_, 1);
lean_inc(v_toBind_2259_);
lean_dec_ref(v_inst_2254_);
v_getRing_2260_ = lean_ctor_get(v_inst_2255_, 0);
lean_inc(v_getRing_2260_);
v_modifyRing_2261_ = lean_ctor_get(v_inst_2255_, 1);
lean_inc(v_modifyRing_2261_);
lean_dec_ref(v_inst_2255_);
v_toPure_2262_ = lean_ctor_get(v_toApplicative_2258_, 1);
lean_inc(v_toPure_2262_);
lean_dec_ref(v_toApplicative_2258_);
v___f_2263_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___closed__0));
v___f_2264_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___closed__1));
lean_inc(v_toBind_2259_);
v___f_2265_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__4), 9, 8);
lean_closure_set(v___f_2265_, 0, v___f_2263_);
lean_closure_set(v___f_2265_, 1, v___f_2264_);
lean_closure_set(v___f_2265_, 2, v_e_2257_);
lean_closure_set(v___f_2265_, 3, v_toPure_2262_);
lean_closure_set(v___f_2265_, 4, v_inst_2253_);
lean_closure_set(v___f_2265_, 5, v_toBind_2259_);
lean_closure_set(v___f_2265_, 6, v_inst_2256_);
lean_closure_set(v___f_2265_, 7, v_modifyRing_2261_);
v___x_2266_ = lean_apply_4(v_toBind_2259_, lean_box(0), lean_box(0), v_getRing_2260_, v___f_2265_);
return v___x_2266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore(lean_object* v_m_2267_, lean_object* v_inst_2268_, lean_object* v_inst_2269_, lean_object* v_inst_2270_, lean_object* v_inst_2271_, lean_object* v_e_2272_){
_start:
{
lean_object* v___x_2273_; 
v___x_2273_ = l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg(v_inst_2268_, v_inst_2269_, v_inst_2270_, v_inst_2271_, v_e_2272_);
return v___x_2273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkVar_spec__0___lam__0(lean_object* v_e_2276_, lean_object* v_size_2277_, lean_object* v_s_2278_){
_start:
{
lean_object* v_toRing_2279_; lean_object* v_invFn_x3f_2280_; lean_object* v_semiringId_x3f_2281_; lean_object* v_commSemiringInst_2282_; lean_object* v_commRingInst_2283_; lean_object* v_noZeroDivInst_x3f_2284_; lean_object* v_fieldInst_x3f_2285_; lean_object* v_denoteEntries_2286_; lean_object* v_nextId_2287_; lean_object* v_steps_2288_; lean_object* v_queue_2289_; lean_object* v_basis_2290_; lean_object* v_diseqs_2291_; uint8_t v_recheck_2292_; lean_object* v_invSet_2293_; lean_object* v_numEq0_x3f_2294_; uint8_t v_numEq0Updated_2295_; lean_object* v___x_2297_; uint8_t v_isShared_2298_; uint8_t v_isSharedCheck_2328_; 
v_toRing_2279_ = lean_ctor_get(v_s_2278_, 0);
v_invFn_x3f_2280_ = lean_ctor_get(v_s_2278_, 1);
v_semiringId_x3f_2281_ = lean_ctor_get(v_s_2278_, 2);
v_commSemiringInst_2282_ = lean_ctor_get(v_s_2278_, 3);
v_commRingInst_2283_ = lean_ctor_get(v_s_2278_, 4);
v_noZeroDivInst_x3f_2284_ = lean_ctor_get(v_s_2278_, 5);
v_fieldInst_x3f_2285_ = lean_ctor_get(v_s_2278_, 6);
v_denoteEntries_2286_ = lean_ctor_get(v_s_2278_, 7);
v_nextId_2287_ = lean_ctor_get(v_s_2278_, 8);
v_steps_2288_ = lean_ctor_get(v_s_2278_, 9);
v_queue_2289_ = lean_ctor_get(v_s_2278_, 10);
v_basis_2290_ = lean_ctor_get(v_s_2278_, 11);
v_diseqs_2291_ = lean_ctor_get(v_s_2278_, 12);
v_recheck_2292_ = lean_ctor_get_uint8(v_s_2278_, sizeof(void*)*15);
v_invSet_2293_ = lean_ctor_get(v_s_2278_, 13);
v_numEq0_x3f_2294_ = lean_ctor_get(v_s_2278_, 14);
v_numEq0Updated_2295_ = lean_ctor_get_uint8(v_s_2278_, sizeof(void*)*15 + 1);
v_isSharedCheck_2328_ = !lean_is_exclusive(v_s_2278_);
if (v_isSharedCheck_2328_ == 0)
{
v___x_2297_ = v_s_2278_;
v_isShared_2298_ = v_isSharedCheck_2328_;
goto v_resetjp_2296_;
}
else
{
lean_inc(v_numEq0_x3f_2294_);
lean_inc(v_invSet_2293_);
lean_inc(v_diseqs_2291_);
lean_inc(v_basis_2290_);
lean_inc(v_queue_2289_);
lean_inc(v_steps_2288_);
lean_inc(v_nextId_2287_);
lean_inc(v_denoteEntries_2286_);
lean_inc(v_fieldInst_x3f_2285_);
lean_inc(v_noZeroDivInst_x3f_2284_);
lean_inc(v_commRingInst_2283_);
lean_inc(v_commSemiringInst_2282_);
lean_inc(v_semiringId_x3f_2281_);
lean_inc(v_invFn_x3f_2280_);
lean_inc(v_toRing_2279_);
lean_dec(v_s_2278_);
v___x_2297_ = lean_box(0);
v_isShared_2298_ = v_isSharedCheck_2328_;
goto v_resetjp_2296_;
}
v_resetjp_2296_:
{
lean_object* v_id_2299_; lean_object* v_type_2300_; lean_object* v_u_2301_; lean_object* v_ringInst_2302_; lean_object* v_semiringInst_2303_; lean_object* v_charInst_x3f_2304_; lean_object* v_addFn_x3f_2305_; lean_object* v_mulFn_x3f_2306_; lean_object* v_subFn_x3f_2307_; lean_object* v_negFn_x3f_2308_; lean_object* v_powFn_x3f_2309_; lean_object* v_intCastFn_x3f_2310_; lean_object* v_natCastFn_x3f_2311_; lean_object* v_one_x3f_2312_; lean_object* v_vars_2313_; lean_object* v_varMap_2314_; lean_object* v_denote_2315_; lean_object* v___x_2317_; uint8_t v_isShared_2318_; uint8_t v_isSharedCheck_2327_; 
v_id_2299_ = lean_ctor_get(v_toRing_2279_, 0);
v_type_2300_ = lean_ctor_get(v_toRing_2279_, 1);
v_u_2301_ = lean_ctor_get(v_toRing_2279_, 2);
v_ringInst_2302_ = lean_ctor_get(v_toRing_2279_, 3);
v_semiringInst_2303_ = lean_ctor_get(v_toRing_2279_, 4);
v_charInst_x3f_2304_ = lean_ctor_get(v_toRing_2279_, 5);
v_addFn_x3f_2305_ = lean_ctor_get(v_toRing_2279_, 6);
v_mulFn_x3f_2306_ = lean_ctor_get(v_toRing_2279_, 7);
v_subFn_x3f_2307_ = lean_ctor_get(v_toRing_2279_, 8);
v_negFn_x3f_2308_ = lean_ctor_get(v_toRing_2279_, 9);
v_powFn_x3f_2309_ = lean_ctor_get(v_toRing_2279_, 10);
v_intCastFn_x3f_2310_ = lean_ctor_get(v_toRing_2279_, 11);
v_natCastFn_x3f_2311_ = lean_ctor_get(v_toRing_2279_, 12);
v_one_x3f_2312_ = lean_ctor_get(v_toRing_2279_, 13);
v_vars_2313_ = lean_ctor_get(v_toRing_2279_, 14);
v_varMap_2314_ = lean_ctor_get(v_toRing_2279_, 15);
v_denote_2315_ = lean_ctor_get(v_toRing_2279_, 16);
v_isSharedCheck_2327_ = !lean_is_exclusive(v_toRing_2279_);
if (v_isSharedCheck_2327_ == 0)
{
v___x_2317_ = v_toRing_2279_;
v_isShared_2318_ = v_isSharedCheck_2327_;
goto v_resetjp_2316_;
}
else
{
lean_inc(v_denote_2315_);
lean_inc(v_varMap_2314_);
lean_inc(v_vars_2313_);
lean_inc(v_one_x3f_2312_);
lean_inc(v_natCastFn_x3f_2311_);
lean_inc(v_intCastFn_x3f_2310_);
lean_inc(v_powFn_x3f_2309_);
lean_inc(v_negFn_x3f_2308_);
lean_inc(v_subFn_x3f_2307_);
lean_inc(v_mulFn_x3f_2306_);
lean_inc(v_addFn_x3f_2305_);
lean_inc(v_charInst_x3f_2304_);
lean_inc(v_semiringInst_2303_);
lean_inc(v_ringInst_2302_);
lean_inc(v_u_2301_);
lean_inc(v_type_2300_);
lean_inc(v_id_2299_);
lean_dec(v_toRing_2279_);
v___x_2317_ = lean_box(0);
v_isShared_2318_ = v_isSharedCheck_2327_;
goto v_resetjp_2316_;
}
v_resetjp_2316_:
{
lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2322_; 
lean_inc_ref(v_e_2276_);
v___x_2319_ = l_Lean_PersistentArray_push___redArg(v_vars_2313_, v_e_2276_);
v___x_2320_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0___redArg(v_varMap_2314_, v_e_2276_, v_size_2277_);
if (v_isShared_2318_ == 0)
{
lean_ctor_set(v___x_2317_, 15, v___x_2320_);
lean_ctor_set(v___x_2317_, 14, v___x_2319_);
v___x_2322_ = v___x_2317_;
goto v_reusejp_2321_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v_id_2299_);
lean_ctor_set(v_reuseFailAlloc_2326_, 1, v_type_2300_);
lean_ctor_set(v_reuseFailAlloc_2326_, 2, v_u_2301_);
lean_ctor_set(v_reuseFailAlloc_2326_, 3, v_ringInst_2302_);
lean_ctor_set(v_reuseFailAlloc_2326_, 4, v_semiringInst_2303_);
lean_ctor_set(v_reuseFailAlloc_2326_, 5, v_charInst_x3f_2304_);
lean_ctor_set(v_reuseFailAlloc_2326_, 6, v_addFn_x3f_2305_);
lean_ctor_set(v_reuseFailAlloc_2326_, 7, v_mulFn_x3f_2306_);
lean_ctor_set(v_reuseFailAlloc_2326_, 8, v_subFn_x3f_2307_);
lean_ctor_set(v_reuseFailAlloc_2326_, 9, v_negFn_x3f_2308_);
lean_ctor_set(v_reuseFailAlloc_2326_, 10, v_powFn_x3f_2309_);
lean_ctor_set(v_reuseFailAlloc_2326_, 11, v_intCastFn_x3f_2310_);
lean_ctor_set(v_reuseFailAlloc_2326_, 12, v_natCastFn_x3f_2311_);
lean_ctor_set(v_reuseFailAlloc_2326_, 13, v_one_x3f_2312_);
lean_ctor_set(v_reuseFailAlloc_2326_, 14, v___x_2319_);
lean_ctor_set(v_reuseFailAlloc_2326_, 15, v___x_2320_);
lean_ctor_set(v_reuseFailAlloc_2326_, 16, v_denote_2315_);
v___x_2322_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2321_;
}
v_reusejp_2321_:
{
lean_object* v___x_2324_; 
if (v_isShared_2298_ == 0)
{
lean_ctor_set(v___x_2297_, 0, v___x_2322_);
v___x_2324_ = v___x_2297_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(0, 15, 2);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v___x_2322_);
lean_ctor_set(v_reuseFailAlloc_2325_, 1, v_invFn_x3f_2280_);
lean_ctor_set(v_reuseFailAlloc_2325_, 2, v_semiringId_x3f_2281_);
lean_ctor_set(v_reuseFailAlloc_2325_, 3, v_commSemiringInst_2282_);
lean_ctor_set(v_reuseFailAlloc_2325_, 4, v_commRingInst_2283_);
lean_ctor_set(v_reuseFailAlloc_2325_, 5, v_noZeroDivInst_x3f_2284_);
lean_ctor_set(v_reuseFailAlloc_2325_, 6, v_fieldInst_x3f_2285_);
lean_ctor_set(v_reuseFailAlloc_2325_, 7, v_denoteEntries_2286_);
lean_ctor_set(v_reuseFailAlloc_2325_, 8, v_nextId_2287_);
lean_ctor_set(v_reuseFailAlloc_2325_, 9, v_steps_2288_);
lean_ctor_set(v_reuseFailAlloc_2325_, 10, v_queue_2289_);
lean_ctor_set(v_reuseFailAlloc_2325_, 11, v_basis_2290_);
lean_ctor_set(v_reuseFailAlloc_2325_, 12, v_diseqs_2291_);
lean_ctor_set(v_reuseFailAlloc_2325_, 13, v_invSet_2293_);
lean_ctor_set(v_reuseFailAlloc_2325_, 14, v_numEq0_x3f_2294_);
lean_ctor_set_uint8(v_reuseFailAlloc_2325_, sizeof(void*)*15, v_recheck_2292_);
lean_ctor_set_uint8(v_reuseFailAlloc_2325_, sizeof(void*)*15 + 1, v_numEq0Updated_2295_);
v___x_2324_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
return v___x_2324_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkVar_spec__0(lean_object* v_e_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_){
_start:
{
lean_object* v___x_2342_; 
v___x_2342_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_);
if (lean_obj_tag(v___x_2342_) == 0)
{
lean_object* v_a_2343_; lean_object* v___x_2345_; uint8_t v_isShared_2346_; uint8_t v_isSharedCheck_2393_; 
v_a_2343_ = lean_ctor_get(v___x_2342_, 0);
v_isSharedCheck_2393_ = !lean_is_exclusive(v___x_2342_);
if (v_isSharedCheck_2393_ == 0)
{
v___x_2345_ = v___x_2342_;
v_isShared_2346_ = v_isSharedCheck_2393_;
goto v_resetjp_2344_;
}
else
{
lean_inc(v_a_2343_);
lean_dec(v___x_2342_);
v___x_2345_ = lean_box(0);
v_isShared_2346_ = v_isSharedCheck_2393_;
goto v_resetjp_2344_;
}
v_resetjp_2344_:
{
lean_object* v_toRing_2347_; lean_object* v_vars_2348_; lean_object* v_varMap_2349_; lean_object* v___x_2350_; 
v_toRing_2347_ = lean_ctor_get(v_a_2343_, 0);
lean_inc_ref(v_toRing_2347_);
lean_dec(v_a_2343_);
v_vars_2348_ = lean_ctor_get(v_toRing_2347_, 14);
lean_inc_ref(v_vars_2348_);
v_varMap_2349_ = lean_ctor_get(v_toRing_2347_, 15);
lean_inc_ref(v_varMap_2349_);
lean_dec_ref(v_toRing_2347_);
v___x_2350_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(v_varMap_2349_, v_e_2329_);
if (lean_obj_tag(v___x_2350_) == 1)
{
lean_object* v_val_2351_; lean_object* v___x_2353_; 
lean_dec_ref(v_vars_2348_);
lean_dec(v___y_2340_);
lean_dec_ref(v___y_2339_);
lean_dec(v___y_2338_);
lean_dec_ref(v___y_2337_);
lean_dec(v___y_2336_);
lean_dec_ref(v___y_2335_);
lean_dec(v___y_2334_);
lean_dec_ref(v___y_2333_);
lean_dec(v___y_2332_);
lean_dec(v___y_2331_);
lean_dec_ref(v___y_2330_);
lean_dec_ref(v_e_2329_);
v_val_2351_ = lean_ctor_get(v___x_2350_, 0);
lean_inc(v_val_2351_);
lean_dec_ref(v___x_2350_);
if (v_isShared_2346_ == 0)
{
lean_ctor_set(v___x_2345_, 0, v_val_2351_);
v___x_2353_ = v___x_2345_;
goto v_reusejp_2352_;
}
else
{
lean_object* v_reuseFailAlloc_2354_; 
v_reuseFailAlloc_2354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2354_, 0, v_val_2351_);
v___x_2353_ = v_reuseFailAlloc_2354_;
goto v_reusejp_2352_;
}
v_reusejp_2352_:
{
return v___x_2353_;
}
}
else
{
lean_object* v_size_2355_; lean_object* v___f_2356_; lean_object* v___x_2357_; 
lean_dec(v___x_2350_);
lean_del_object(v___x_2345_);
v_size_2355_ = lean_ctor_get(v_vars_2348_, 2);
lean_inc(v_size_2355_);
lean_dec_ref(v_vars_2348_);
lean_inc(v_size_2355_);
lean_inc_ref(v_e_2329_);
v___f_2356_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkVar_spec__0___lam__0), 3, 2);
lean_closure_set(v___f_2356_, 0, v_e_2329_);
lean_closure_set(v___f_2356_, 1, v_size_2355_);
lean_inc_ref(v___y_2330_);
v___x_2357_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_2356_, v___y_2330_, v___y_2331_);
if (lean_obj_tag(v___x_2357_) == 0)
{
lean_object* v___x_2358_; 
lean_dec_ref(v___x_2357_);
lean_inc_ref(v_e_2329_);
v___x_2358_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId(v_e_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_);
if (lean_obj_tag(v___x_2358_) == 0)
{
lean_object* v___x_2359_; lean_object* v___x_2360_; 
lean_dec_ref(v___x_2358_);
v___x_2359_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_2360_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_2359_, v_e_2329_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_);
if (lean_obj_tag(v___x_2360_) == 0)
{
lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2367_; 
v_isSharedCheck_2367_ = !lean_is_exclusive(v___x_2360_);
if (v_isSharedCheck_2367_ == 0)
{
lean_object* v_unused_2368_; 
v_unused_2368_ = lean_ctor_get(v___x_2360_, 0);
lean_dec(v_unused_2368_);
v___x_2362_ = v___x_2360_;
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
else
{
lean_dec(v___x_2360_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
lean_object* v___x_2365_; 
if (v_isShared_2363_ == 0)
{
lean_ctor_set(v___x_2362_, 0, v_size_2355_);
v___x_2365_ = v___x_2362_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v_size_2355_);
v___x_2365_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
return v___x_2365_;
}
}
}
else
{
lean_object* v_a_2369_; lean_object* v___x_2371_; uint8_t v_isShared_2372_; uint8_t v_isSharedCheck_2376_; 
lean_dec(v_size_2355_);
v_a_2369_ = lean_ctor_get(v___x_2360_, 0);
v_isSharedCheck_2376_ = !lean_is_exclusive(v___x_2360_);
if (v_isSharedCheck_2376_ == 0)
{
v___x_2371_ = v___x_2360_;
v_isShared_2372_ = v_isSharedCheck_2376_;
goto v_resetjp_2370_;
}
else
{
lean_inc(v_a_2369_);
lean_dec(v___x_2360_);
v___x_2371_ = lean_box(0);
v_isShared_2372_ = v_isSharedCheck_2376_;
goto v_resetjp_2370_;
}
v_resetjp_2370_:
{
lean_object* v___x_2374_; 
if (v_isShared_2372_ == 0)
{
v___x_2374_ = v___x_2371_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v_a_2369_);
v___x_2374_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
return v___x_2374_;
}
}
}
}
else
{
lean_object* v_a_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2384_; 
lean_dec(v_size_2355_);
lean_dec(v___y_2340_);
lean_dec_ref(v___y_2339_);
lean_dec(v___y_2338_);
lean_dec_ref(v___y_2337_);
lean_dec(v___y_2336_);
lean_dec_ref(v___y_2335_);
lean_dec(v___y_2334_);
lean_dec_ref(v___y_2333_);
lean_dec(v___y_2332_);
lean_dec(v___y_2331_);
lean_dec_ref(v_e_2329_);
v_a_2377_ = lean_ctor_get(v___x_2358_, 0);
v_isSharedCheck_2384_ = !lean_is_exclusive(v___x_2358_);
if (v_isSharedCheck_2384_ == 0)
{
v___x_2379_ = v___x_2358_;
v_isShared_2380_ = v_isSharedCheck_2384_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_a_2377_);
lean_dec(v___x_2358_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2384_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
lean_object* v___x_2382_; 
if (v_isShared_2380_ == 0)
{
v___x_2382_ = v___x_2379_;
goto v_reusejp_2381_;
}
else
{
lean_object* v_reuseFailAlloc_2383_; 
v_reuseFailAlloc_2383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2383_, 0, v_a_2377_);
v___x_2382_ = v_reuseFailAlloc_2383_;
goto v_reusejp_2381_;
}
v_reusejp_2381_:
{
return v___x_2382_;
}
}
}
}
else
{
lean_object* v_a_2385_; lean_object* v___x_2387_; uint8_t v_isShared_2388_; uint8_t v_isSharedCheck_2392_; 
lean_dec(v_size_2355_);
lean_dec(v___y_2340_);
lean_dec_ref(v___y_2339_);
lean_dec(v___y_2338_);
lean_dec_ref(v___y_2337_);
lean_dec(v___y_2336_);
lean_dec_ref(v___y_2335_);
lean_dec(v___y_2334_);
lean_dec_ref(v___y_2333_);
lean_dec(v___y_2332_);
lean_dec(v___y_2331_);
lean_dec_ref(v___y_2330_);
lean_dec_ref(v_e_2329_);
v_a_2385_ = lean_ctor_get(v___x_2357_, 0);
v_isSharedCheck_2392_ = !lean_is_exclusive(v___x_2357_);
if (v_isSharedCheck_2392_ == 0)
{
v___x_2387_ = v___x_2357_;
v_isShared_2388_ = v_isSharedCheck_2392_;
goto v_resetjp_2386_;
}
else
{
lean_inc(v_a_2385_);
lean_dec(v___x_2357_);
v___x_2387_ = lean_box(0);
v_isShared_2388_ = v_isSharedCheck_2392_;
goto v_resetjp_2386_;
}
v_resetjp_2386_:
{
lean_object* v___x_2390_; 
if (v_isShared_2388_ == 0)
{
v___x_2390_ = v___x_2387_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2391_; 
v_reuseFailAlloc_2391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2391_, 0, v_a_2385_);
v___x_2390_ = v_reuseFailAlloc_2391_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
return v___x_2390_;
}
}
}
}
}
}
else
{
lean_object* v_a_2394_; lean_object* v___x_2396_; uint8_t v_isShared_2397_; uint8_t v_isSharedCheck_2401_; 
lean_dec(v___y_2340_);
lean_dec_ref(v___y_2339_);
lean_dec(v___y_2338_);
lean_dec_ref(v___y_2337_);
lean_dec(v___y_2336_);
lean_dec_ref(v___y_2335_);
lean_dec(v___y_2334_);
lean_dec_ref(v___y_2333_);
lean_dec(v___y_2332_);
lean_dec(v___y_2331_);
lean_dec_ref(v___y_2330_);
lean_dec_ref(v_e_2329_);
v_a_2394_ = lean_ctor_get(v___x_2342_, 0);
v_isSharedCheck_2401_ = !lean_is_exclusive(v___x_2342_);
if (v_isSharedCheck_2401_ == 0)
{
v___x_2396_ = v___x_2342_;
v_isShared_2397_ = v_isSharedCheck_2401_;
goto v_resetjp_2395_;
}
else
{
lean_inc(v_a_2394_);
lean_dec(v___x_2342_);
v___x_2396_ = lean_box(0);
v_isShared_2397_ = v_isSharedCheck_2401_;
goto v_resetjp_2395_;
}
v_resetjp_2395_:
{
lean_object* v___x_2399_; 
if (v_isShared_2397_ == 0)
{
v___x_2399_ = v___x_2396_;
goto v_reusejp_2398_;
}
else
{
lean_object* v_reuseFailAlloc_2400_; 
v_reuseFailAlloc_2400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2400_, 0, v_a_2394_);
v___x_2399_ = v_reuseFailAlloc_2400_;
goto v_reusejp_2398_;
}
v_reusejp_2398_:
{
return v___x_2399_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkVar_spec__0___boxed(lean_object* v_e_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_){
_start:
{
lean_object* v_res_2415_; 
v_res_2415_ = l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkVar_spec__0(v_e_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_);
return v_res_2415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVar(lean_object* v_e_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_){
_start:
{
lean_object* v___x_2429_; 
v___x_2429_ = l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkVar_spec__0(v_e_2416_, v_a_2417_, v_a_2418_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_, v_a_2427_);
return v___x_2429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVar___boxed(lean_object* v_e_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_){
_start:
{
lean_object* v_res_2443_; 
v_res_2443_ = l_Lean_Meta_Grind_Arith_CommRing_mkVar(v_e_2430_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_, v_a_2441_);
return v_res_2443_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_SynthInstance(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadRing(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadRing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM = _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_SynthInstance(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadRing(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadRing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(builtin);
}
#ifdef __cplusplus
}
#endif
