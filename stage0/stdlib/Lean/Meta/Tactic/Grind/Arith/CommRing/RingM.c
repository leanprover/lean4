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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_incSteps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_incSteps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg___lam__0(lean_object* v_n_65_, lean_object* v_s_66_){
_start:
{
lean_object* v_rings_67_; lean_object* v_typeIdOf_68_; lean_object* v_exprToRingId_69_; lean_object* v_semirings_70_; lean_object* v_stypeIdOf_71_; lean_object* v_exprToSemiringId_72_; lean_object* v_ncRings_73_; lean_object* v_exprToNCRingId_74_; lean_object* v_nctypeIdOf_75_; lean_object* v_ncSemirings_76_; lean_object* v_exprToNCSemiringId_77_; lean_object* v_ncstypeIdOf_78_; lean_object* v_steps_79_; lean_object* v___x_81_; uint8_t v_isShared_82_; uint8_t v_isSharedCheck_87_; 
v_rings_67_ = lean_ctor_get(v_s_66_, 0);
v_typeIdOf_68_ = lean_ctor_get(v_s_66_, 1);
v_exprToRingId_69_ = lean_ctor_get(v_s_66_, 2);
v_semirings_70_ = lean_ctor_get(v_s_66_, 3);
v_stypeIdOf_71_ = lean_ctor_get(v_s_66_, 4);
v_exprToSemiringId_72_ = lean_ctor_get(v_s_66_, 5);
v_ncRings_73_ = lean_ctor_get(v_s_66_, 6);
v_exprToNCRingId_74_ = lean_ctor_get(v_s_66_, 7);
v_nctypeIdOf_75_ = lean_ctor_get(v_s_66_, 8);
v_ncSemirings_76_ = lean_ctor_get(v_s_66_, 9);
v_exprToNCSemiringId_77_ = lean_ctor_get(v_s_66_, 10);
v_ncstypeIdOf_78_ = lean_ctor_get(v_s_66_, 11);
v_steps_79_ = lean_ctor_get(v_s_66_, 12);
v_isSharedCheck_87_ = !lean_is_exclusive(v_s_66_);
if (v_isSharedCheck_87_ == 0)
{
v___x_81_ = v_s_66_;
v_isShared_82_ = v_isSharedCheck_87_;
goto v_resetjp_80_;
}
else
{
lean_inc(v_steps_79_);
lean_inc(v_ncstypeIdOf_78_);
lean_inc(v_exprToNCSemiringId_77_);
lean_inc(v_ncSemirings_76_);
lean_inc(v_nctypeIdOf_75_);
lean_inc(v_exprToNCRingId_74_);
lean_inc(v_ncRings_73_);
lean_inc(v_exprToSemiringId_72_);
lean_inc(v_stypeIdOf_71_);
lean_inc(v_semirings_70_);
lean_inc(v_exprToRingId_69_);
lean_inc(v_typeIdOf_68_);
lean_inc(v_rings_67_);
lean_dec(v_s_66_);
v___x_81_ = lean_box(0);
v_isShared_82_ = v_isSharedCheck_87_;
goto v_resetjp_80_;
}
v_resetjp_80_:
{
lean_object* v___x_83_; lean_object* v___x_85_; 
v___x_83_ = lean_nat_add(v_steps_79_, v_n_65_);
lean_dec(v_steps_79_);
if (v_isShared_82_ == 0)
{
lean_ctor_set(v___x_81_, 12, v___x_83_);
v___x_85_ = v___x_81_;
goto v_reusejp_84_;
}
else
{
lean_object* v_reuseFailAlloc_86_; 
v_reuseFailAlloc_86_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_86_, 0, v_rings_67_);
lean_ctor_set(v_reuseFailAlloc_86_, 1, v_typeIdOf_68_);
lean_ctor_set(v_reuseFailAlloc_86_, 2, v_exprToRingId_69_);
lean_ctor_set(v_reuseFailAlloc_86_, 3, v_semirings_70_);
lean_ctor_set(v_reuseFailAlloc_86_, 4, v_stypeIdOf_71_);
lean_ctor_set(v_reuseFailAlloc_86_, 5, v_exprToSemiringId_72_);
lean_ctor_set(v_reuseFailAlloc_86_, 6, v_ncRings_73_);
lean_ctor_set(v_reuseFailAlloc_86_, 7, v_exprToNCRingId_74_);
lean_ctor_set(v_reuseFailAlloc_86_, 8, v_nctypeIdOf_75_);
lean_ctor_set(v_reuseFailAlloc_86_, 9, v_ncSemirings_76_);
lean_ctor_set(v_reuseFailAlloc_86_, 10, v_exprToNCSemiringId_77_);
lean_ctor_set(v_reuseFailAlloc_86_, 11, v_ncstypeIdOf_78_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg___lam__0___boxed(lean_object* v_n_88_, lean_object* v_s_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg___lam__0(v_n_88_, v_s_89_);
lean_dec(v_n_88_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg(lean_object* v_n_91_, lean_object* v_a_92_){
_start:
{
lean_object* v___f_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___f_94_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_94_, 0, v_n_91_);
v___x_95_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_96_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_95_, v___f_94_, v_a_92_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg___boxed(lean_object* v_n_97_, lean_object* v_a_98_, lean_object* v_a_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg(v_n_97_, v_a_98_);
lean_dec(v_a_98_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_incSteps(lean_object* v_n_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg(v_n_101_, v_a_102_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_incSteps___boxed(lean_object* v_n_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_Lean_Meta_Grind_Arith_CommRing_incSteps(v_n_114_, v_a_115_, v_a_116_, v_a_117_, v_a_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_, v_a_123_, v_a_124_);
lean_dec(v_a_124_);
lean_dec_ref(v_a_123_);
lean_dec(v_a_122_);
lean_dec_ref(v_a_121_);
lean_dec(v_a_120_);
lean_dec_ref(v_a_119_);
lean_dec(v_a_118_);
lean_dec_ref(v_a_117_);
lean_dec(v_a_116_);
lean_dec(v_a_115_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_run___redArg(lean_object* v_ringId_127_, lean_object* v_x_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_){
_start:
{
uint8_t v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_140_ = 0;
v___x_141_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_141_, 0, v_ringId_127_);
lean_ctor_set_uint8(v___x_141_, sizeof(void*)*1, v___x_140_);
v___x_142_ = lean_apply_12(v_x_128_, v___x_141_, v_a_129_, v_a_130_, v_a_131_, v_a_132_, v_a_133_, v_a_134_, v_a_135_, v_a_136_, v_a_137_, v_a_138_, lean_box(0));
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_run___redArg___boxed(lean_object* v_ringId_143_, lean_object* v_x_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_run___redArg(v_ringId_143_, v_x_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_, v_a_149_, v_a_150_, v_a_151_, v_a_152_, v_a_153_, v_a_154_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_run(lean_object* v_00_u03b1_157_, lean_object* v_ringId_158_, lean_object* v_x_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_){
_start:
{
uint8_t v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_171_ = 0;
v___x_172_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_172_, 0, v_ringId_158_);
lean_ctor_set_uint8(v___x_172_, sizeof(void*)*1, v___x_171_);
v___x_173_ = lean_apply_12(v_x_159_, v___x_172_, v_a_160_, v_a_161_, v_a_162_, v_a_163_, v_a_164_, v_a_165_, v_a_166_, v_a_167_, v_a_168_, v_a_169_, lean_box(0));
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_run___boxed(lean_object* v_00_u03b1_174_, lean_object* v_ringId_175_, lean_object* v_x_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_run(v_00_u03b1_174_, v_ringId_175_, v_x_176_, v_a_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_, v_a_182_, v_a_183_, v_a_184_, v_a_185_, v_a_186_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getRingId___redArg(lean_object* v_a_189_){
_start:
{
lean_object* v_ringId_191_; lean_object* v___x_192_; 
v_ringId_191_ = lean_ctor_get(v_a_189_, 0);
lean_inc(v_ringId_191_);
v___x_192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_192_, 0, v_ringId_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getRingId___redArg___boxed(lean_object* v_a_193_, lean_object* v_a_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_Lean_Meta_Grind_Arith_CommRing_getRingId___redArg(v_a_193_);
lean_dec_ref(v_a_193_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getRingId(lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_){
_start:
{
lean_object* v_ringId_208_; lean_object* v___x_209_; 
v_ringId_208_ = lean_ctor_get(v_a_196_, 0);
lean_inc(v_ringId_208_);
v___x_209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_209_, 0, v_ringId_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getRingId___boxed(lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_Lean_Meta_Grind_Arith_CommRing_getRingId(v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_, v_a_218_, v_a_219_, v_a_220_);
lean_dec(v_a_220_);
lean_dec_ref(v_a_219_);
lean_dec(v_a_218_);
lean_dec_ref(v_a_217_);
lean_dec(v_a_216_);
lean_dec_ref(v_a_215_);
lean_dec(v_a_214_);
lean_dec_ref(v_a_213_);
lean_dec(v_a_212_);
lean_dec(v_a_211_);
lean_dec_ref(v_a_210_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__0(lean_object* v_e_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_){
_start:
{
lean_object* v___x_236_; 
lean_inc(v___y_230_);
v___x_236_ = lean_grind_canon(v_e_223_, v___y_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_);
if (lean_obj_tag(v___x_236_) == 0)
{
lean_object* v_a_237_; lean_object* v___x_238_; 
v_a_237_ = lean_ctor_get(v___x_236_, 0);
lean_inc(v_a_237_);
lean_dec_ref(v___x_236_);
v___x_238_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_237_, v___y_230_);
lean_dec(v___y_230_);
return v___x_238_;
}
else
{
lean_dec(v___y_230_);
return v___x_236_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__0___boxed(lean_object* v_e_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__0(v_e_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_);
lean_dec_ref(v___y_240_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__1(lean_object* v_e_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_){
_start:
{
lean_object* v___x_266_; 
v___x_266_ = l_Lean_Meta_Grind_synthInstanceMeta_x3f(v_e_253_, v___y_261_, v___y_262_, v___y_263_, v___y_264_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__1___boxed(lean_object* v_e_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__1(v_e_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_);
lean_dec(v___y_274_);
lean_dec_ref(v___y_273_);
lean_dec(v___y_272_);
lean_dec_ref(v___y_271_);
lean_dec(v___y_270_);
lean_dec(v___y_269_);
lean_dec_ref(v___y_268_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0_spec__0(lean_object* v_msgData_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_){
_start:
{
lean_object* v___x_293_; lean_object* v_env_294_; lean_object* v___x_295_; lean_object* v_mctx_296_; lean_object* v_lctx_297_; lean_object* v_options_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_293_ = lean_st_ref_get(v___y_291_);
v_env_294_ = lean_ctor_get(v___x_293_, 0);
lean_inc_ref(v_env_294_);
lean_dec(v___x_293_);
v___x_295_ = lean_st_ref_get(v___y_289_);
v_mctx_296_ = lean_ctor_get(v___x_295_, 0);
lean_inc_ref(v_mctx_296_);
lean_dec(v___x_295_);
v_lctx_297_ = lean_ctor_get(v___y_288_, 2);
v_options_298_ = lean_ctor_get(v___y_290_, 2);
lean_inc_ref(v_options_298_);
lean_inc_ref(v_lctx_297_);
v___x_299_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_299_, 0, v_env_294_);
lean_ctor_set(v___x_299_, 1, v_mctx_296_);
lean_ctor_set(v___x_299_, 2, v_lctx_297_);
lean_ctor_set(v___x_299_, 3, v_options_298_);
v___x_300_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_300_, 0, v___x_299_);
lean_ctor_set(v___x_300_, 1, v_msgData_287_);
v___x_301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_301_, 0, v___x_300_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0_spec__0___boxed(lean_object* v_msgData_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0_spec__0(v_msgData_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_);
lean_dec(v___y_306_);
lean_dec_ref(v___y_305_);
lean_dec(v___y_304_);
lean_dec_ref(v___y_303_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg(lean_object* v_msg_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_){
_start:
{
lean_object* v_ref_315_; lean_object* v___x_316_; lean_object* v_a_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_325_; 
v_ref_315_ = lean_ctor_get(v___y_312_, 5);
v___x_316_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0_spec__0(v_msg_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_);
v_a_317_ = lean_ctor_get(v___x_316_, 0);
v_isSharedCheck_325_ = !lean_is_exclusive(v___x_316_);
if (v_isSharedCheck_325_ == 0)
{
v___x_319_ = v___x_316_;
v_isShared_320_ = v_isSharedCheck_325_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_a_317_);
lean_dec(v___x_316_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_325_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v___x_321_; lean_object* v___x_323_; 
lean_inc(v_ref_315_);
v___x_321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_321_, 0, v_ref_315_);
lean_ctor_set(v___x_321_, 1, v_a_317_);
if (v_isShared_320_ == 0)
{
lean_ctor_set_tag(v___x_319_, 1);
lean_ctor_set(v___x_319_, 0, v___x_321_);
v___x_323_ = v___x_319_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v___x_321_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
return v___x_323_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg___boxed(lean_object* v_msg_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg(v_msg_326_, v___y_327_, v___y_328_, v___y_329_, v___y_330_);
lean_dec(v___y_330_);
lean_dec_ref(v___y_329_);
lean_dec(v___y_328_);
lean_dec_ref(v___y_327_);
return v_res_332_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__1(void){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_334_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__0));
v___x_335_ = l_Lean_stringToMessageData(v___x_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_){
_start:
{
lean_object* v___x_348_; 
v___x_348_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_337_, v_a_345_);
if (lean_obj_tag(v___x_348_) == 0)
{
lean_object* v_a_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_363_; 
v_a_349_ = lean_ctor_get(v___x_348_, 0);
v_isSharedCheck_363_ = !lean_is_exclusive(v___x_348_);
if (v_isSharedCheck_363_ == 0)
{
v___x_351_ = v___x_348_;
v_isShared_352_ = v_isSharedCheck_363_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_a_349_);
lean_dec(v___x_348_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_363_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
lean_object* v_ringId_353_; lean_object* v_rings_354_; lean_object* v___x_355_; uint8_t v___x_356_; 
v_ringId_353_ = lean_ctor_get(v_a_336_, 0);
v_rings_354_ = lean_ctor_get(v_a_349_, 0);
lean_inc_ref(v_rings_354_);
lean_dec(v_a_349_);
v___x_355_ = lean_array_get_size(v_rings_354_);
v___x_356_ = lean_nat_dec_lt(v_ringId_353_, v___x_355_);
if (v___x_356_ == 0)
{
lean_object* v___x_357_; lean_object* v___x_358_; 
lean_dec_ref(v_rings_354_);
lean_del_object(v___x_351_);
v___x_357_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__1);
v___x_358_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg(v___x_357_, v_a_343_, v_a_344_, v_a_345_, v_a_346_);
return v___x_358_;
}
else
{
lean_object* v___x_359_; lean_object* v___x_361_; 
v___x_359_ = lean_array_fget(v_rings_354_, v_ringId_353_);
lean_dec_ref(v_rings_354_);
if (v_isShared_352_ == 0)
{
lean_ctor_set(v___x_351_, 0, v___x_359_);
v___x_361_ = v___x_351_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v___x_359_);
v___x_361_ = v_reuseFailAlloc_362_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
return v___x_361_;
}
}
}
}
else
{
lean_object* v_a_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_371_; 
v_a_364_ = lean_ctor_get(v___x_348_, 0);
v_isSharedCheck_371_ = !lean_is_exclusive(v___x_348_);
if (v_isSharedCheck_371_ == 0)
{
v___x_366_ = v___x_348_;
v_isShared_367_ = v_isSharedCheck_371_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_a_364_);
lean_dec(v___x_348_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_371_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v___x_369_; 
if (v_isShared_367_ == 0)
{
v___x_369_ = v___x_366_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v_a_364_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
return v___x_369_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___boxed(lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_372_, v_a_373_, v_a_374_, v_a_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_, v_a_380_, v_a_381_, v_a_382_);
lean_dec(v_a_382_);
lean_dec_ref(v_a_381_);
lean_dec(v_a_380_);
lean_dec_ref(v_a_379_);
lean_dec(v_a_378_);
lean_dec_ref(v_a_377_);
lean_dec(v_a_376_);
lean_dec_ref(v_a_375_);
lean_dec(v_a_374_);
lean_dec(v_a_373_);
lean_dec_ref(v_a_372_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0(lean_object* v_00_u03b1_385_, lean_object* v_msg_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_){
_start:
{
lean_object* v___x_399_; 
v___x_399_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg(v_msg_386_, v___y_394_, v___y_395_, v___y_396_, v___y_397_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___boxed(lean_object* v_00_u03b1_400_, lean_object* v_msg_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0(v_00_u03b1_400_, v_msg_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_, v___y_412_);
lean_dec(v___y_412_);
lean_dec_ref(v___y_411_);
lean_dec(v___y_410_);
lean_dec_ref(v___y_409_);
lean_dec(v___y_408_);
lean_dec_ref(v___y_407_);
lean_dec(v___y_406_);
lean_dec_ref(v___y_405_);
lean_dec(v___y_404_);
lean_dec(v___y_403_);
lean_dec_ref(v___y_402_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg___lam__0(lean_object* v_ringId_415_, lean_object* v_f_416_, lean_object* v_s_417_){
_start:
{
lean_object* v_rings_418_; lean_object* v_typeIdOf_419_; lean_object* v_exprToRingId_420_; lean_object* v_semirings_421_; lean_object* v_stypeIdOf_422_; lean_object* v_exprToSemiringId_423_; lean_object* v_ncRings_424_; lean_object* v_exprToNCRingId_425_; lean_object* v_nctypeIdOf_426_; lean_object* v_ncSemirings_427_; lean_object* v_exprToNCSemiringId_428_; lean_object* v_ncstypeIdOf_429_; lean_object* v_steps_430_; lean_object* v___x_431_; uint8_t v___x_432_; 
v_rings_418_ = lean_ctor_get(v_s_417_, 0);
v_typeIdOf_419_ = lean_ctor_get(v_s_417_, 1);
v_exprToRingId_420_ = lean_ctor_get(v_s_417_, 2);
v_semirings_421_ = lean_ctor_get(v_s_417_, 3);
v_stypeIdOf_422_ = lean_ctor_get(v_s_417_, 4);
v_exprToSemiringId_423_ = lean_ctor_get(v_s_417_, 5);
v_ncRings_424_ = lean_ctor_get(v_s_417_, 6);
v_exprToNCRingId_425_ = lean_ctor_get(v_s_417_, 7);
v_nctypeIdOf_426_ = lean_ctor_get(v_s_417_, 8);
v_ncSemirings_427_ = lean_ctor_get(v_s_417_, 9);
v_exprToNCSemiringId_428_ = lean_ctor_get(v_s_417_, 10);
v_ncstypeIdOf_429_ = lean_ctor_get(v_s_417_, 11);
v_steps_430_ = lean_ctor_get(v_s_417_, 12);
v___x_431_ = lean_array_get_size(v_rings_418_);
v___x_432_ = lean_nat_dec_lt(v_ringId_415_, v___x_431_);
if (v___x_432_ == 0)
{
lean_dec_ref(v_f_416_);
return v_s_417_;
}
else
{
lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_444_; 
lean_inc(v_steps_430_);
lean_inc_ref(v_ncstypeIdOf_429_);
lean_inc_ref(v_exprToNCSemiringId_428_);
lean_inc_ref(v_ncSemirings_427_);
lean_inc_ref(v_nctypeIdOf_426_);
lean_inc_ref(v_exprToNCRingId_425_);
lean_inc_ref(v_ncRings_424_);
lean_inc_ref(v_exprToSemiringId_423_);
lean_inc_ref(v_stypeIdOf_422_);
lean_inc_ref(v_semirings_421_);
lean_inc_ref(v_exprToRingId_420_);
lean_inc_ref(v_typeIdOf_419_);
lean_inc_ref(v_rings_418_);
v_isSharedCheck_444_ = !lean_is_exclusive(v_s_417_);
if (v_isSharedCheck_444_ == 0)
{
lean_object* v_unused_445_; lean_object* v_unused_446_; lean_object* v_unused_447_; lean_object* v_unused_448_; lean_object* v_unused_449_; lean_object* v_unused_450_; lean_object* v_unused_451_; lean_object* v_unused_452_; lean_object* v_unused_453_; lean_object* v_unused_454_; lean_object* v_unused_455_; lean_object* v_unused_456_; lean_object* v_unused_457_; 
v_unused_445_ = lean_ctor_get(v_s_417_, 12);
lean_dec(v_unused_445_);
v_unused_446_ = lean_ctor_get(v_s_417_, 11);
lean_dec(v_unused_446_);
v_unused_447_ = lean_ctor_get(v_s_417_, 10);
lean_dec(v_unused_447_);
v_unused_448_ = lean_ctor_get(v_s_417_, 9);
lean_dec(v_unused_448_);
v_unused_449_ = lean_ctor_get(v_s_417_, 8);
lean_dec(v_unused_449_);
v_unused_450_ = lean_ctor_get(v_s_417_, 7);
lean_dec(v_unused_450_);
v_unused_451_ = lean_ctor_get(v_s_417_, 6);
lean_dec(v_unused_451_);
v_unused_452_ = lean_ctor_get(v_s_417_, 5);
lean_dec(v_unused_452_);
v_unused_453_ = lean_ctor_get(v_s_417_, 4);
lean_dec(v_unused_453_);
v_unused_454_ = lean_ctor_get(v_s_417_, 3);
lean_dec(v_unused_454_);
v_unused_455_ = lean_ctor_get(v_s_417_, 2);
lean_dec(v_unused_455_);
v_unused_456_ = lean_ctor_get(v_s_417_, 1);
lean_dec(v_unused_456_);
v_unused_457_ = lean_ctor_get(v_s_417_, 0);
lean_dec(v_unused_457_);
v___x_434_ = v_s_417_;
v_isShared_435_ = v_isSharedCheck_444_;
goto v_resetjp_433_;
}
else
{
lean_dec(v_s_417_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_444_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v_v_436_; lean_object* v___x_437_; lean_object* v_xs_x27_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_442_; 
v_v_436_ = lean_array_fget(v_rings_418_, v_ringId_415_);
v___x_437_ = lean_box(0);
v_xs_x27_438_ = lean_array_fset(v_rings_418_, v_ringId_415_, v___x_437_);
v___x_439_ = lean_apply_1(v_f_416_, v_v_436_);
v___x_440_ = lean_array_fset(v_xs_x27_438_, v_ringId_415_, v___x_439_);
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 0, v___x_440_);
v___x_442_ = v___x_434_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v___x_440_);
lean_ctor_set(v_reuseFailAlloc_443_, 1, v_typeIdOf_419_);
lean_ctor_set(v_reuseFailAlloc_443_, 2, v_exprToRingId_420_);
lean_ctor_set(v_reuseFailAlloc_443_, 3, v_semirings_421_);
lean_ctor_set(v_reuseFailAlloc_443_, 4, v_stypeIdOf_422_);
lean_ctor_set(v_reuseFailAlloc_443_, 5, v_exprToSemiringId_423_);
lean_ctor_set(v_reuseFailAlloc_443_, 6, v_ncRings_424_);
lean_ctor_set(v_reuseFailAlloc_443_, 7, v_exprToNCRingId_425_);
lean_ctor_set(v_reuseFailAlloc_443_, 8, v_nctypeIdOf_426_);
lean_ctor_set(v_reuseFailAlloc_443_, 9, v_ncSemirings_427_);
lean_ctor_set(v_reuseFailAlloc_443_, 10, v_exprToNCSemiringId_428_);
lean_ctor_set(v_reuseFailAlloc_443_, 11, v_ncstypeIdOf_429_);
lean_ctor_set(v_reuseFailAlloc_443_, 12, v_steps_430_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg___lam__0___boxed(lean_object* v_ringId_458_, lean_object* v_f_459_, lean_object* v_s_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg___lam__0(v_ringId_458_, v_f_459_, v_s_460_);
lean_dec(v_ringId_458_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(lean_object* v_f_462_, lean_object* v_a_463_, lean_object* v_a_464_){
_start:
{
lean_object* v_ringId_466_; lean_object* v___f_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v_ringId_466_ = lean_ctor_get(v_a_463_, 0);
lean_inc(v_ringId_466_);
lean_dec_ref(v_a_463_);
v___f_467_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_467_, 0, v_ringId_466_);
lean_closure_set(v___f_467_, 1, v_f_462_);
v___x_468_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_469_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_468_, v___f_467_, v_a_464_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg___boxed(lean_object* v_f_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v_f_470_, v_a_471_, v_a_472_);
lean_dec(v_a_472_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing(lean_object* v_f_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_){
_start:
{
lean_object* v___x_488_; 
v___x_488_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v_f_475_, v_a_476_, v_a_477_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___boxed(lean_object* v_f_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing(v_f_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_, v_a_494_, v_a_495_, v_a_496_, v_a_497_, v_a_498_, v_a_499_, v_a_500_);
lean_dec(v_a_500_);
lean_dec_ref(v_a_499_);
lean_dec(v_a_498_);
lean_dec_ref(v_a_497_);
lean_dec(v_a_496_);
lean_dec_ref(v_a_495_);
lean_dec(v_a_494_);
lean_dec_ref(v_a_493_);
lean_dec(v_a_492_);
lean_dec(v_a_491_);
return v_res_502_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__1(void){
_start:
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_504_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__0));
v___x_505_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___boxed), 12, 0);
v___x_506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_506_, 0, v___x_505_);
lean_ctor_set(v___x_506_, 1, v___x_504_);
return v___x_506_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM(void){
_start:
{
lean_object* v___x_507_; 
v___x_507_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__1);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd___redArg(lean_object* v_x_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_){
_start:
{
lean_object* v_ringId_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_530_; 
v_ringId_521_ = lean_ctor_get(v_a_509_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v_a_509_);
if (v_isSharedCheck_530_ == 0)
{
v___x_523_ = v_a_509_;
v_isShared_524_ = v_isSharedCheck_530_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_ringId_521_);
lean_dec(v_a_509_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_530_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
uint8_t v___x_525_; lean_object* v___x_527_; 
v___x_525_ = 1;
if (v_isShared_524_ == 0)
{
v___x_527_ = v___x_523_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_ringId_521_);
v___x_527_ = v_reuseFailAlloc_529_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
lean_object* v___x_528_; 
lean_ctor_set_uint8(v___x_527_, sizeof(void*)*1, v___x_525_);
v___x_528_ = lean_apply_12(v_x_508_, v___x_527_, v_a_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_, v_a_517_, v_a_518_, v_a_519_, lean_box(0));
return v___x_528_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd___redArg___boxed(lean_object* v_x_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd___redArg(v_x_531_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_, v_a_540_, v_a_541_, v_a_542_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd(lean_object* v_00_u03b1_545_, lean_object* v_x_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_){
_start:
{
lean_object* v_ringId_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_568_; 
v_ringId_559_ = lean_ctor_get(v_a_547_, 0);
v_isSharedCheck_568_ = !lean_is_exclusive(v_a_547_);
if (v_isSharedCheck_568_ == 0)
{
v___x_561_ = v_a_547_;
v_isShared_562_ = v_isSharedCheck_568_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_ringId_559_);
lean_dec(v_a_547_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_568_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
uint8_t v___x_563_; lean_object* v___x_565_; 
v___x_563_ = 1;
if (v_isShared_562_ == 0)
{
v___x_565_ = v___x_561_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v_ringId_559_);
v___x_565_ = v_reuseFailAlloc_567_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
lean_object* v___x_566_; 
lean_ctor_set_uint8(v___x_565_, sizeof(void*)*1, v___x_563_);
v___x_566_ = lean_apply_12(v_x_546_, v___x_565_, v_a_548_, v_a_549_, v_a_550_, v_a_551_, v_a_552_, v_a_553_, v_a_554_, v_a_555_, v_a_556_, v_a_557_, lean_box(0));
return v___x_566_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd___boxed(lean_object* v_00_u03b1_569_, lean_object* v_x_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd(v_00_u03b1_569_, v_x_570_, v_a_571_, v_a_572_, v_a_573_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___redArg(lean_object* v_a_584_){
_start:
{
uint8_t v_checkCoeffDvd_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v_checkCoeffDvd_586_ = lean_ctor_get_uint8(v_a_584_, sizeof(void*)*1);
v___x_587_ = lean_box(v_checkCoeffDvd_586_);
v___x_588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_588_, 0, v___x_587_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___redArg___boxed(lean_object* v_a_589_, lean_object* v_a_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___redArg(v_a_589_);
lean_dec_ref(v_a_589_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd(lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_){
_start:
{
lean_object* v___x_604_; 
v___x_604_ = l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___redArg(v_a_592_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___boxed(lean_object* v_a_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd(v_a_605_, v_a_606_, v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_);
lean_dec(v_a_615_);
lean_dec_ref(v_a_614_);
lean_dec(v_a_613_);
lean_dec_ref(v_a_612_);
lean_dec(v_a_611_);
lean_dec_ref(v_a_610_);
lean_dec(v_a_609_);
lean_dec_ref(v_a_608_);
lean_dec(v_a_607_);
lean_dec(v_a_606_);
lean_dec_ref(v_a_605_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_618_, lean_object* v_vals_619_, lean_object* v_i_620_, lean_object* v_k_621_){
_start:
{
lean_object* v___x_622_; uint8_t v___x_623_; 
v___x_622_ = lean_array_get_size(v_keys_618_);
v___x_623_ = lean_nat_dec_lt(v_i_620_, v___x_622_);
if (v___x_623_ == 0)
{
lean_object* v___x_624_; 
lean_dec(v_i_620_);
v___x_624_ = lean_box(0);
return v___x_624_;
}
else
{
lean_object* v_k_x27_625_; uint8_t v___x_626_; 
v_k_x27_625_ = lean_array_fget_borrowed(v_keys_618_, v_i_620_);
v___x_626_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_621_, v_k_x27_625_);
if (v___x_626_ == 0)
{
lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_627_ = lean_unsigned_to_nat(1u);
v___x_628_ = lean_nat_add(v_i_620_, v___x_627_);
lean_dec(v_i_620_);
v_i_620_ = v___x_628_;
goto _start;
}
else
{
lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_630_ = lean_array_fget_borrowed(v_vals_619_, v_i_620_);
lean_dec(v_i_620_);
lean_inc(v___x_630_);
v___x_631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_631_, 0, v___x_630_);
return v___x_631_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_632_, lean_object* v_vals_633_, lean_object* v_i_634_, lean_object* v_k_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_632_, v_vals_633_, v_i_634_, v_k_635_);
lean_dec_ref(v_k_635_);
lean_dec_ref(v_vals_633_);
lean_dec_ref(v_keys_632_);
return v_res_636_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_637_; size_t v___x_638_; size_t v___x_639_; 
v___x_637_ = ((size_t)5ULL);
v___x_638_ = ((size_t)1ULL);
v___x_639_ = lean_usize_shift_left(v___x_638_, v___x_637_);
return v___x_639_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_640_; size_t v___x_641_; size_t v___x_642_; 
v___x_640_ = ((size_t)1ULL);
v___x_641_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__0);
v___x_642_ = lean_usize_sub(v___x_641_, v___x_640_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg(lean_object* v_x_643_, size_t v_x_644_, lean_object* v_x_645_){
_start:
{
if (lean_obj_tag(v_x_643_) == 0)
{
lean_object* v_es_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_667_; 
v_es_646_ = lean_ctor_get(v_x_643_, 0);
v_isSharedCheck_667_ = !lean_is_exclusive(v_x_643_);
if (v_isSharedCheck_667_ == 0)
{
v___x_648_ = v_x_643_;
v_isShared_649_ = v_isSharedCheck_667_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_es_646_);
lean_dec(v_x_643_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_667_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v___x_650_; size_t v___x_651_; size_t v___x_652_; size_t v___x_653_; lean_object* v_j_654_; lean_object* v___x_655_; 
v___x_650_ = lean_box(2);
v___x_651_ = ((size_t)5ULL);
v___x_652_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__1);
v___x_653_ = lean_usize_land(v_x_644_, v___x_652_);
v_j_654_ = lean_usize_to_nat(v___x_653_);
v___x_655_ = lean_array_get(v___x_650_, v_es_646_, v_j_654_);
lean_dec(v_j_654_);
lean_dec_ref(v_es_646_);
switch(lean_obj_tag(v___x_655_))
{
case 0:
{
lean_object* v_key_656_; lean_object* v_val_657_; uint8_t v___x_658_; 
v_key_656_ = lean_ctor_get(v___x_655_, 0);
lean_inc(v_key_656_);
v_val_657_ = lean_ctor_get(v___x_655_, 1);
lean_inc(v_val_657_);
lean_dec_ref(v___x_655_);
v___x_658_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_645_, v_key_656_);
lean_dec(v_key_656_);
if (v___x_658_ == 0)
{
lean_object* v___x_659_; 
lean_dec(v_val_657_);
lean_del_object(v___x_648_);
v___x_659_ = lean_box(0);
return v___x_659_;
}
else
{
lean_object* v___x_661_; 
if (v_isShared_649_ == 0)
{
lean_ctor_set_tag(v___x_648_, 1);
lean_ctor_set(v___x_648_, 0, v_val_657_);
v___x_661_ = v___x_648_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v_val_657_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
}
case 1:
{
lean_object* v_node_663_; size_t v___x_664_; 
lean_del_object(v___x_648_);
v_node_663_ = lean_ctor_get(v___x_655_, 0);
lean_inc(v_node_663_);
lean_dec_ref(v___x_655_);
v___x_664_ = lean_usize_shift_right(v_x_644_, v___x_651_);
v_x_643_ = v_node_663_;
v_x_644_ = v___x_664_;
goto _start;
}
default: 
{
lean_object* v___x_666_; 
lean_del_object(v___x_648_);
v___x_666_ = lean_box(0);
return v___x_666_;
}
}
}
}
else
{
lean_object* v_ks_668_; lean_object* v_vs_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v_ks_668_ = lean_ctor_get(v_x_643_, 0);
lean_inc_ref(v_ks_668_);
v_vs_669_ = lean_ctor_get(v_x_643_, 1);
lean_inc_ref(v_vs_669_);
lean_dec_ref(v_x_643_);
v___x_670_ = lean_unsigned_to_nat(0u);
v___x_671_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_668_, v_vs_669_, v___x_670_, v_x_645_);
lean_dec_ref(v_vs_669_);
lean_dec_ref(v_ks_668_);
return v___x_671_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_672_, lean_object* v_x_673_, lean_object* v_x_674_){
_start:
{
size_t v_x_960__boxed_675_; lean_object* v_res_676_; 
v_x_960__boxed_675_ = lean_unbox_usize(v_x_673_);
lean_dec(v_x_673_);
v_res_676_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg(v_x_672_, v_x_960__boxed_675_, v_x_674_);
lean_dec_ref(v_x_674_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(lean_object* v_x_677_, lean_object* v_x_678_){
_start:
{
uint64_t v___x_679_; size_t v___x_680_; lean_object* v___x_681_; 
v___x_679_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_678_);
v___x_680_ = lean_uint64_to_usize(v___x_679_);
v___x_681_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg(v_x_677_, v___x_680_, v_x_678_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg___boxed(lean_object* v_x_682_, lean_object* v_x_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(v_x_682_, v_x_683_);
lean_dec_ref(v_x_683_);
return v_res_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg(lean_object* v_e_685_, lean_object* v_a_686_, lean_object* v_a_687_){
_start:
{
lean_object* v___x_689_; 
v___x_689_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_686_, v_a_687_);
if (lean_obj_tag(v___x_689_) == 0)
{
lean_object* v_a_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_699_; 
v_a_690_ = lean_ctor_get(v___x_689_, 0);
v_isSharedCheck_699_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_699_ == 0)
{
v___x_692_ = v___x_689_;
v_isShared_693_ = v_isSharedCheck_699_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_a_690_);
lean_dec(v___x_689_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_699_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v_exprToRingId_694_; lean_object* v___x_695_; lean_object* v___x_697_; 
v_exprToRingId_694_ = lean_ctor_get(v_a_690_, 2);
lean_inc_ref(v_exprToRingId_694_);
lean_dec(v_a_690_);
v___x_695_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(v_exprToRingId_694_, v_e_685_);
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 0, v___x_695_);
v___x_697_ = v___x_692_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v___x_695_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
}
else
{
lean_object* v_a_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_707_; 
v_a_700_ = lean_ctor_get(v___x_689_, 0);
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_707_ == 0)
{
v___x_702_ = v___x_689_;
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_a_700_);
lean_dec(v___x_689_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_705_; 
if (v_isShared_703_ == 0)
{
v___x_705_ = v___x_702_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_a_700_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg___boxed(lean_object* v_e_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_){
_start:
{
lean_object* v_res_712_; 
v_res_712_ = l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg(v_e_708_, v_a_709_, v_a_710_);
lean_dec_ref(v_a_710_);
lean_dec(v_a_709_);
lean_dec_ref(v_e_708_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f(lean_object* v_e_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_){
_start:
{
lean_object* v___x_725_; 
v___x_725_ = l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg(v_e_713_, v_a_714_, v_a_722_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___boxed(lean_object* v_e_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f(v_e_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_);
lean_dec(v_a_736_);
lean_dec_ref(v_a_735_);
lean_dec(v_a_734_);
lean_dec_ref(v_a_733_);
lean_dec(v_a_732_);
lean_dec_ref(v_a_731_);
lean_dec(v_a_730_);
lean_dec_ref(v_a_729_);
lean_dec(v_a_728_);
lean_dec(v_a_727_);
lean_dec_ref(v_e_726_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0(lean_object* v_00_u03b2_739_, lean_object* v_x_740_, lean_object* v_x_741_){
_start:
{
lean_object* v___x_742_; 
v___x_742_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(v_x_740_, v_x_741_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___boxed(lean_object* v_00_u03b2_743_, lean_object* v_x_744_, lean_object* v_x_745_){
_start:
{
lean_object* v_res_746_; 
v_res_746_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0(v_00_u03b2_743_, v_x_744_, v_x_745_);
lean_dec_ref(v_x_745_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_747_, lean_object* v_x_748_, size_t v_x_749_, lean_object* v_x_750_){
_start:
{
lean_object* v___x_751_; 
v___x_751_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg(v_x_748_, v_x_749_, v_x_750_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_752_, lean_object* v_x_753_, lean_object* v_x_754_, lean_object* v_x_755_){
_start:
{
size_t v_x_1125__boxed_756_; lean_object* v_res_757_; 
v_x_1125__boxed_756_ = lean_unbox_usize(v_x_754_);
lean_dec(v_x_754_);
v_res_757_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0(v_00_u03b2_752_, v_x_753_, v_x_1125__boxed_756_, v_x_755_);
lean_dec_ref(v_x_755_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_758_, lean_object* v_keys_759_, lean_object* v_vals_760_, lean_object* v_heq_761_, lean_object* v_i_762_, lean_object* v_k_763_){
_start:
{
lean_object* v___x_764_; 
v___x_764_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_759_, v_vals_760_, v_i_762_, v_k_763_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_765_, lean_object* v_keys_766_, lean_object* v_vals_767_, lean_object* v_heq_768_, lean_object* v_i_769_, lean_object* v_k_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_765_, v_keys_766_, v_vals_767_, v_heq_768_, v_i_769_, v_k_770_);
lean_dec_ref(v_k_770_);
lean_dec_ref(v_vals_767_);
lean_dec_ref(v_keys_766_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg___lam__0(lean_object* v_toPure_772_, lean_object* v_____do__lift_773_){
_start:
{
lean_object* v_charInst_x3f_777_; 
v_charInst_x3f_777_ = lean_ctor_get(v_____do__lift_773_, 5);
lean_inc(v_charInst_x3f_777_);
lean_dec_ref(v_____do__lift_773_);
if (lean_obj_tag(v_charInst_x3f_777_) == 1)
{
lean_object* v_val_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_789_; 
v_val_778_ = lean_ctor_get(v_charInst_x3f_777_, 0);
v_isSharedCheck_789_ = !lean_is_exclusive(v_charInst_x3f_777_);
if (v_isSharedCheck_789_ == 0)
{
v___x_780_ = v_charInst_x3f_777_;
v_isShared_781_ = v_isSharedCheck_789_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_val_778_);
lean_dec(v_charInst_x3f_777_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_789_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v_snd_782_; lean_object* v___x_783_; uint8_t v___x_784_; 
v_snd_782_ = lean_ctor_get(v_val_778_, 1);
lean_inc(v_snd_782_);
lean_dec(v_val_778_);
v___x_783_ = lean_unsigned_to_nat(0u);
v___x_784_ = lean_nat_dec_eq(v_snd_782_, v___x_783_);
if (v___x_784_ == 0)
{
lean_object* v___x_786_; 
if (v_isShared_781_ == 0)
{
lean_ctor_set(v___x_780_, 0, v_snd_782_);
v___x_786_ = v___x_780_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v_snd_782_);
v___x_786_ = v_reuseFailAlloc_788_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
lean_object* v___x_787_; 
v___x_787_ = lean_apply_2(v_toPure_772_, lean_box(0), v___x_786_);
return v___x_787_;
}
}
else
{
lean_dec(v_snd_782_);
lean_del_object(v___x_780_);
goto v___jp_774_;
}
}
}
else
{
lean_dec(v_charInst_x3f_777_);
goto v___jp_774_;
}
v___jp_774_:
{
lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_775_ = lean_box(0);
v___x_776_ = lean_apply_2(v_toPure_772_, lean_box(0), v___x_775_);
return v___x_776_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg(lean_object* v_inst_790_, lean_object* v_inst_791_){
_start:
{
lean_object* v_toApplicative_792_; lean_object* v_toBind_793_; lean_object* v_getRing_794_; lean_object* v_toPure_795_; lean_object* v___f_796_; lean_object* v___x_797_; 
v_toApplicative_792_ = lean_ctor_get(v_inst_790_, 0);
lean_inc_ref(v_toApplicative_792_);
v_toBind_793_ = lean_ctor_get(v_inst_790_, 1);
lean_inc(v_toBind_793_);
lean_dec_ref(v_inst_790_);
v_getRing_794_ = lean_ctor_get(v_inst_791_, 0);
lean_inc(v_getRing_794_);
lean_dec_ref(v_inst_791_);
v_toPure_795_ = lean_ctor_get(v_toApplicative_792_, 1);
lean_inc(v_toPure_795_);
lean_dec_ref(v_toApplicative_792_);
v___f_796_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_796_, 0, v_toPure_795_);
v___x_797_ = lean_apply_4(v_toBind_793_, lean_box(0), lean_box(0), v_getRing_794_, v___f_796_);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f(lean_object* v_m_798_, lean_object* v_inst_799_, lean_object* v_inst_800_){
_start:
{
lean_object* v___x_801_; 
v___x_801_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg(v_inst_799_, v_inst_800_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f___redArg___lam__0(lean_object* v_toPure_802_, lean_object* v_____do__lift_803_){
_start:
{
lean_object* v_charInst_x3f_807_; 
v_charInst_x3f_807_ = lean_ctor_get(v_____do__lift_803_, 5);
lean_inc(v_charInst_x3f_807_);
lean_dec_ref(v_____do__lift_803_);
if (lean_obj_tag(v_charInst_x3f_807_) == 1)
{
lean_object* v_val_808_; lean_object* v_snd_809_; lean_object* v___x_810_; uint8_t v___x_811_; 
v_val_808_ = lean_ctor_get(v_charInst_x3f_807_, 0);
v_snd_809_ = lean_ctor_get(v_val_808_, 1);
v___x_810_ = lean_unsigned_to_nat(0u);
v___x_811_ = lean_nat_dec_eq(v_snd_809_, v___x_810_);
if (v___x_811_ == 0)
{
lean_object* v___x_812_; 
v___x_812_ = lean_apply_2(v_toPure_802_, lean_box(0), v_charInst_x3f_807_);
return v___x_812_;
}
else
{
lean_dec_ref(v_charInst_x3f_807_);
goto v___jp_804_;
}
}
else
{
lean_dec(v_charInst_x3f_807_);
goto v___jp_804_;
}
v___jp_804_:
{
lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_805_ = lean_box(0);
v___x_806_ = lean_apply_2(v_toPure_802_, lean_box(0), v___x_805_);
return v___x_806_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f___redArg(lean_object* v_inst_813_, lean_object* v_inst_814_){
_start:
{
lean_object* v_toApplicative_815_; lean_object* v_toBind_816_; lean_object* v_getRing_817_; lean_object* v_toPure_818_; lean_object* v___f_819_; lean_object* v___x_820_; 
v_toApplicative_815_ = lean_ctor_get(v_inst_813_, 0);
lean_inc_ref(v_toApplicative_815_);
v_toBind_816_ = lean_ctor_get(v_inst_813_, 1);
lean_inc(v_toBind_816_);
lean_dec_ref(v_inst_813_);
v_getRing_817_ = lean_ctor_get(v_inst_814_, 0);
lean_inc(v_getRing_817_);
lean_dec_ref(v_inst_814_);
v_toPure_818_ = lean_ctor_get(v_toApplicative_815_, 1);
lean_inc(v_toPure_818_);
lean_dec_ref(v_toApplicative_815_);
v___f_819_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_819_, 0, v_toPure_818_);
v___x_820_ = lean_apply_4(v_toBind_816_, lean_box(0), lean_box(0), v_getRing_817_, v___f_819_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f(lean_object* v_m_821_, lean_object* v_inst_822_, lean_object* v_inst_823_){
_start:
{
lean_object* v___x_824_; 
v___x_824_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f___redArg(v_inst_822_, v_inst_823_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisorsInst_x3f(lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_){
_start:
{
lean_object* v___x_837_; 
v___x_837_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_825_, v_a_826_, v_a_827_, v_a_828_, v_a_829_, v_a_830_, v_a_831_, v_a_832_, v_a_833_, v_a_834_, v_a_835_);
if (lean_obj_tag(v___x_837_) == 0)
{
lean_object* v_a_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_846_; 
v_a_838_ = lean_ctor_get(v___x_837_, 0);
v_isSharedCheck_846_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_846_ == 0)
{
v___x_840_ = v___x_837_;
v_isShared_841_ = v_isSharedCheck_846_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_a_838_);
lean_dec(v___x_837_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_846_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v_noZeroDivInst_x3f_842_; lean_object* v___x_844_; 
v_noZeroDivInst_x3f_842_ = lean_ctor_get(v_a_838_, 5);
lean_inc(v_noZeroDivInst_x3f_842_);
lean_dec(v_a_838_);
if (v_isShared_841_ == 0)
{
lean_ctor_set(v___x_840_, 0, v_noZeroDivInst_x3f_842_);
v___x_844_ = v___x_840_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v_noZeroDivInst_x3f_842_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
}
else
{
lean_object* v_a_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_854_; 
v_a_847_ = lean_ctor_get(v___x_837_, 0);
v_isSharedCheck_854_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_854_ == 0)
{
v___x_849_ = v___x_837_;
v_isShared_850_ = v_isSharedCheck_854_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_a_847_);
lean_dec(v___x_837_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_854_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v___x_852_; 
if (v_isShared_850_ == 0)
{
v___x_852_ = v___x_849_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v_a_847_);
v___x_852_ = v_reuseFailAlloc_853_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
return v___x_852_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisorsInst_x3f___boxed(lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_){
_start:
{
lean_object* v_res_867_; 
v_res_867_ = l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisorsInst_x3f(v_a_855_, v_a_856_, v_a_857_, v_a_858_, v_a_859_, v_a_860_, v_a_861_, v_a_862_, v_a_863_, v_a_864_, v_a_865_);
lean_dec(v_a_865_);
lean_dec_ref(v_a_864_);
lean_dec(v_a_863_);
lean_dec_ref(v_a_862_);
lean_dec(v_a_861_);
lean_dec_ref(v_a_860_);
lean_dec(v_a_859_);
lean_dec_ref(v_a_858_);
lean_dec(v_a_857_);
lean_dec(v_a_856_);
lean_dec_ref(v_a_855_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisors(lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_){
_start:
{
lean_object* v___x_880_; 
v___x_880_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_);
if (lean_obj_tag(v___x_880_) == 0)
{
lean_object* v_a_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_896_; 
v_a_881_ = lean_ctor_get(v___x_880_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_896_ == 0)
{
v___x_883_ = v___x_880_;
v_isShared_884_ = v_isSharedCheck_896_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_a_881_);
lean_dec(v___x_880_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_896_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v_noZeroDivInst_x3f_885_; 
v_noZeroDivInst_x3f_885_ = lean_ctor_get(v_a_881_, 5);
lean_inc(v_noZeroDivInst_x3f_885_);
lean_dec(v_a_881_);
if (lean_obj_tag(v_noZeroDivInst_x3f_885_) == 0)
{
uint8_t v___x_886_; lean_object* v___x_887_; lean_object* v___x_889_; 
v___x_886_ = 0;
v___x_887_ = lean_box(v___x_886_);
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 0, v___x_887_);
v___x_889_ = v___x_883_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v___x_887_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
else
{
uint8_t v___x_891_; lean_object* v___x_892_; lean_object* v___x_894_; 
lean_dec_ref(v_noZeroDivInst_x3f_885_);
v___x_891_ = 1;
v___x_892_ = lean_box(v___x_891_);
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 0, v___x_892_);
v___x_894_ = v___x_883_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v___x_892_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
}
}
else
{
lean_object* v_a_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_904_; 
v_a_897_ = lean_ctor_get(v___x_880_, 0);
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_904_ == 0)
{
v___x_899_ = v___x_880_;
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_a_897_);
lean_dec(v___x_880_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_902_; 
if (v_isShared_900_ == 0)
{
v___x_902_ = v___x_899_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_a_897_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisors___boxed(lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_){
_start:
{
lean_object* v_res_917_; 
v_res_917_ = l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisors(v_a_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_);
lean_dec(v_a_915_);
lean_dec_ref(v_a_914_);
lean_dec(v_a_913_);
lean_dec_ref(v_a_912_);
lean_dec(v_a_911_);
lean_dec_ref(v_a_910_);
lean_dec(v_a_909_);
lean_dec_ref(v_a_908_);
lean_dec(v_a_907_);
lean_dec(v_a_906_);
lean_dec_ref(v_a_905_);
return v_res_917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_hasChar(lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_){
_start:
{
lean_object* v___x_930_; 
v___x_930_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_918_, v_a_919_, v_a_920_, v_a_921_, v_a_922_, v_a_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_);
if (lean_obj_tag(v___x_930_) == 0)
{
lean_object* v_a_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_947_; 
v_a_931_ = lean_ctor_get(v___x_930_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_947_ == 0)
{
v___x_933_ = v___x_930_;
v_isShared_934_ = v_isSharedCheck_947_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_a_931_);
lean_dec(v___x_930_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_947_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v_toRing_935_; lean_object* v_charInst_x3f_936_; 
v_toRing_935_ = lean_ctor_get(v_a_931_, 0);
lean_inc_ref(v_toRing_935_);
lean_dec(v_a_931_);
v_charInst_x3f_936_ = lean_ctor_get(v_toRing_935_, 5);
lean_inc(v_charInst_x3f_936_);
lean_dec_ref(v_toRing_935_);
if (lean_obj_tag(v_charInst_x3f_936_) == 0)
{
uint8_t v___x_937_; lean_object* v___x_938_; lean_object* v___x_940_; 
v___x_937_ = 0;
v___x_938_ = lean_box(v___x_937_);
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 0, v___x_938_);
v___x_940_ = v___x_933_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v___x_938_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
return v___x_940_;
}
}
else
{
uint8_t v___x_942_; lean_object* v___x_943_; lean_object* v___x_945_; 
lean_dec_ref(v_charInst_x3f_936_);
v___x_942_ = 1;
v___x_943_ = lean_box(v___x_942_);
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 0, v___x_943_);
v___x_945_ = v___x_933_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v___x_943_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
}
else
{
lean_object* v_a_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_955_; 
v_a_948_ = lean_ctor_get(v___x_930_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_955_ == 0)
{
v___x_950_ = v___x_930_;
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_a_948_);
lean_dec(v___x_930_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_955_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_953_; 
if (v_isShared_951_ == 0)
{
v___x_953_ = v___x_950_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_a_948_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_hasChar___boxed(lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l_Lean_Meta_Grind_Arith_CommRing_hasChar(v_a_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_, v_a_966_);
lean_dec(v_a_966_);
lean_dec_ref(v_a_965_);
lean_dec(v_a_964_);
lean_dec_ref(v_a_963_);
lean_dec(v_a_962_);
lean_dec_ref(v_a_961_);
lean_dec(v_a_960_);
lean_dec_ref(v_a_959_);
lean_dec(v_a_958_);
lean_dec(v_a_957_);
lean_dec_ref(v_a_956_);
return v_res_968_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__1(void){
_start:
{
lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_970_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__0));
v___x_971_ = l_Lean_stringToMessageData(v___x_970_);
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCharInst(lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_){
_start:
{
lean_object* v___x_984_; 
v___x_984_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_972_, v_a_973_, v_a_974_, v_a_975_, v_a_976_, v_a_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_);
if (lean_obj_tag(v___x_984_) == 0)
{
lean_object* v_a_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_997_; 
v_a_985_ = lean_ctor_get(v___x_984_, 0);
v_isSharedCheck_997_ = !lean_is_exclusive(v___x_984_);
if (v_isSharedCheck_997_ == 0)
{
v___x_987_ = v___x_984_;
v_isShared_988_ = v_isSharedCheck_997_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_a_985_);
lean_dec(v___x_984_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_997_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v_toRing_989_; lean_object* v_charInst_x3f_990_; 
v_toRing_989_ = lean_ctor_get(v_a_985_, 0);
lean_inc_ref(v_toRing_989_);
lean_dec(v_a_985_);
v_charInst_x3f_990_ = lean_ctor_get(v_toRing_989_, 5);
lean_inc(v_charInst_x3f_990_);
lean_dec_ref(v_toRing_989_);
if (lean_obj_tag(v_charInst_x3f_990_) == 1)
{
lean_object* v_val_991_; lean_object* v___x_993_; 
v_val_991_ = lean_ctor_get(v_charInst_x3f_990_, 0);
lean_inc(v_val_991_);
lean_dec_ref(v_charInst_x3f_990_);
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 0, v_val_991_);
v___x_993_ = v___x_987_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_val_991_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
else
{
lean_object* v___x_995_; lean_object* v___x_996_; 
lean_dec(v_charInst_x3f_990_);
lean_del_object(v___x_987_);
v___x_995_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__1);
v___x_996_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg(v___x_995_, v_a_979_, v_a_980_, v_a_981_, v_a_982_);
return v___x_996_;
}
}
}
else
{
lean_object* v_a_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1005_; 
v_a_998_ = lean_ctor_get(v___x_984_, 0);
v_isSharedCheck_1005_ = !lean_is_exclusive(v___x_984_);
if (v_isSharedCheck_1005_ == 0)
{
v___x_1000_ = v___x_984_;
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_a_998_);
lean_dec(v___x_984_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v___x_1003_; 
if (v_isShared_1001_ == 0)
{
v___x_1003_ = v___x_1000_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v_a_998_);
v___x_1003_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
return v___x_1003_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCharInst___boxed(lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_){
_start:
{
lean_object* v_res_1018_; 
v_res_1018_ = l_Lean_Meta_Grind_Arith_CommRing_getCharInst(v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_);
lean_dec(v_a_1016_);
lean_dec_ref(v_a_1015_);
lean_dec(v_a_1014_);
lean_dec_ref(v_a_1013_);
lean_dec(v_a_1012_);
lean_dec_ref(v_a_1011_);
lean_dec(v_a_1010_);
lean_dec_ref(v_a_1009_);
lean_dec(v_a_1008_);
lean_dec(v_a_1007_);
lean_dec_ref(v_a_1006_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isField(lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_){
_start:
{
lean_object* v___x_1031_; 
v___x_1031_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_);
if (lean_obj_tag(v___x_1031_) == 0)
{
lean_object* v_a_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1047_; 
v_a_1032_ = lean_ctor_get(v___x_1031_, 0);
v_isSharedCheck_1047_ = !lean_is_exclusive(v___x_1031_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1034_ = v___x_1031_;
v_isShared_1035_ = v_isSharedCheck_1047_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_a_1032_);
lean_dec(v___x_1031_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1047_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v_fieldInst_x3f_1036_; 
v_fieldInst_x3f_1036_ = lean_ctor_get(v_a_1032_, 6);
lean_inc(v_fieldInst_x3f_1036_);
lean_dec(v_a_1032_);
if (lean_obj_tag(v_fieldInst_x3f_1036_) == 0)
{
uint8_t v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1040_; 
v___x_1037_ = 0;
v___x_1038_ = lean_box(v___x_1037_);
if (v_isShared_1035_ == 0)
{
lean_ctor_set(v___x_1034_, 0, v___x_1038_);
v___x_1040_ = v___x_1034_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v___x_1038_);
v___x_1040_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
return v___x_1040_;
}
}
else
{
uint8_t v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1045_; 
lean_dec_ref(v_fieldInst_x3f_1036_);
v___x_1042_ = 1;
v___x_1043_ = lean_box(v___x_1042_);
if (v_isShared_1035_ == 0)
{
lean_ctor_set(v___x_1034_, 0, v___x_1043_);
v___x_1045_ = v___x_1034_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v___x_1043_);
v___x_1045_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
return v___x_1045_;
}
}
}
}
else
{
lean_object* v_a_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1055_; 
v_a_1048_ = lean_ctor_get(v___x_1031_, 0);
v_isSharedCheck_1055_ = !lean_is_exclusive(v___x_1031_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1050_ = v___x_1031_;
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_a_1048_);
lean_dec(v___x_1031_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v___x_1053_; 
if (v_isShared_1051_ == 0)
{
v___x_1053_ = v___x_1050_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v_a_1048_);
v___x_1053_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
return v___x_1053_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isField___boxed(lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_){
_start:
{
lean_object* v_res_1068_; 
v_res_1068_ = l_Lean_Meta_Grind_Arith_CommRing_isField(v_a_1056_, v_a_1057_, v_a_1058_, v_a_1059_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_);
lean_dec(v_a_1066_);
lean_dec_ref(v_a_1065_);
lean_dec(v_a_1064_);
lean_dec_ref(v_a_1063_);
lean_dec(v_a_1062_);
lean_dec_ref(v_a_1061_);
lean_dec(v_a_1060_);
lean_dec_ref(v_a_1059_);
lean_dec(v_a_1058_);
lean_dec(v_a_1057_);
lean_dec_ref(v_a_1056_);
return v_res_1068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty(lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_){
_start:
{
lean_object* v___x_1081_; 
v___x_1081_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_);
if (lean_obj_tag(v___x_1081_) == 0)
{
lean_object* v_a_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1097_; 
v_a_1082_ = lean_ctor_get(v___x_1081_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1081_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1084_ = v___x_1081_;
v_isShared_1085_ = v_isSharedCheck_1097_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_a_1082_);
lean_dec(v___x_1081_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1097_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
lean_object* v_queue_1086_; 
v_queue_1086_ = lean_ctor_get(v_a_1082_, 10);
lean_inc(v_queue_1086_);
lean_dec(v_a_1082_);
if (lean_obj_tag(v_queue_1086_) == 0)
{
uint8_t v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1090_; 
lean_dec_ref(v_queue_1086_);
v___x_1087_ = 0;
v___x_1088_ = lean_box(v___x_1087_);
if (v_isShared_1085_ == 0)
{
lean_ctor_set(v___x_1084_, 0, v___x_1088_);
v___x_1090_ = v___x_1084_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v___x_1088_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
return v___x_1090_;
}
}
else
{
uint8_t v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1095_; 
v___x_1092_ = 1;
v___x_1093_ = lean_box(v___x_1092_);
if (v_isShared_1085_ == 0)
{
lean_ctor_set(v___x_1084_, 0, v___x_1093_);
v___x_1095_ = v___x_1084_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v___x_1093_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
return v___x_1095_;
}
}
}
}
else
{
lean_object* v_a_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1105_; 
v_a_1098_ = lean_ctor_get(v___x_1081_, 0);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___x_1081_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1100_ = v___x_1081_;
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_a_1098_);
lean_dec(v___x_1081_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1103_; 
if (v_isShared_1101_ == 0)
{
v___x_1103_ = v___x_1100_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_a_1098_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
return v___x_1103_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty___boxed(lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_){
_start:
{
lean_object* v_res_1118_; 
v_res_1118_ = l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty(v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_);
lean_dec(v_a_1116_);
lean_dec_ref(v_a_1115_);
lean_dec(v_a_1114_);
lean_dec_ref(v_a_1113_);
lean_dec(v_a_1112_);
lean_dec_ref(v_a_1111_);
lean_dec(v_a_1110_);
lean_dec_ref(v_a_1109_);
lean_dec(v_a_1108_);
lean_dec(v_a_1107_);
lean_dec_ref(v_a_1106_);
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(lean_object* v_k_1119_, lean_object* v_t_1120_){
_start:
{
if (lean_obj_tag(v_t_1120_) == 0)
{
lean_object* v_k_1121_; lean_object* v_v_1122_; lean_object* v_l_1123_; lean_object* v_r_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1778_; 
v_k_1121_ = lean_ctor_get(v_t_1120_, 1);
v_v_1122_ = lean_ctor_get(v_t_1120_, 2);
v_l_1123_ = lean_ctor_get(v_t_1120_, 3);
v_r_1124_ = lean_ctor_get(v_t_1120_, 4);
v_isSharedCheck_1778_ = !lean_is_exclusive(v_t_1120_);
if (v_isSharedCheck_1778_ == 0)
{
lean_object* v_unused_1779_; 
v_unused_1779_ = lean_ctor_get(v_t_1120_, 0);
lean_dec(v_unused_1779_);
v___x_1126_ = v_t_1120_;
v_isShared_1127_ = v_isSharedCheck_1778_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_r_1124_);
lean_inc(v_l_1123_);
lean_inc(v_v_1122_);
lean_inc(v_k_1121_);
lean_dec(v_t_1120_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1778_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
uint8_t v___x_1128_; 
v___x_1128_ = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_compare(v_k_1119_, v_k_1121_);
switch(v___x_1128_)
{
case 0:
{
lean_object* v_impl_1129_; lean_object* v___x_1130_; 
v_impl_1129_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_k_1119_, v_l_1123_);
v___x_1130_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1129_) == 0)
{
if (lean_obj_tag(v_r_1124_) == 0)
{
lean_object* v_size_1131_; lean_object* v_size_1132_; lean_object* v_k_1133_; lean_object* v_v_1134_; lean_object* v_l_1135_; lean_object* v_r_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; uint8_t v___x_1139_; 
v_size_1131_ = lean_ctor_get(v_impl_1129_, 0);
lean_inc(v_size_1131_);
v_size_1132_ = lean_ctor_get(v_r_1124_, 0);
v_k_1133_ = lean_ctor_get(v_r_1124_, 1);
v_v_1134_ = lean_ctor_get(v_r_1124_, 2);
v_l_1135_ = lean_ctor_get(v_r_1124_, 3);
lean_inc(v_l_1135_);
v_r_1136_ = lean_ctor_get(v_r_1124_, 4);
v___x_1137_ = lean_unsigned_to_nat(3u);
v___x_1138_ = lean_nat_mul(v___x_1137_, v_size_1131_);
v___x_1139_ = lean_nat_dec_lt(v___x_1138_, v_size_1132_);
lean_dec(v___x_1138_);
if (v___x_1139_ == 0)
{
lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1143_; 
lean_dec(v_l_1135_);
v___x_1140_ = lean_nat_add(v___x_1130_, v_size_1131_);
lean_dec(v_size_1131_);
v___x_1141_ = lean_nat_add(v___x_1140_, v_size_1132_);
lean_dec(v___x_1140_);
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 3, v_impl_1129_);
lean_ctor_set(v___x_1126_, 0, v___x_1141_);
v___x_1143_ = v___x_1126_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v___x_1141_);
lean_ctor_set(v_reuseFailAlloc_1144_, 1, v_k_1121_);
lean_ctor_set(v_reuseFailAlloc_1144_, 2, v_v_1122_);
lean_ctor_set(v_reuseFailAlloc_1144_, 3, v_impl_1129_);
lean_ctor_set(v_reuseFailAlloc_1144_, 4, v_r_1124_);
v___x_1143_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
return v___x_1143_;
}
}
else
{
lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1208_; 
lean_inc(v_r_1136_);
lean_inc(v_v_1134_);
lean_inc(v_k_1133_);
lean_inc(v_size_1132_);
v_isSharedCheck_1208_ = !lean_is_exclusive(v_r_1124_);
if (v_isSharedCheck_1208_ == 0)
{
lean_object* v_unused_1209_; lean_object* v_unused_1210_; lean_object* v_unused_1211_; lean_object* v_unused_1212_; lean_object* v_unused_1213_; 
v_unused_1209_ = lean_ctor_get(v_r_1124_, 4);
lean_dec(v_unused_1209_);
v_unused_1210_ = lean_ctor_get(v_r_1124_, 3);
lean_dec(v_unused_1210_);
v_unused_1211_ = lean_ctor_get(v_r_1124_, 2);
lean_dec(v_unused_1211_);
v_unused_1212_ = lean_ctor_get(v_r_1124_, 1);
lean_dec(v_unused_1212_);
v_unused_1213_ = lean_ctor_get(v_r_1124_, 0);
lean_dec(v_unused_1213_);
v___x_1146_ = v_r_1124_;
v_isShared_1147_ = v_isSharedCheck_1208_;
goto v_resetjp_1145_;
}
else
{
lean_dec(v_r_1124_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1208_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v_size_1148_; lean_object* v_k_1149_; lean_object* v_v_1150_; lean_object* v_l_1151_; lean_object* v_r_1152_; lean_object* v_size_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; uint8_t v___x_1156_; 
v_size_1148_ = lean_ctor_get(v_l_1135_, 0);
v_k_1149_ = lean_ctor_get(v_l_1135_, 1);
v_v_1150_ = lean_ctor_get(v_l_1135_, 2);
v_l_1151_ = lean_ctor_get(v_l_1135_, 3);
v_r_1152_ = lean_ctor_get(v_l_1135_, 4);
v_size_1153_ = lean_ctor_get(v_r_1136_, 0);
v___x_1154_ = lean_unsigned_to_nat(2u);
v___x_1155_ = lean_nat_mul(v___x_1154_, v_size_1153_);
v___x_1156_ = lean_nat_dec_lt(v_size_1148_, v___x_1155_);
lean_dec(v___x_1155_);
if (v___x_1156_ == 0)
{
lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1184_; 
lean_inc(v_r_1152_);
lean_inc(v_l_1151_);
lean_inc(v_v_1150_);
lean_inc(v_k_1149_);
v_isSharedCheck_1184_ = !lean_is_exclusive(v_l_1135_);
if (v_isSharedCheck_1184_ == 0)
{
lean_object* v_unused_1185_; lean_object* v_unused_1186_; lean_object* v_unused_1187_; lean_object* v_unused_1188_; lean_object* v_unused_1189_; 
v_unused_1185_ = lean_ctor_get(v_l_1135_, 4);
lean_dec(v_unused_1185_);
v_unused_1186_ = lean_ctor_get(v_l_1135_, 3);
lean_dec(v_unused_1186_);
v_unused_1187_ = lean_ctor_get(v_l_1135_, 2);
lean_dec(v_unused_1187_);
v_unused_1188_ = lean_ctor_get(v_l_1135_, 1);
lean_dec(v_unused_1188_);
v_unused_1189_ = lean_ctor_get(v_l_1135_, 0);
lean_dec(v_unused_1189_);
v___x_1158_ = v_l_1135_;
v_isShared_1159_ = v_isSharedCheck_1184_;
goto v_resetjp_1157_;
}
else
{
lean_dec(v_l_1135_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1184_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___y_1163_; lean_object* v___y_1164_; lean_object* v___y_1165_; lean_object* v___y_1174_; 
v___x_1160_ = lean_nat_add(v___x_1130_, v_size_1131_);
lean_dec(v_size_1131_);
v___x_1161_ = lean_nat_add(v___x_1160_, v_size_1132_);
lean_dec(v_size_1132_);
if (lean_obj_tag(v_l_1151_) == 0)
{
lean_object* v_size_1182_; 
v_size_1182_ = lean_ctor_get(v_l_1151_, 0);
lean_inc(v_size_1182_);
v___y_1174_ = v_size_1182_;
goto v___jp_1173_;
}
else
{
lean_object* v___x_1183_; 
v___x_1183_ = lean_unsigned_to_nat(0u);
v___y_1174_ = v___x_1183_;
goto v___jp_1173_;
}
v___jp_1162_:
{
lean_object* v___x_1166_; lean_object* v___x_1168_; 
v___x_1166_ = lean_nat_add(v___y_1163_, v___y_1165_);
lean_dec(v___y_1165_);
lean_dec(v___y_1163_);
if (v_isShared_1159_ == 0)
{
lean_ctor_set(v___x_1158_, 4, v_r_1136_);
lean_ctor_set(v___x_1158_, 3, v_r_1152_);
lean_ctor_set(v___x_1158_, 2, v_v_1134_);
lean_ctor_set(v___x_1158_, 1, v_k_1133_);
lean_ctor_set(v___x_1158_, 0, v___x_1166_);
v___x_1168_ = v___x_1158_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v___x_1166_);
lean_ctor_set(v_reuseFailAlloc_1172_, 1, v_k_1133_);
lean_ctor_set(v_reuseFailAlloc_1172_, 2, v_v_1134_);
lean_ctor_set(v_reuseFailAlloc_1172_, 3, v_r_1152_);
lean_ctor_set(v_reuseFailAlloc_1172_, 4, v_r_1136_);
v___x_1168_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
lean_object* v___x_1170_; 
if (v_isShared_1147_ == 0)
{
lean_ctor_set(v___x_1146_, 4, v___x_1168_);
lean_ctor_set(v___x_1146_, 3, v___y_1164_);
lean_ctor_set(v___x_1146_, 2, v_v_1150_);
lean_ctor_set(v___x_1146_, 1, v_k_1149_);
lean_ctor_set(v___x_1146_, 0, v___x_1161_);
v___x_1170_ = v___x_1146_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v___x_1161_);
lean_ctor_set(v_reuseFailAlloc_1171_, 1, v_k_1149_);
lean_ctor_set(v_reuseFailAlloc_1171_, 2, v_v_1150_);
lean_ctor_set(v_reuseFailAlloc_1171_, 3, v___y_1164_);
lean_ctor_set(v_reuseFailAlloc_1171_, 4, v___x_1168_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
}
v___jp_1173_:
{
lean_object* v___x_1175_; lean_object* v___x_1177_; 
v___x_1175_ = lean_nat_add(v___x_1160_, v___y_1174_);
lean_dec(v___y_1174_);
lean_dec(v___x_1160_);
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 4, v_l_1151_);
lean_ctor_set(v___x_1126_, 3, v_impl_1129_);
lean_ctor_set(v___x_1126_, 0, v___x_1175_);
v___x_1177_ = v___x_1126_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v___x_1175_);
lean_ctor_set(v_reuseFailAlloc_1181_, 1, v_k_1121_);
lean_ctor_set(v_reuseFailAlloc_1181_, 2, v_v_1122_);
lean_ctor_set(v_reuseFailAlloc_1181_, 3, v_impl_1129_);
lean_ctor_set(v_reuseFailAlloc_1181_, 4, v_l_1151_);
v___x_1177_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
lean_object* v___x_1178_; 
v___x_1178_ = lean_nat_add(v___x_1130_, v_size_1153_);
if (lean_obj_tag(v_r_1152_) == 0)
{
lean_object* v_size_1179_; 
v_size_1179_ = lean_ctor_get(v_r_1152_, 0);
lean_inc(v_size_1179_);
v___y_1163_ = v___x_1178_;
v___y_1164_ = v___x_1177_;
v___y_1165_ = v_size_1179_;
goto v___jp_1162_;
}
else
{
lean_object* v___x_1180_; 
v___x_1180_ = lean_unsigned_to_nat(0u);
v___y_1163_ = v___x_1178_;
v___y_1164_ = v___x_1177_;
v___y_1165_ = v___x_1180_;
goto v___jp_1162_;
}
}
}
}
}
else
{
lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1194_; 
lean_del_object(v___x_1126_);
v___x_1190_ = lean_nat_add(v___x_1130_, v_size_1131_);
lean_dec(v_size_1131_);
v___x_1191_ = lean_nat_add(v___x_1190_, v_size_1132_);
lean_dec(v_size_1132_);
v___x_1192_ = lean_nat_add(v___x_1190_, v_size_1148_);
lean_dec(v___x_1190_);
lean_inc_ref(v_impl_1129_);
if (v_isShared_1147_ == 0)
{
lean_ctor_set(v___x_1146_, 4, v_l_1135_);
lean_ctor_set(v___x_1146_, 3, v_impl_1129_);
lean_ctor_set(v___x_1146_, 2, v_v_1122_);
lean_ctor_set(v___x_1146_, 1, v_k_1121_);
lean_ctor_set(v___x_1146_, 0, v___x_1192_);
v___x_1194_ = v___x_1146_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v___x_1192_);
lean_ctor_set(v_reuseFailAlloc_1207_, 1, v_k_1121_);
lean_ctor_set(v_reuseFailAlloc_1207_, 2, v_v_1122_);
lean_ctor_set(v_reuseFailAlloc_1207_, 3, v_impl_1129_);
lean_ctor_set(v_reuseFailAlloc_1207_, 4, v_l_1135_);
v___x_1194_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1201_; 
v_isSharedCheck_1201_ = !lean_is_exclusive(v_impl_1129_);
if (v_isSharedCheck_1201_ == 0)
{
lean_object* v_unused_1202_; lean_object* v_unused_1203_; lean_object* v_unused_1204_; lean_object* v_unused_1205_; lean_object* v_unused_1206_; 
v_unused_1202_ = lean_ctor_get(v_impl_1129_, 4);
lean_dec(v_unused_1202_);
v_unused_1203_ = lean_ctor_get(v_impl_1129_, 3);
lean_dec(v_unused_1203_);
v_unused_1204_ = lean_ctor_get(v_impl_1129_, 2);
lean_dec(v_unused_1204_);
v_unused_1205_ = lean_ctor_get(v_impl_1129_, 1);
lean_dec(v_unused_1205_);
v_unused_1206_ = lean_ctor_get(v_impl_1129_, 0);
lean_dec(v_unused_1206_);
v___x_1196_ = v_impl_1129_;
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
else
{
lean_dec(v_impl_1129_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1199_; 
if (v_isShared_1197_ == 0)
{
lean_ctor_set(v___x_1196_, 4, v_r_1136_);
lean_ctor_set(v___x_1196_, 3, v___x_1194_);
lean_ctor_set(v___x_1196_, 2, v_v_1134_);
lean_ctor_set(v___x_1196_, 1, v_k_1133_);
lean_ctor_set(v___x_1196_, 0, v___x_1191_);
v___x_1199_ = v___x_1196_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v___x_1191_);
lean_ctor_set(v_reuseFailAlloc_1200_, 1, v_k_1133_);
lean_ctor_set(v_reuseFailAlloc_1200_, 2, v_v_1134_);
lean_ctor_set(v_reuseFailAlloc_1200_, 3, v___x_1194_);
lean_ctor_set(v_reuseFailAlloc_1200_, 4, v_r_1136_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1214_; lean_object* v___x_1215_; lean_object* v___x_1217_; 
v_size_1214_ = lean_ctor_get(v_impl_1129_, 0);
lean_inc(v_size_1214_);
v___x_1215_ = lean_nat_add(v___x_1130_, v_size_1214_);
lean_dec(v_size_1214_);
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 3, v_impl_1129_);
lean_ctor_set(v___x_1126_, 0, v___x_1215_);
v___x_1217_ = v___x_1126_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v___x_1215_);
lean_ctor_set(v_reuseFailAlloc_1218_, 1, v_k_1121_);
lean_ctor_set(v_reuseFailAlloc_1218_, 2, v_v_1122_);
lean_ctor_set(v_reuseFailAlloc_1218_, 3, v_impl_1129_);
lean_ctor_set(v_reuseFailAlloc_1218_, 4, v_r_1124_);
v___x_1217_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
return v___x_1217_;
}
}
}
else
{
if (lean_obj_tag(v_r_1124_) == 0)
{
lean_object* v_l_1219_; 
v_l_1219_ = lean_ctor_get(v_r_1124_, 3);
lean_inc(v_l_1219_);
if (lean_obj_tag(v_l_1219_) == 0)
{
lean_object* v_r_1220_; 
v_r_1220_ = lean_ctor_get(v_r_1124_, 4);
lean_inc(v_r_1220_);
if (lean_obj_tag(v_r_1220_) == 0)
{
lean_object* v_size_1221_; lean_object* v_k_1222_; lean_object* v_v_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1236_; 
v_size_1221_ = lean_ctor_get(v_r_1124_, 0);
v_k_1222_ = lean_ctor_get(v_r_1124_, 1);
v_v_1223_ = lean_ctor_get(v_r_1124_, 2);
v_isSharedCheck_1236_ = !lean_is_exclusive(v_r_1124_);
if (v_isSharedCheck_1236_ == 0)
{
lean_object* v_unused_1237_; lean_object* v_unused_1238_; 
v_unused_1237_ = lean_ctor_get(v_r_1124_, 4);
lean_dec(v_unused_1237_);
v_unused_1238_ = lean_ctor_get(v_r_1124_, 3);
lean_dec(v_unused_1238_);
v___x_1225_ = v_r_1124_;
v_isShared_1226_ = v_isSharedCheck_1236_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_v_1223_);
lean_inc(v_k_1222_);
lean_inc(v_size_1221_);
lean_dec(v_r_1124_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1236_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v_size_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1231_; 
v_size_1227_ = lean_ctor_get(v_l_1219_, 0);
v___x_1228_ = lean_nat_add(v___x_1130_, v_size_1221_);
lean_dec(v_size_1221_);
v___x_1229_ = lean_nat_add(v___x_1130_, v_size_1227_);
if (v_isShared_1226_ == 0)
{
lean_ctor_set(v___x_1225_, 4, v_l_1219_);
lean_ctor_set(v___x_1225_, 3, v_impl_1129_);
lean_ctor_set(v___x_1225_, 2, v_v_1122_);
lean_ctor_set(v___x_1225_, 1, v_k_1121_);
lean_ctor_set(v___x_1225_, 0, v___x_1229_);
v___x_1231_ = v___x_1225_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v___x_1229_);
lean_ctor_set(v_reuseFailAlloc_1235_, 1, v_k_1121_);
lean_ctor_set(v_reuseFailAlloc_1235_, 2, v_v_1122_);
lean_ctor_set(v_reuseFailAlloc_1235_, 3, v_impl_1129_);
lean_ctor_set(v_reuseFailAlloc_1235_, 4, v_l_1219_);
v___x_1231_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
lean_object* v___x_1233_; 
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 4, v_r_1220_);
lean_ctor_set(v___x_1126_, 3, v___x_1231_);
lean_ctor_set(v___x_1126_, 2, v_v_1223_);
lean_ctor_set(v___x_1126_, 1, v_k_1222_);
lean_ctor_set(v___x_1126_, 0, v___x_1228_);
v___x_1233_ = v___x_1126_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v___x_1228_);
lean_ctor_set(v_reuseFailAlloc_1234_, 1, v_k_1222_);
lean_ctor_set(v_reuseFailAlloc_1234_, 2, v_v_1223_);
lean_ctor_set(v_reuseFailAlloc_1234_, 3, v___x_1231_);
lean_ctor_set(v_reuseFailAlloc_1234_, 4, v_r_1220_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
return v___x_1233_;
}
}
}
}
else
{
lean_object* v_k_1239_; lean_object* v_v_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1263_; 
v_k_1239_ = lean_ctor_get(v_r_1124_, 1);
v_v_1240_ = lean_ctor_get(v_r_1124_, 2);
v_isSharedCheck_1263_ = !lean_is_exclusive(v_r_1124_);
if (v_isSharedCheck_1263_ == 0)
{
lean_object* v_unused_1264_; lean_object* v_unused_1265_; lean_object* v_unused_1266_; 
v_unused_1264_ = lean_ctor_get(v_r_1124_, 4);
lean_dec(v_unused_1264_);
v_unused_1265_ = lean_ctor_get(v_r_1124_, 3);
lean_dec(v_unused_1265_);
v_unused_1266_ = lean_ctor_get(v_r_1124_, 0);
lean_dec(v_unused_1266_);
v___x_1242_ = v_r_1124_;
v_isShared_1243_ = v_isSharedCheck_1263_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_v_1240_);
lean_inc(v_k_1239_);
lean_dec(v_r_1124_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1263_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v_k_1244_; lean_object* v_v_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1259_; 
v_k_1244_ = lean_ctor_get(v_l_1219_, 1);
v_v_1245_ = lean_ctor_get(v_l_1219_, 2);
v_isSharedCheck_1259_ = !lean_is_exclusive(v_l_1219_);
if (v_isSharedCheck_1259_ == 0)
{
lean_object* v_unused_1260_; lean_object* v_unused_1261_; lean_object* v_unused_1262_; 
v_unused_1260_ = lean_ctor_get(v_l_1219_, 4);
lean_dec(v_unused_1260_);
v_unused_1261_ = lean_ctor_get(v_l_1219_, 3);
lean_dec(v_unused_1261_);
v_unused_1262_ = lean_ctor_get(v_l_1219_, 0);
lean_dec(v_unused_1262_);
v___x_1247_ = v_l_1219_;
v_isShared_1248_ = v_isSharedCheck_1259_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_v_1245_);
lean_inc(v_k_1244_);
lean_dec(v_l_1219_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1259_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1249_; lean_object* v___x_1251_; 
v___x_1249_ = lean_unsigned_to_nat(3u);
if (v_isShared_1248_ == 0)
{
lean_ctor_set(v___x_1247_, 4, v_r_1220_);
lean_ctor_set(v___x_1247_, 3, v_r_1220_);
lean_ctor_set(v___x_1247_, 2, v_v_1122_);
lean_ctor_set(v___x_1247_, 1, v_k_1121_);
lean_ctor_set(v___x_1247_, 0, v___x_1130_);
v___x_1251_ = v___x_1247_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v___x_1130_);
lean_ctor_set(v_reuseFailAlloc_1258_, 1, v_k_1121_);
lean_ctor_set(v_reuseFailAlloc_1258_, 2, v_v_1122_);
lean_ctor_set(v_reuseFailAlloc_1258_, 3, v_r_1220_);
lean_ctor_set(v_reuseFailAlloc_1258_, 4, v_r_1220_);
v___x_1251_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
lean_object* v___x_1253_; 
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 3, v_r_1220_);
lean_ctor_set(v___x_1242_, 0, v___x_1130_);
v___x_1253_ = v___x_1242_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v___x_1130_);
lean_ctor_set(v_reuseFailAlloc_1257_, 1, v_k_1239_);
lean_ctor_set(v_reuseFailAlloc_1257_, 2, v_v_1240_);
lean_ctor_set(v_reuseFailAlloc_1257_, 3, v_r_1220_);
lean_ctor_set(v_reuseFailAlloc_1257_, 4, v_r_1220_);
v___x_1253_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
lean_object* v___x_1255_; 
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 4, v___x_1253_);
lean_ctor_set(v___x_1126_, 3, v___x_1251_);
lean_ctor_set(v___x_1126_, 2, v_v_1245_);
lean_ctor_set(v___x_1126_, 1, v_k_1244_);
lean_ctor_set(v___x_1126_, 0, v___x_1249_);
v___x_1255_ = v___x_1126_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v___x_1249_);
lean_ctor_set(v_reuseFailAlloc_1256_, 1, v_k_1244_);
lean_ctor_set(v_reuseFailAlloc_1256_, 2, v_v_1245_);
lean_ctor_set(v_reuseFailAlloc_1256_, 3, v___x_1251_);
lean_ctor_set(v_reuseFailAlloc_1256_, 4, v___x_1253_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_1267_; 
v_r_1267_ = lean_ctor_get(v_r_1124_, 4);
lean_inc(v_r_1267_);
if (lean_obj_tag(v_r_1267_) == 0)
{
lean_object* v_k_1268_; lean_object* v_v_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1280_; 
v_k_1268_ = lean_ctor_get(v_r_1124_, 1);
v_v_1269_ = lean_ctor_get(v_r_1124_, 2);
v_isSharedCheck_1280_ = !lean_is_exclusive(v_r_1124_);
if (v_isSharedCheck_1280_ == 0)
{
lean_object* v_unused_1281_; lean_object* v_unused_1282_; lean_object* v_unused_1283_; 
v_unused_1281_ = lean_ctor_get(v_r_1124_, 4);
lean_dec(v_unused_1281_);
v_unused_1282_ = lean_ctor_get(v_r_1124_, 3);
lean_dec(v_unused_1282_);
v_unused_1283_ = lean_ctor_get(v_r_1124_, 0);
lean_dec(v_unused_1283_);
v___x_1271_ = v_r_1124_;
v_isShared_1272_ = v_isSharedCheck_1280_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_v_1269_);
lean_inc(v_k_1268_);
lean_dec(v_r_1124_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1280_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v___x_1273_; lean_object* v___x_1275_; 
v___x_1273_ = lean_unsigned_to_nat(3u);
if (v_isShared_1272_ == 0)
{
lean_ctor_set(v___x_1271_, 4, v_l_1219_);
lean_ctor_set(v___x_1271_, 2, v_v_1122_);
lean_ctor_set(v___x_1271_, 1, v_k_1121_);
lean_ctor_set(v___x_1271_, 0, v___x_1130_);
v___x_1275_ = v___x_1271_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v___x_1130_);
lean_ctor_set(v_reuseFailAlloc_1279_, 1, v_k_1121_);
lean_ctor_set(v_reuseFailAlloc_1279_, 2, v_v_1122_);
lean_ctor_set(v_reuseFailAlloc_1279_, 3, v_l_1219_);
lean_ctor_set(v_reuseFailAlloc_1279_, 4, v_l_1219_);
v___x_1275_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
lean_object* v___x_1277_; 
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 4, v_r_1267_);
lean_ctor_set(v___x_1126_, 3, v___x_1275_);
lean_ctor_set(v___x_1126_, 2, v_v_1269_);
lean_ctor_set(v___x_1126_, 1, v_k_1268_);
lean_ctor_set(v___x_1126_, 0, v___x_1273_);
v___x_1277_ = v___x_1126_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v___x_1273_);
lean_ctor_set(v_reuseFailAlloc_1278_, 1, v_k_1268_);
lean_ctor_set(v_reuseFailAlloc_1278_, 2, v_v_1269_);
lean_ctor_set(v_reuseFailAlloc_1278_, 3, v___x_1275_);
lean_ctor_set(v_reuseFailAlloc_1278_, 4, v_r_1267_);
v___x_1277_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
return v___x_1277_;
}
}
}
}
else
{
lean_object* v_size_1284_; lean_object* v_k_1285_; lean_object* v_v_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1297_; 
v_size_1284_ = lean_ctor_get(v_r_1124_, 0);
v_k_1285_ = lean_ctor_get(v_r_1124_, 1);
v_v_1286_ = lean_ctor_get(v_r_1124_, 2);
v_isSharedCheck_1297_ = !lean_is_exclusive(v_r_1124_);
if (v_isSharedCheck_1297_ == 0)
{
lean_object* v_unused_1298_; lean_object* v_unused_1299_; 
v_unused_1298_ = lean_ctor_get(v_r_1124_, 4);
lean_dec(v_unused_1298_);
v_unused_1299_ = lean_ctor_get(v_r_1124_, 3);
lean_dec(v_unused_1299_);
v___x_1288_ = v_r_1124_;
v_isShared_1289_ = v_isSharedCheck_1297_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_v_1286_);
lean_inc(v_k_1285_);
lean_inc(v_size_1284_);
lean_dec(v_r_1124_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1297_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1291_; 
if (v_isShared_1289_ == 0)
{
lean_ctor_set(v___x_1288_, 3, v_r_1267_);
v___x_1291_ = v___x_1288_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_size_1284_);
lean_ctor_set(v_reuseFailAlloc_1296_, 1, v_k_1285_);
lean_ctor_set(v_reuseFailAlloc_1296_, 2, v_v_1286_);
lean_ctor_set(v_reuseFailAlloc_1296_, 3, v_r_1267_);
lean_ctor_set(v_reuseFailAlloc_1296_, 4, v_r_1267_);
v___x_1291_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
lean_object* v___x_1292_; lean_object* v___x_1294_; 
v___x_1292_ = lean_unsigned_to_nat(2u);
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 4, v___x_1291_);
lean_ctor_set(v___x_1126_, 3, v_r_1267_);
lean_ctor_set(v___x_1126_, 0, v___x_1292_);
v___x_1294_ = v___x_1126_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v___x_1292_);
lean_ctor_set(v_reuseFailAlloc_1295_, 1, v_k_1121_);
lean_ctor_set(v_reuseFailAlloc_1295_, 2, v_v_1122_);
lean_ctor_set(v_reuseFailAlloc_1295_, 3, v_r_1267_);
lean_ctor_set(v_reuseFailAlloc_1295_, 4, v___x_1291_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
return v___x_1294_;
}
}
}
}
}
}
else
{
lean_object* v___x_1301_; 
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 3, v_r_1124_);
lean_ctor_set(v___x_1126_, 0, v___x_1130_);
v___x_1301_ = v___x_1126_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v___x_1130_);
lean_ctor_set(v_reuseFailAlloc_1302_, 1, v_k_1121_);
lean_ctor_set(v_reuseFailAlloc_1302_, 2, v_v_1122_);
lean_ctor_set(v_reuseFailAlloc_1302_, 3, v_r_1124_);
lean_ctor_set(v_reuseFailAlloc_1302_, 4, v_r_1124_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
}
case 1:
{
lean_del_object(v___x_1126_);
lean_dec(v_v_1122_);
lean_dec(v_k_1121_);
if (lean_obj_tag(v_l_1123_) == 0)
{
if (lean_obj_tag(v_r_1124_) == 0)
{
lean_object* v_size_1303_; lean_object* v_k_1304_; lean_object* v_v_1305_; lean_object* v_l_1306_; lean_object* v_r_1307_; lean_object* v_size_1308_; lean_object* v_k_1309_; lean_object* v_v_1310_; lean_object* v_l_1311_; lean_object* v_r_1312_; lean_object* v___x_1313_; uint8_t v___x_1314_; 
v_size_1303_ = lean_ctor_get(v_l_1123_, 0);
v_k_1304_ = lean_ctor_get(v_l_1123_, 1);
v_v_1305_ = lean_ctor_get(v_l_1123_, 2);
v_l_1306_ = lean_ctor_get(v_l_1123_, 3);
v_r_1307_ = lean_ctor_get(v_l_1123_, 4);
lean_inc(v_r_1307_);
v_size_1308_ = lean_ctor_get(v_r_1124_, 0);
v_k_1309_ = lean_ctor_get(v_r_1124_, 1);
v_v_1310_ = lean_ctor_get(v_r_1124_, 2);
v_l_1311_ = lean_ctor_get(v_r_1124_, 3);
lean_inc(v_l_1311_);
v_r_1312_ = lean_ctor_get(v_r_1124_, 4);
v___x_1313_ = lean_unsigned_to_nat(1u);
v___x_1314_ = lean_nat_dec_lt(v_size_1303_, v_size_1308_);
if (v___x_1314_ == 0)
{
lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1450_; 
lean_inc(v_l_1306_);
lean_inc(v_v_1305_);
lean_inc(v_k_1304_);
v_isSharedCheck_1450_ = !lean_is_exclusive(v_l_1123_);
if (v_isSharedCheck_1450_ == 0)
{
lean_object* v_unused_1451_; lean_object* v_unused_1452_; lean_object* v_unused_1453_; lean_object* v_unused_1454_; lean_object* v_unused_1455_; 
v_unused_1451_ = lean_ctor_get(v_l_1123_, 4);
lean_dec(v_unused_1451_);
v_unused_1452_ = lean_ctor_get(v_l_1123_, 3);
lean_dec(v_unused_1452_);
v_unused_1453_ = lean_ctor_get(v_l_1123_, 2);
lean_dec(v_unused_1453_);
v_unused_1454_ = lean_ctor_get(v_l_1123_, 1);
lean_dec(v_unused_1454_);
v_unused_1455_ = lean_ctor_get(v_l_1123_, 0);
lean_dec(v_unused_1455_);
v___x_1316_ = v_l_1123_;
v_isShared_1317_ = v_isSharedCheck_1450_;
goto v_resetjp_1315_;
}
else
{
lean_dec(v_l_1123_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1450_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v___x_1318_; lean_object* v_tree_1319_; 
v___x_1318_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_1304_, v_v_1305_, v_l_1306_, v_r_1307_);
v_tree_1319_ = lean_ctor_get(v___x_1318_, 2);
lean_inc(v_tree_1319_);
if (lean_obj_tag(v_tree_1319_) == 0)
{
lean_object* v_k_1320_; lean_object* v_v_1321_; lean_object* v_size_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; uint8_t v___x_1325_; 
v_k_1320_ = lean_ctor_get(v___x_1318_, 0);
lean_inc(v_k_1320_);
v_v_1321_ = lean_ctor_get(v___x_1318_, 1);
lean_inc(v_v_1321_);
lean_dec_ref(v___x_1318_);
v_size_1322_ = lean_ctor_get(v_tree_1319_, 0);
v___x_1323_ = lean_unsigned_to_nat(3u);
v___x_1324_ = lean_nat_mul(v___x_1323_, v_size_1322_);
v___x_1325_ = lean_nat_dec_lt(v___x_1324_, v_size_1308_);
lean_dec(v___x_1324_);
if (v___x_1325_ == 0)
{
lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1329_; 
lean_dec(v_l_1311_);
v___x_1326_ = lean_nat_add(v___x_1313_, v_size_1322_);
v___x_1327_ = lean_nat_add(v___x_1326_, v_size_1308_);
lean_dec(v___x_1326_);
if (v_isShared_1317_ == 0)
{
lean_ctor_set(v___x_1316_, 4, v_r_1124_);
lean_ctor_set(v___x_1316_, 3, v_tree_1319_);
lean_ctor_set(v___x_1316_, 2, v_v_1321_);
lean_ctor_set(v___x_1316_, 1, v_k_1320_);
lean_ctor_set(v___x_1316_, 0, v___x_1327_);
v___x_1329_ = v___x_1316_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v___x_1327_);
lean_ctor_set(v_reuseFailAlloc_1330_, 1, v_k_1320_);
lean_ctor_set(v_reuseFailAlloc_1330_, 2, v_v_1321_);
lean_ctor_set(v_reuseFailAlloc_1330_, 3, v_tree_1319_);
lean_ctor_set(v_reuseFailAlloc_1330_, 4, v_r_1124_);
v___x_1329_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
return v___x_1329_;
}
}
else
{
lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1385_; 
lean_inc(v_r_1312_);
lean_inc(v_v_1310_);
lean_inc(v_k_1309_);
lean_inc(v_size_1308_);
v_isSharedCheck_1385_ = !lean_is_exclusive(v_r_1124_);
if (v_isSharedCheck_1385_ == 0)
{
lean_object* v_unused_1386_; lean_object* v_unused_1387_; lean_object* v_unused_1388_; lean_object* v_unused_1389_; lean_object* v_unused_1390_; 
v_unused_1386_ = lean_ctor_get(v_r_1124_, 4);
lean_dec(v_unused_1386_);
v_unused_1387_ = lean_ctor_get(v_r_1124_, 3);
lean_dec(v_unused_1387_);
v_unused_1388_ = lean_ctor_get(v_r_1124_, 2);
lean_dec(v_unused_1388_);
v_unused_1389_ = lean_ctor_get(v_r_1124_, 1);
lean_dec(v_unused_1389_);
v_unused_1390_ = lean_ctor_get(v_r_1124_, 0);
lean_dec(v_unused_1390_);
v___x_1332_ = v_r_1124_;
v_isShared_1333_ = v_isSharedCheck_1385_;
goto v_resetjp_1331_;
}
else
{
lean_dec(v_r_1124_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1385_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v_size_1334_; lean_object* v_k_1335_; lean_object* v_v_1336_; lean_object* v_l_1337_; lean_object* v_r_1338_; lean_object* v_size_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; uint8_t v___x_1342_; 
v_size_1334_ = lean_ctor_get(v_l_1311_, 0);
v_k_1335_ = lean_ctor_get(v_l_1311_, 1);
v_v_1336_ = lean_ctor_get(v_l_1311_, 2);
v_l_1337_ = lean_ctor_get(v_l_1311_, 3);
v_r_1338_ = lean_ctor_get(v_l_1311_, 4);
v_size_1339_ = lean_ctor_get(v_r_1312_, 0);
v___x_1340_ = lean_unsigned_to_nat(2u);
v___x_1341_ = lean_nat_mul(v___x_1340_, v_size_1339_);
v___x_1342_ = lean_nat_dec_lt(v_size_1334_, v___x_1341_);
lean_dec(v___x_1341_);
if (v___x_1342_ == 0)
{
lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1370_; 
lean_inc(v_r_1338_);
lean_inc(v_l_1337_);
lean_inc(v_v_1336_);
lean_inc(v_k_1335_);
v_isSharedCheck_1370_ = !lean_is_exclusive(v_l_1311_);
if (v_isSharedCheck_1370_ == 0)
{
lean_object* v_unused_1371_; lean_object* v_unused_1372_; lean_object* v_unused_1373_; lean_object* v_unused_1374_; lean_object* v_unused_1375_; 
v_unused_1371_ = lean_ctor_get(v_l_1311_, 4);
lean_dec(v_unused_1371_);
v_unused_1372_ = lean_ctor_get(v_l_1311_, 3);
lean_dec(v_unused_1372_);
v_unused_1373_ = lean_ctor_get(v_l_1311_, 2);
lean_dec(v_unused_1373_);
v_unused_1374_ = lean_ctor_get(v_l_1311_, 1);
lean_dec(v_unused_1374_);
v_unused_1375_ = lean_ctor_get(v_l_1311_, 0);
lean_dec(v_unused_1375_);
v___x_1344_ = v_l_1311_;
v_isShared_1345_ = v_isSharedCheck_1370_;
goto v_resetjp_1343_;
}
else
{
lean_dec(v_l_1311_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1370_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___y_1349_; lean_object* v___y_1350_; lean_object* v___y_1351_; lean_object* v___y_1360_; 
v___x_1346_ = lean_nat_add(v___x_1313_, v_size_1322_);
v___x_1347_ = lean_nat_add(v___x_1346_, v_size_1308_);
lean_dec(v_size_1308_);
if (lean_obj_tag(v_l_1337_) == 0)
{
lean_object* v_size_1368_; 
v_size_1368_ = lean_ctor_get(v_l_1337_, 0);
lean_inc(v_size_1368_);
v___y_1360_ = v_size_1368_;
goto v___jp_1359_;
}
else
{
lean_object* v___x_1369_; 
v___x_1369_ = lean_unsigned_to_nat(0u);
v___y_1360_ = v___x_1369_;
goto v___jp_1359_;
}
v___jp_1348_:
{
lean_object* v___x_1352_; lean_object* v___x_1354_; 
v___x_1352_ = lean_nat_add(v___y_1350_, v___y_1351_);
lean_dec(v___y_1351_);
lean_dec(v___y_1350_);
if (v_isShared_1345_ == 0)
{
lean_ctor_set(v___x_1344_, 4, v_r_1312_);
lean_ctor_set(v___x_1344_, 3, v_r_1338_);
lean_ctor_set(v___x_1344_, 2, v_v_1310_);
lean_ctor_set(v___x_1344_, 1, v_k_1309_);
lean_ctor_set(v___x_1344_, 0, v___x_1352_);
v___x_1354_ = v___x_1344_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v___x_1352_);
lean_ctor_set(v_reuseFailAlloc_1358_, 1, v_k_1309_);
lean_ctor_set(v_reuseFailAlloc_1358_, 2, v_v_1310_);
lean_ctor_set(v_reuseFailAlloc_1358_, 3, v_r_1338_);
lean_ctor_set(v_reuseFailAlloc_1358_, 4, v_r_1312_);
v___x_1354_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
lean_object* v___x_1356_; 
if (v_isShared_1333_ == 0)
{
lean_ctor_set(v___x_1332_, 4, v___x_1354_);
lean_ctor_set(v___x_1332_, 3, v___y_1349_);
lean_ctor_set(v___x_1332_, 2, v_v_1336_);
lean_ctor_set(v___x_1332_, 1, v_k_1335_);
lean_ctor_set(v___x_1332_, 0, v___x_1347_);
v___x_1356_ = v___x_1332_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v___x_1347_);
lean_ctor_set(v_reuseFailAlloc_1357_, 1, v_k_1335_);
lean_ctor_set(v_reuseFailAlloc_1357_, 2, v_v_1336_);
lean_ctor_set(v_reuseFailAlloc_1357_, 3, v___y_1349_);
lean_ctor_set(v_reuseFailAlloc_1357_, 4, v___x_1354_);
v___x_1356_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
return v___x_1356_;
}
}
}
v___jp_1359_:
{
lean_object* v___x_1361_; lean_object* v___x_1363_; 
v___x_1361_ = lean_nat_add(v___x_1346_, v___y_1360_);
lean_dec(v___y_1360_);
lean_dec(v___x_1346_);
if (v_isShared_1317_ == 0)
{
lean_ctor_set(v___x_1316_, 4, v_l_1337_);
lean_ctor_set(v___x_1316_, 3, v_tree_1319_);
lean_ctor_set(v___x_1316_, 2, v_v_1321_);
lean_ctor_set(v___x_1316_, 1, v_k_1320_);
lean_ctor_set(v___x_1316_, 0, v___x_1361_);
v___x_1363_ = v___x_1316_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v___x_1361_);
lean_ctor_set(v_reuseFailAlloc_1367_, 1, v_k_1320_);
lean_ctor_set(v_reuseFailAlloc_1367_, 2, v_v_1321_);
lean_ctor_set(v_reuseFailAlloc_1367_, 3, v_tree_1319_);
lean_ctor_set(v_reuseFailAlloc_1367_, 4, v_l_1337_);
v___x_1363_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
lean_object* v___x_1364_; 
v___x_1364_ = lean_nat_add(v___x_1313_, v_size_1339_);
if (lean_obj_tag(v_r_1338_) == 0)
{
lean_object* v_size_1365_; 
v_size_1365_ = lean_ctor_get(v_r_1338_, 0);
lean_inc(v_size_1365_);
v___y_1349_ = v___x_1363_;
v___y_1350_ = v___x_1364_;
v___y_1351_ = v_size_1365_;
goto v___jp_1348_;
}
else
{
lean_object* v___x_1366_; 
v___x_1366_ = lean_unsigned_to_nat(0u);
v___y_1349_ = v___x_1363_;
v___y_1350_ = v___x_1364_;
v___y_1351_ = v___x_1366_;
goto v___jp_1348_;
}
}
}
}
}
else
{
lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1380_; 
v___x_1376_ = lean_nat_add(v___x_1313_, v_size_1322_);
v___x_1377_ = lean_nat_add(v___x_1376_, v_size_1308_);
lean_dec(v_size_1308_);
v___x_1378_ = lean_nat_add(v___x_1376_, v_size_1334_);
lean_dec(v___x_1376_);
if (v_isShared_1333_ == 0)
{
lean_ctor_set(v___x_1332_, 4, v_l_1311_);
lean_ctor_set(v___x_1332_, 3, v_tree_1319_);
lean_ctor_set(v___x_1332_, 2, v_v_1321_);
lean_ctor_set(v___x_1332_, 1, v_k_1320_);
lean_ctor_set(v___x_1332_, 0, v___x_1378_);
v___x_1380_ = v___x_1332_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v___x_1378_);
lean_ctor_set(v_reuseFailAlloc_1384_, 1, v_k_1320_);
lean_ctor_set(v_reuseFailAlloc_1384_, 2, v_v_1321_);
lean_ctor_set(v_reuseFailAlloc_1384_, 3, v_tree_1319_);
lean_ctor_set(v_reuseFailAlloc_1384_, 4, v_l_1311_);
v___x_1380_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
lean_object* v___x_1382_; 
if (v_isShared_1317_ == 0)
{
lean_ctor_set(v___x_1316_, 4, v_r_1312_);
lean_ctor_set(v___x_1316_, 3, v___x_1380_);
lean_ctor_set(v___x_1316_, 2, v_v_1310_);
lean_ctor_set(v___x_1316_, 1, v_k_1309_);
lean_ctor_set(v___x_1316_, 0, v___x_1377_);
v___x_1382_ = v___x_1316_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v___x_1377_);
lean_ctor_set(v_reuseFailAlloc_1383_, 1, v_k_1309_);
lean_ctor_set(v_reuseFailAlloc_1383_, 2, v_v_1310_);
lean_ctor_set(v_reuseFailAlloc_1383_, 3, v___x_1380_);
lean_ctor_set(v_reuseFailAlloc_1383_, 4, v_r_1312_);
v___x_1382_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
return v___x_1382_;
}
}
}
}
}
}
else
{
lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1444_; 
lean_inc(v_r_1312_);
lean_inc(v_v_1310_);
lean_inc(v_k_1309_);
lean_inc(v_size_1308_);
v_isSharedCheck_1444_ = !lean_is_exclusive(v_r_1124_);
if (v_isSharedCheck_1444_ == 0)
{
lean_object* v_unused_1445_; lean_object* v_unused_1446_; lean_object* v_unused_1447_; lean_object* v_unused_1448_; lean_object* v_unused_1449_; 
v_unused_1445_ = lean_ctor_get(v_r_1124_, 4);
lean_dec(v_unused_1445_);
v_unused_1446_ = lean_ctor_get(v_r_1124_, 3);
lean_dec(v_unused_1446_);
v_unused_1447_ = lean_ctor_get(v_r_1124_, 2);
lean_dec(v_unused_1447_);
v_unused_1448_ = lean_ctor_get(v_r_1124_, 1);
lean_dec(v_unused_1448_);
v_unused_1449_ = lean_ctor_get(v_r_1124_, 0);
lean_dec(v_unused_1449_);
v___x_1392_ = v_r_1124_;
v_isShared_1393_ = v_isSharedCheck_1444_;
goto v_resetjp_1391_;
}
else
{
lean_dec(v_r_1124_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1444_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
if (lean_obj_tag(v_l_1311_) == 0)
{
if (lean_obj_tag(v_r_1312_) == 0)
{
lean_object* v_k_1394_; lean_object* v_v_1395_; lean_object* v_size_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1400_; 
v_k_1394_ = lean_ctor_get(v___x_1318_, 0);
lean_inc(v_k_1394_);
v_v_1395_ = lean_ctor_get(v___x_1318_, 1);
lean_inc(v_v_1395_);
lean_dec_ref(v___x_1318_);
v_size_1396_ = lean_ctor_get(v_l_1311_, 0);
v___x_1397_ = lean_nat_add(v___x_1313_, v_size_1308_);
lean_dec(v_size_1308_);
v___x_1398_ = lean_nat_add(v___x_1313_, v_size_1396_);
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 4, v_l_1311_);
lean_ctor_set(v___x_1392_, 3, v_tree_1319_);
lean_ctor_set(v___x_1392_, 2, v_v_1395_);
lean_ctor_set(v___x_1392_, 1, v_k_1394_);
lean_ctor_set(v___x_1392_, 0, v___x_1398_);
v___x_1400_ = v___x_1392_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v___x_1398_);
lean_ctor_set(v_reuseFailAlloc_1404_, 1, v_k_1394_);
lean_ctor_set(v_reuseFailAlloc_1404_, 2, v_v_1395_);
lean_ctor_set(v_reuseFailAlloc_1404_, 3, v_tree_1319_);
lean_ctor_set(v_reuseFailAlloc_1404_, 4, v_l_1311_);
v___x_1400_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
lean_object* v___x_1402_; 
if (v_isShared_1317_ == 0)
{
lean_ctor_set(v___x_1316_, 4, v_r_1312_);
lean_ctor_set(v___x_1316_, 3, v___x_1400_);
lean_ctor_set(v___x_1316_, 2, v_v_1310_);
lean_ctor_set(v___x_1316_, 1, v_k_1309_);
lean_ctor_set(v___x_1316_, 0, v___x_1397_);
v___x_1402_ = v___x_1316_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v___x_1397_);
lean_ctor_set(v_reuseFailAlloc_1403_, 1, v_k_1309_);
lean_ctor_set(v_reuseFailAlloc_1403_, 2, v_v_1310_);
lean_ctor_set(v_reuseFailAlloc_1403_, 3, v___x_1400_);
lean_ctor_set(v_reuseFailAlloc_1403_, 4, v_r_1312_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
return v___x_1402_;
}
}
}
else
{
lean_object* v_k_1405_; lean_object* v_v_1406_; lean_object* v_k_1407_; lean_object* v_v_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1422_; 
lean_dec(v_size_1308_);
v_k_1405_ = lean_ctor_get(v___x_1318_, 0);
lean_inc(v_k_1405_);
v_v_1406_ = lean_ctor_get(v___x_1318_, 1);
lean_inc(v_v_1406_);
lean_dec_ref(v___x_1318_);
v_k_1407_ = lean_ctor_get(v_l_1311_, 1);
v_v_1408_ = lean_ctor_get(v_l_1311_, 2);
v_isSharedCheck_1422_ = !lean_is_exclusive(v_l_1311_);
if (v_isSharedCheck_1422_ == 0)
{
lean_object* v_unused_1423_; lean_object* v_unused_1424_; lean_object* v_unused_1425_; 
v_unused_1423_ = lean_ctor_get(v_l_1311_, 4);
lean_dec(v_unused_1423_);
v_unused_1424_ = lean_ctor_get(v_l_1311_, 3);
lean_dec(v_unused_1424_);
v_unused_1425_ = lean_ctor_get(v_l_1311_, 0);
lean_dec(v_unused_1425_);
v___x_1410_ = v_l_1311_;
v_isShared_1411_ = v_isSharedCheck_1422_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_v_1408_);
lean_inc(v_k_1407_);
lean_dec(v_l_1311_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1422_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1412_; lean_object* v___x_1414_; 
v___x_1412_ = lean_unsigned_to_nat(3u);
if (v_isShared_1411_ == 0)
{
lean_ctor_set(v___x_1410_, 4, v_r_1312_);
lean_ctor_set(v___x_1410_, 3, v_r_1312_);
lean_ctor_set(v___x_1410_, 2, v_v_1406_);
lean_ctor_set(v___x_1410_, 1, v_k_1405_);
lean_ctor_set(v___x_1410_, 0, v___x_1313_);
v___x_1414_ = v___x_1410_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v___x_1313_);
lean_ctor_set(v_reuseFailAlloc_1421_, 1, v_k_1405_);
lean_ctor_set(v_reuseFailAlloc_1421_, 2, v_v_1406_);
lean_ctor_set(v_reuseFailAlloc_1421_, 3, v_r_1312_);
lean_ctor_set(v_reuseFailAlloc_1421_, 4, v_r_1312_);
v___x_1414_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
lean_object* v___x_1416_; 
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 3, v_r_1312_);
lean_ctor_set(v___x_1392_, 0, v___x_1313_);
v___x_1416_ = v___x_1392_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v___x_1313_);
lean_ctor_set(v_reuseFailAlloc_1420_, 1, v_k_1309_);
lean_ctor_set(v_reuseFailAlloc_1420_, 2, v_v_1310_);
lean_ctor_set(v_reuseFailAlloc_1420_, 3, v_r_1312_);
lean_ctor_set(v_reuseFailAlloc_1420_, 4, v_r_1312_);
v___x_1416_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
lean_object* v___x_1418_; 
if (v_isShared_1317_ == 0)
{
lean_ctor_set(v___x_1316_, 4, v___x_1416_);
lean_ctor_set(v___x_1316_, 3, v___x_1414_);
lean_ctor_set(v___x_1316_, 2, v_v_1408_);
lean_ctor_set(v___x_1316_, 1, v_k_1407_);
lean_ctor_set(v___x_1316_, 0, v___x_1412_);
v___x_1418_ = v___x_1316_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v___x_1412_);
lean_ctor_set(v_reuseFailAlloc_1419_, 1, v_k_1407_);
lean_ctor_set(v_reuseFailAlloc_1419_, 2, v_v_1408_);
lean_ctor_set(v_reuseFailAlloc_1419_, 3, v___x_1414_);
lean_ctor_set(v_reuseFailAlloc_1419_, 4, v___x_1416_);
v___x_1418_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
return v___x_1418_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1312_) == 0)
{
lean_object* v_k_1426_; lean_object* v_v_1427_; lean_object* v___x_1428_; lean_object* v___x_1430_; 
lean_dec(v_size_1308_);
v_k_1426_ = lean_ctor_get(v___x_1318_, 0);
lean_inc(v_k_1426_);
v_v_1427_ = lean_ctor_get(v___x_1318_, 1);
lean_inc(v_v_1427_);
lean_dec_ref(v___x_1318_);
v___x_1428_ = lean_unsigned_to_nat(3u);
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 4, v_l_1311_);
lean_ctor_set(v___x_1392_, 2, v_v_1427_);
lean_ctor_set(v___x_1392_, 1, v_k_1426_);
lean_ctor_set(v___x_1392_, 0, v___x_1313_);
v___x_1430_ = v___x_1392_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v___x_1313_);
lean_ctor_set(v_reuseFailAlloc_1434_, 1, v_k_1426_);
lean_ctor_set(v_reuseFailAlloc_1434_, 2, v_v_1427_);
lean_ctor_set(v_reuseFailAlloc_1434_, 3, v_l_1311_);
lean_ctor_set(v_reuseFailAlloc_1434_, 4, v_l_1311_);
v___x_1430_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
lean_object* v___x_1432_; 
if (v_isShared_1317_ == 0)
{
lean_ctor_set(v___x_1316_, 4, v_r_1312_);
lean_ctor_set(v___x_1316_, 3, v___x_1430_);
lean_ctor_set(v___x_1316_, 2, v_v_1310_);
lean_ctor_set(v___x_1316_, 1, v_k_1309_);
lean_ctor_set(v___x_1316_, 0, v___x_1428_);
v___x_1432_ = v___x_1316_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v___x_1428_);
lean_ctor_set(v_reuseFailAlloc_1433_, 1, v_k_1309_);
lean_ctor_set(v_reuseFailAlloc_1433_, 2, v_v_1310_);
lean_ctor_set(v_reuseFailAlloc_1433_, 3, v___x_1430_);
lean_ctor_set(v_reuseFailAlloc_1433_, 4, v_r_1312_);
v___x_1432_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
return v___x_1432_;
}
}
}
else
{
lean_object* v_k_1435_; lean_object* v_v_1436_; lean_object* v___x_1438_; 
v_k_1435_ = lean_ctor_get(v___x_1318_, 0);
lean_inc(v_k_1435_);
v_v_1436_ = lean_ctor_get(v___x_1318_, 1);
lean_inc(v_v_1436_);
lean_dec_ref(v___x_1318_);
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 3, v_r_1312_);
v___x_1438_ = v___x_1392_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v_size_1308_);
lean_ctor_set(v_reuseFailAlloc_1443_, 1, v_k_1309_);
lean_ctor_set(v_reuseFailAlloc_1443_, 2, v_v_1310_);
lean_ctor_set(v_reuseFailAlloc_1443_, 3, v_r_1312_);
lean_ctor_set(v_reuseFailAlloc_1443_, 4, v_r_1312_);
v___x_1438_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
lean_object* v___x_1439_; lean_object* v___x_1441_; 
v___x_1439_ = lean_unsigned_to_nat(2u);
if (v_isShared_1317_ == 0)
{
lean_ctor_set(v___x_1316_, 4, v___x_1438_);
lean_ctor_set(v___x_1316_, 3, v_r_1312_);
lean_ctor_set(v___x_1316_, 2, v_v_1436_);
lean_ctor_set(v___x_1316_, 1, v_k_1435_);
lean_ctor_set(v___x_1316_, 0, v___x_1439_);
v___x_1441_ = v___x_1316_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v___x_1439_);
lean_ctor_set(v_reuseFailAlloc_1442_, 1, v_k_1435_);
lean_ctor_set(v_reuseFailAlloc_1442_, 2, v_v_1436_);
lean_ctor_set(v_reuseFailAlloc_1442_, 3, v_r_1312_);
lean_ctor_set(v_reuseFailAlloc_1442_, 4, v___x_1438_);
v___x_1441_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
return v___x_1441_;
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
lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1608_; 
lean_inc(v_r_1312_);
lean_inc(v_v_1310_);
lean_inc(v_k_1309_);
v_isSharedCheck_1608_ = !lean_is_exclusive(v_r_1124_);
if (v_isSharedCheck_1608_ == 0)
{
lean_object* v_unused_1609_; lean_object* v_unused_1610_; lean_object* v_unused_1611_; lean_object* v_unused_1612_; lean_object* v_unused_1613_; 
v_unused_1609_ = lean_ctor_get(v_r_1124_, 4);
lean_dec(v_unused_1609_);
v_unused_1610_ = lean_ctor_get(v_r_1124_, 3);
lean_dec(v_unused_1610_);
v_unused_1611_ = lean_ctor_get(v_r_1124_, 2);
lean_dec(v_unused_1611_);
v_unused_1612_ = lean_ctor_get(v_r_1124_, 1);
lean_dec(v_unused_1612_);
v_unused_1613_ = lean_ctor_get(v_r_1124_, 0);
lean_dec(v_unused_1613_);
v___x_1457_ = v_r_1124_;
v_isShared_1458_ = v_isSharedCheck_1608_;
goto v_resetjp_1456_;
}
else
{
lean_dec(v_r_1124_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1608_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
lean_object* v___x_1459_; lean_object* v_tree_1460_; 
v___x_1459_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_1309_, v_v_1310_, v_l_1311_, v_r_1312_);
v_tree_1460_ = lean_ctor_get(v___x_1459_, 2);
lean_inc(v_tree_1460_);
if (lean_obj_tag(v_tree_1460_) == 0)
{
lean_object* v_k_1461_; lean_object* v_v_1462_; lean_object* v_size_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; uint8_t v___x_1466_; 
v_k_1461_ = lean_ctor_get(v___x_1459_, 0);
lean_inc(v_k_1461_);
v_v_1462_ = lean_ctor_get(v___x_1459_, 1);
lean_inc(v_v_1462_);
lean_dec_ref(v___x_1459_);
v_size_1463_ = lean_ctor_get(v_tree_1460_, 0);
v___x_1464_ = lean_unsigned_to_nat(3u);
v___x_1465_ = lean_nat_mul(v___x_1464_, v_size_1463_);
v___x_1466_ = lean_nat_dec_lt(v___x_1465_, v_size_1303_);
lean_dec(v___x_1465_);
if (v___x_1466_ == 0)
{
lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1470_; 
lean_dec(v_r_1307_);
v___x_1467_ = lean_nat_add(v___x_1313_, v_size_1303_);
v___x_1468_ = lean_nat_add(v___x_1467_, v_size_1463_);
lean_dec(v___x_1467_);
if (v_isShared_1458_ == 0)
{
lean_ctor_set(v___x_1457_, 4, v_tree_1460_);
lean_ctor_set(v___x_1457_, 3, v_l_1123_);
lean_ctor_set(v___x_1457_, 2, v_v_1462_);
lean_ctor_set(v___x_1457_, 1, v_k_1461_);
lean_ctor_set(v___x_1457_, 0, v___x_1468_);
v___x_1470_ = v___x_1457_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v___x_1468_);
lean_ctor_set(v_reuseFailAlloc_1471_, 1, v_k_1461_);
lean_ctor_set(v_reuseFailAlloc_1471_, 2, v_v_1462_);
lean_ctor_set(v_reuseFailAlloc_1471_, 3, v_l_1123_);
lean_ctor_set(v_reuseFailAlloc_1471_, 4, v_tree_1460_);
v___x_1470_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
return v___x_1470_;
}
}
else
{
lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1537_; 
lean_inc(v_l_1306_);
lean_inc(v_v_1305_);
lean_inc(v_k_1304_);
lean_inc(v_size_1303_);
v_isSharedCheck_1537_ = !lean_is_exclusive(v_l_1123_);
if (v_isSharedCheck_1537_ == 0)
{
lean_object* v_unused_1538_; lean_object* v_unused_1539_; lean_object* v_unused_1540_; lean_object* v_unused_1541_; lean_object* v_unused_1542_; 
v_unused_1538_ = lean_ctor_get(v_l_1123_, 4);
lean_dec(v_unused_1538_);
v_unused_1539_ = lean_ctor_get(v_l_1123_, 3);
lean_dec(v_unused_1539_);
v_unused_1540_ = lean_ctor_get(v_l_1123_, 2);
lean_dec(v_unused_1540_);
v_unused_1541_ = lean_ctor_get(v_l_1123_, 1);
lean_dec(v_unused_1541_);
v_unused_1542_ = lean_ctor_get(v_l_1123_, 0);
lean_dec(v_unused_1542_);
v___x_1473_ = v_l_1123_;
v_isShared_1474_ = v_isSharedCheck_1537_;
goto v_resetjp_1472_;
}
else
{
lean_dec(v_l_1123_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1537_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v_size_1475_; lean_object* v_size_1476_; lean_object* v_k_1477_; lean_object* v_v_1478_; lean_object* v_l_1479_; lean_object* v_r_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; uint8_t v___x_1483_; 
v_size_1475_ = lean_ctor_get(v_l_1306_, 0);
v_size_1476_ = lean_ctor_get(v_r_1307_, 0);
v_k_1477_ = lean_ctor_get(v_r_1307_, 1);
v_v_1478_ = lean_ctor_get(v_r_1307_, 2);
v_l_1479_ = lean_ctor_get(v_r_1307_, 3);
v_r_1480_ = lean_ctor_get(v_r_1307_, 4);
v___x_1481_ = lean_unsigned_to_nat(2u);
v___x_1482_ = lean_nat_mul(v___x_1481_, v_size_1475_);
v___x_1483_ = lean_nat_dec_lt(v_size_1476_, v___x_1482_);
lean_dec(v___x_1482_);
if (v___x_1483_ == 0)
{
lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1521_; 
lean_inc(v_r_1480_);
lean_inc(v_l_1479_);
lean_inc(v_v_1478_);
lean_inc(v_k_1477_);
lean_del_object(v___x_1473_);
v_isSharedCheck_1521_ = !lean_is_exclusive(v_r_1307_);
if (v_isSharedCheck_1521_ == 0)
{
lean_object* v_unused_1522_; lean_object* v_unused_1523_; lean_object* v_unused_1524_; lean_object* v_unused_1525_; lean_object* v_unused_1526_; 
v_unused_1522_ = lean_ctor_get(v_r_1307_, 4);
lean_dec(v_unused_1522_);
v_unused_1523_ = lean_ctor_get(v_r_1307_, 3);
lean_dec(v_unused_1523_);
v_unused_1524_ = lean_ctor_get(v_r_1307_, 2);
lean_dec(v_unused_1524_);
v_unused_1525_ = lean_ctor_get(v_r_1307_, 1);
lean_dec(v_unused_1525_);
v_unused_1526_ = lean_ctor_get(v_r_1307_, 0);
lean_dec(v_unused_1526_);
v___x_1485_ = v_r_1307_;
v_isShared_1486_ = v_isSharedCheck_1521_;
goto v_resetjp_1484_;
}
else
{
lean_dec(v_r_1307_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1521_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___y_1490_; lean_object* v___y_1491_; lean_object* v___y_1492_; lean_object* v___x_1509_; lean_object* v___y_1511_; 
v___x_1487_ = lean_nat_add(v___x_1313_, v_size_1303_);
lean_dec(v_size_1303_);
v___x_1488_ = lean_nat_add(v___x_1487_, v_size_1463_);
lean_dec(v___x_1487_);
v___x_1509_ = lean_nat_add(v___x_1313_, v_size_1475_);
if (lean_obj_tag(v_l_1479_) == 0)
{
lean_object* v_size_1519_; 
v_size_1519_ = lean_ctor_get(v_l_1479_, 0);
lean_inc(v_size_1519_);
v___y_1511_ = v_size_1519_;
goto v___jp_1510_;
}
else
{
lean_object* v___x_1520_; 
v___x_1520_ = lean_unsigned_to_nat(0u);
v___y_1511_ = v___x_1520_;
goto v___jp_1510_;
}
v___jp_1489_:
{
lean_object* v___x_1493_; lean_object* v___x_1495_; 
v___x_1493_ = lean_nat_add(v___y_1491_, v___y_1492_);
lean_dec(v___y_1492_);
lean_dec(v___y_1491_);
lean_inc_ref(v_tree_1460_);
if (v_isShared_1486_ == 0)
{
lean_ctor_set(v___x_1485_, 4, v_tree_1460_);
lean_ctor_set(v___x_1485_, 3, v_r_1480_);
lean_ctor_set(v___x_1485_, 2, v_v_1462_);
lean_ctor_set(v___x_1485_, 1, v_k_1461_);
lean_ctor_set(v___x_1485_, 0, v___x_1493_);
v___x_1495_ = v___x_1485_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v___x_1493_);
lean_ctor_set(v_reuseFailAlloc_1508_, 1, v_k_1461_);
lean_ctor_set(v_reuseFailAlloc_1508_, 2, v_v_1462_);
lean_ctor_set(v_reuseFailAlloc_1508_, 3, v_r_1480_);
lean_ctor_set(v_reuseFailAlloc_1508_, 4, v_tree_1460_);
v___x_1495_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1502_; 
v_isSharedCheck_1502_ = !lean_is_exclusive(v_tree_1460_);
if (v_isSharedCheck_1502_ == 0)
{
lean_object* v_unused_1503_; lean_object* v_unused_1504_; lean_object* v_unused_1505_; lean_object* v_unused_1506_; lean_object* v_unused_1507_; 
v_unused_1503_ = lean_ctor_get(v_tree_1460_, 4);
lean_dec(v_unused_1503_);
v_unused_1504_ = lean_ctor_get(v_tree_1460_, 3);
lean_dec(v_unused_1504_);
v_unused_1505_ = lean_ctor_get(v_tree_1460_, 2);
lean_dec(v_unused_1505_);
v_unused_1506_ = lean_ctor_get(v_tree_1460_, 1);
lean_dec(v_unused_1506_);
v_unused_1507_ = lean_ctor_get(v_tree_1460_, 0);
lean_dec(v_unused_1507_);
v___x_1497_ = v_tree_1460_;
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
else
{
lean_dec(v_tree_1460_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v___x_1500_; 
if (v_isShared_1498_ == 0)
{
lean_ctor_set(v___x_1497_, 4, v___x_1495_);
lean_ctor_set(v___x_1497_, 3, v___y_1490_);
lean_ctor_set(v___x_1497_, 2, v_v_1478_);
lean_ctor_set(v___x_1497_, 1, v_k_1477_);
lean_ctor_set(v___x_1497_, 0, v___x_1488_);
v___x_1500_ = v___x_1497_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v___x_1488_);
lean_ctor_set(v_reuseFailAlloc_1501_, 1, v_k_1477_);
lean_ctor_set(v_reuseFailAlloc_1501_, 2, v_v_1478_);
lean_ctor_set(v_reuseFailAlloc_1501_, 3, v___y_1490_);
lean_ctor_set(v_reuseFailAlloc_1501_, 4, v___x_1495_);
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
v___jp_1510_:
{
lean_object* v___x_1512_; lean_object* v___x_1514_; 
v___x_1512_ = lean_nat_add(v___x_1509_, v___y_1511_);
lean_dec(v___y_1511_);
lean_dec(v___x_1509_);
if (v_isShared_1458_ == 0)
{
lean_ctor_set(v___x_1457_, 4, v_l_1479_);
lean_ctor_set(v___x_1457_, 3, v_l_1306_);
lean_ctor_set(v___x_1457_, 2, v_v_1305_);
lean_ctor_set(v___x_1457_, 1, v_k_1304_);
lean_ctor_set(v___x_1457_, 0, v___x_1512_);
v___x_1514_ = v___x_1457_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v___x_1512_);
lean_ctor_set(v_reuseFailAlloc_1518_, 1, v_k_1304_);
lean_ctor_set(v_reuseFailAlloc_1518_, 2, v_v_1305_);
lean_ctor_set(v_reuseFailAlloc_1518_, 3, v_l_1306_);
lean_ctor_set(v_reuseFailAlloc_1518_, 4, v_l_1479_);
v___x_1514_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
lean_object* v___x_1515_; 
v___x_1515_ = lean_nat_add(v___x_1313_, v_size_1463_);
if (lean_obj_tag(v_r_1480_) == 0)
{
lean_object* v_size_1516_; 
v_size_1516_ = lean_ctor_get(v_r_1480_, 0);
lean_inc(v_size_1516_);
v___y_1490_ = v___x_1514_;
v___y_1491_ = v___x_1515_;
v___y_1492_ = v_size_1516_;
goto v___jp_1489_;
}
else
{
lean_object* v___x_1517_; 
v___x_1517_ = lean_unsigned_to_nat(0u);
v___y_1490_ = v___x_1514_;
v___y_1491_ = v___x_1515_;
v___y_1492_ = v___x_1517_;
goto v___jp_1489_;
}
}
}
}
}
else
{
lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1532_; 
v___x_1527_ = lean_nat_add(v___x_1313_, v_size_1303_);
lean_dec(v_size_1303_);
v___x_1528_ = lean_nat_add(v___x_1527_, v_size_1463_);
lean_dec(v___x_1527_);
v___x_1529_ = lean_nat_add(v___x_1313_, v_size_1463_);
v___x_1530_ = lean_nat_add(v___x_1529_, v_size_1476_);
lean_dec(v___x_1529_);
if (v_isShared_1458_ == 0)
{
lean_ctor_set(v___x_1457_, 4, v_tree_1460_);
lean_ctor_set(v___x_1457_, 3, v_r_1307_);
lean_ctor_set(v___x_1457_, 2, v_v_1462_);
lean_ctor_set(v___x_1457_, 1, v_k_1461_);
lean_ctor_set(v___x_1457_, 0, v___x_1530_);
v___x_1532_ = v___x_1457_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v___x_1530_);
lean_ctor_set(v_reuseFailAlloc_1536_, 1, v_k_1461_);
lean_ctor_set(v_reuseFailAlloc_1536_, 2, v_v_1462_);
lean_ctor_set(v_reuseFailAlloc_1536_, 3, v_r_1307_);
lean_ctor_set(v_reuseFailAlloc_1536_, 4, v_tree_1460_);
v___x_1532_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
lean_object* v___x_1534_; 
if (v_isShared_1474_ == 0)
{
lean_ctor_set(v___x_1473_, 4, v___x_1532_);
lean_ctor_set(v___x_1473_, 0, v___x_1528_);
v___x_1534_ = v___x_1473_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v___x_1528_);
lean_ctor_set(v_reuseFailAlloc_1535_, 1, v_k_1304_);
lean_ctor_set(v_reuseFailAlloc_1535_, 2, v_v_1305_);
lean_ctor_set(v_reuseFailAlloc_1535_, 3, v_l_1306_);
lean_ctor_set(v_reuseFailAlloc_1535_, 4, v___x_1532_);
v___x_1534_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
return v___x_1534_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_1306_) == 0)
{
lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1566_; 
lean_inc_ref(v_l_1306_);
lean_inc(v_v_1305_);
lean_inc(v_k_1304_);
lean_inc(v_size_1303_);
v_isSharedCheck_1566_ = !lean_is_exclusive(v_l_1123_);
if (v_isSharedCheck_1566_ == 0)
{
lean_object* v_unused_1567_; lean_object* v_unused_1568_; lean_object* v_unused_1569_; lean_object* v_unused_1570_; lean_object* v_unused_1571_; 
v_unused_1567_ = lean_ctor_get(v_l_1123_, 4);
lean_dec(v_unused_1567_);
v_unused_1568_ = lean_ctor_get(v_l_1123_, 3);
lean_dec(v_unused_1568_);
v_unused_1569_ = lean_ctor_get(v_l_1123_, 2);
lean_dec(v_unused_1569_);
v_unused_1570_ = lean_ctor_get(v_l_1123_, 1);
lean_dec(v_unused_1570_);
v_unused_1571_ = lean_ctor_get(v_l_1123_, 0);
lean_dec(v_unused_1571_);
v___x_1544_ = v_l_1123_;
v_isShared_1545_ = v_isSharedCheck_1566_;
goto v_resetjp_1543_;
}
else
{
lean_dec(v_l_1123_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1566_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
if (lean_obj_tag(v_r_1307_) == 0)
{
lean_object* v_k_1546_; lean_object* v_v_1547_; lean_object* v_size_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1552_; 
v_k_1546_ = lean_ctor_get(v___x_1459_, 0);
lean_inc(v_k_1546_);
v_v_1547_ = lean_ctor_get(v___x_1459_, 1);
lean_inc(v_v_1547_);
lean_dec_ref(v___x_1459_);
v_size_1548_ = lean_ctor_get(v_r_1307_, 0);
v___x_1549_ = lean_nat_add(v___x_1313_, v_size_1303_);
lean_dec(v_size_1303_);
v___x_1550_ = lean_nat_add(v___x_1313_, v_size_1548_);
if (v_isShared_1458_ == 0)
{
lean_ctor_set(v___x_1457_, 4, v_tree_1460_);
lean_ctor_set(v___x_1457_, 3, v_r_1307_);
lean_ctor_set(v___x_1457_, 2, v_v_1547_);
lean_ctor_set(v___x_1457_, 1, v_k_1546_);
lean_ctor_set(v___x_1457_, 0, v___x_1550_);
v___x_1552_ = v___x_1457_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v___x_1550_);
lean_ctor_set(v_reuseFailAlloc_1556_, 1, v_k_1546_);
lean_ctor_set(v_reuseFailAlloc_1556_, 2, v_v_1547_);
lean_ctor_set(v_reuseFailAlloc_1556_, 3, v_r_1307_);
lean_ctor_set(v_reuseFailAlloc_1556_, 4, v_tree_1460_);
v___x_1552_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
lean_object* v___x_1554_; 
if (v_isShared_1545_ == 0)
{
lean_ctor_set(v___x_1544_, 4, v___x_1552_);
lean_ctor_set(v___x_1544_, 0, v___x_1549_);
v___x_1554_ = v___x_1544_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v___x_1549_);
lean_ctor_set(v_reuseFailAlloc_1555_, 1, v_k_1304_);
lean_ctor_set(v_reuseFailAlloc_1555_, 2, v_v_1305_);
lean_ctor_set(v_reuseFailAlloc_1555_, 3, v_l_1306_);
lean_ctor_set(v_reuseFailAlloc_1555_, 4, v___x_1552_);
v___x_1554_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
return v___x_1554_;
}
}
}
else
{
lean_object* v_k_1557_; lean_object* v_v_1558_; lean_object* v___x_1559_; lean_object* v___x_1561_; 
lean_dec(v_size_1303_);
v_k_1557_ = lean_ctor_get(v___x_1459_, 0);
lean_inc(v_k_1557_);
v_v_1558_ = lean_ctor_get(v___x_1459_, 1);
lean_inc(v_v_1558_);
lean_dec_ref(v___x_1459_);
v___x_1559_ = lean_unsigned_to_nat(3u);
if (v_isShared_1458_ == 0)
{
lean_ctor_set(v___x_1457_, 4, v_r_1307_);
lean_ctor_set(v___x_1457_, 3, v_r_1307_);
lean_ctor_set(v___x_1457_, 2, v_v_1558_);
lean_ctor_set(v___x_1457_, 1, v_k_1557_);
lean_ctor_set(v___x_1457_, 0, v___x_1313_);
v___x_1561_ = v___x_1457_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v___x_1313_);
lean_ctor_set(v_reuseFailAlloc_1565_, 1, v_k_1557_);
lean_ctor_set(v_reuseFailAlloc_1565_, 2, v_v_1558_);
lean_ctor_set(v_reuseFailAlloc_1565_, 3, v_r_1307_);
lean_ctor_set(v_reuseFailAlloc_1565_, 4, v_r_1307_);
v___x_1561_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
lean_object* v___x_1563_; 
if (v_isShared_1545_ == 0)
{
lean_ctor_set(v___x_1544_, 4, v___x_1561_);
lean_ctor_set(v___x_1544_, 0, v___x_1559_);
v___x_1563_ = v___x_1544_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v___x_1559_);
lean_ctor_set(v_reuseFailAlloc_1564_, 1, v_k_1304_);
lean_ctor_set(v_reuseFailAlloc_1564_, 2, v_v_1305_);
lean_ctor_set(v_reuseFailAlloc_1564_, 3, v_l_1306_);
lean_ctor_set(v_reuseFailAlloc_1564_, 4, v___x_1561_);
v___x_1563_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
return v___x_1563_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1307_) == 0)
{
lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1596_; 
lean_inc(v_l_1306_);
lean_inc(v_v_1305_);
lean_inc(v_k_1304_);
v_isSharedCheck_1596_ = !lean_is_exclusive(v_l_1123_);
if (v_isSharedCheck_1596_ == 0)
{
lean_object* v_unused_1597_; lean_object* v_unused_1598_; lean_object* v_unused_1599_; lean_object* v_unused_1600_; lean_object* v_unused_1601_; 
v_unused_1597_ = lean_ctor_get(v_l_1123_, 4);
lean_dec(v_unused_1597_);
v_unused_1598_ = lean_ctor_get(v_l_1123_, 3);
lean_dec(v_unused_1598_);
v_unused_1599_ = lean_ctor_get(v_l_1123_, 2);
lean_dec(v_unused_1599_);
v_unused_1600_ = lean_ctor_get(v_l_1123_, 1);
lean_dec(v_unused_1600_);
v_unused_1601_ = lean_ctor_get(v_l_1123_, 0);
lean_dec(v_unused_1601_);
v___x_1573_ = v_l_1123_;
v_isShared_1574_ = v_isSharedCheck_1596_;
goto v_resetjp_1572_;
}
else
{
lean_dec(v_l_1123_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1596_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v_k_1575_; lean_object* v_v_1576_; lean_object* v_k_1577_; lean_object* v_v_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1592_; 
v_k_1575_ = lean_ctor_get(v___x_1459_, 0);
lean_inc(v_k_1575_);
v_v_1576_ = lean_ctor_get(v___x_1459_, 1);
lean_inc(v_v_1576_);
lean_dec_ref(v___x_1459_);
v_k_1577_ = lean_ctor_get(v_r_1307_, 1);
v_v_1578_ = lean_ctor_get(v_r_1307_, 2);
v_isSharedCheck_1592_ = !lean_is_exclusive(v_r_1307_);
if (v_isSharedCheck_1592_ == 0)
{
lean_object* v_unused_1593_; lean_object* v_unused_1594_; lean_object* v_unused_1595_; 
v_unused_1593_ = lean_ctor_get(v_r_1307_, 4);
lean_dec(v_unused_1593_);
v_unused_1594_ = lean_ctor_get(v_r_1307_, 3);
lean_dec(v_unused_1594_);
v_unused_1595_ = lean_ctor_get(v_r_1307_, 0);
lean_dec(v_unused_1595_);
v___x_1580_ = v_r_1307_;
v_isShared_1581_ = v_isSharedCheck_1592_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_v_1578_);
lean_inc(v_k_1577_);
lean_dec(v_r_1307_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1592_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
lean_object* v___x_1582_; lean_object* v___x_1584_; 
v___x_1582_ = lean_unsigned_to_nat(3u);
if (v_isShared_1581_ == 0)
{
lean_ctor_set(v___x_1580_, 4, v_l_1306_);
lean_ctor_set(v___x_1580_, 3, v_l_1306_);
lean_ctor_set(v___x_1580_, 2, v_v_1305_);
lean_ctor_set(v___x_1580_, 1, v_k_1304_);
lean_ctor_set(v___x_1580_, 0, v___x_1313_);
v___x_1584_ = v___x_1580_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v___x_1313_);
lean_ctor_set(v_reuseFailAlloc_1591_, 1, v_k_1304_);
lean_ctor_set(v_reuseFailAlloc_1591_, 2, v_v_1305_);
lean_ctor_set(v_reuseFailAlloc_1591_, 3, v_l_1306_);
lean_ctor_set(v_reuseFailAlloc_1591_, 4, v_l_1306_);
v___x_1584_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
lean_object* v___x_1586_; 
if (v_isShared_1458_ == 0)
{
lean_ctor_set(v___x_1457_, 4, v_l_1306_);
lean_ctor_set(v___x_1457_, 3, v_l_1306_);
lean_ctor_set(v___x_1457_, 2, v_v_1576_);
lean_ctor_set(v___x_1457_, 1, v_k_1575_);
lean_ctor_set(v___x_1457_, 0, v___x_1313_);
v___x_1586_ = v___x_1457_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v___x_1313_);
lean_ctor_set(v_reuseFailAlloc_1590_, 1, v_k_1575_);
lean_ctor_set(v_reuseFailAlloc_1590_, 2, v_v_1576_);
lean_ctor_set(v_reuseFailAlloc_1590_, 3, v_l_1306_);
lean_ctor_set(v_reuseFailAlloc_1590_, 4, v_l_1306_);
v___x_1586_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
lean_object* v___x_1588_; 
if (v_isShared_1574_ == 0)
{
lean_ctor_set(v___x_1573_, 4, v___x_1586_);
lean_ctor_set(v___x_1573_, 3, v___x_1584_);
lean_ctor_set(v___x_1573_, 2, v_v_1578_);
lean_ctor_set(v___x_1573_, 1, v_k_1577_);
lean_ctor_set(v___x_1573_, 0, v___x_1582_);
v___x_1588_ = v___x_1573_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v___x_1582_);
lean_ctor_set(v_reuseFailAlloc_1589_, 1, v_k_1577_);
lean_ctor_set(v_reuseFailAlloc_1589_, 2, v_v_1578_);
lean_ctor_set(v_reuseFailAlloc_1589_, 3, v___x_1584_);
lean_ctor_set(v_reuseFailAlloc_1589_, 4, v___x_1586_);
v___x_1588_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
return v___x_1588_;
}
}
}
}
}
}
else
{
lean_object* v_k_1602_; lean_object* v_v_1603_; lean_object* v___x_1604_; lean_object* v___x_1606_; 
v_k_1602_ = lean_ctor_get(v___x_1459_, 0);
lean_inc(v_k_1602_);
v_v_1603_ = lean_ctor_get(v___x_1459_, 1);
lean_inc(v_v_1603_);
lean_dec_ref(v___x_1459_);
v___x_1604_ = lean_unsigned_to_nat(2u);
if (v_isShared_1458_ == 0)
{
lean_ctor_set(v___x_1457_, 4, v_r_1307_);
lean_ctor_set(v___x_1457_, 3, v_l_1123_);
lean_ctor_set(v___x_1457_, 2, v_v_1603_);
lean_ctor_set(v___x_1457_, 1, v_k_1602_);
lean_ctor_set(v___x_1457_, 0, v___x_1604_);
v___x_1606_ = v___x_1457_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v___x_1604_);
lean_ctor_set(v_reuseFailAlloc_1607_, 1, v_k_1602_);
lean_ctor_set(v_reuseFailAlloc_1607_, 2, v_v_1603_);
lean_ctor_set(v_reuseFailAlloc_1607_, 3, v_l_1123_);
lean_ctor_set(v_reuseFailAlloc_1607_, 4, v_r_1307_);
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
}
}
else
{
return v_l_1123_;
}
}
else
{
return v_r_1124_;
}
}
default: 
{
lean_object* v_impl_1614_; lean_object* v___x_1615_; 
v_impl_1614_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_k_1119_, v_r_1124_);
v___x_1615_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1614_) == 0)
{
if (lean_obj_tag(v_l_1123_) == 0)
{
lean_object* v_size_1616_; lean_object* v_size_1617_; lean_object* v_k_1618_; lean_object* v_v_1619_; lean_object* v_l_1620_; lean_object* v_r_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; uint8_t v___x_1624_; 
v_size_1616_ = lean_ctor_get(v_impl_1614_, 0);
lean_inc(v_size_1616_);
v_size_1617_ = lean_ctor_get(v_l_1123_, 0);
v_k_1618_ = lean_ctor_get(v_l_1123_, 1);
v_v_1619_ = lean_ctor_get(v_l_1123_, 2);
v_l_1620_ = lean_ctor_get(v_l_1123_, 3);
v_r_1621_ = lean_ctor_get(v_l_1123_, 4);
lean_inc(v_r_1621_);
v___x_1622_ = lean_unsigned_to_nat(3u);
v___x_1623_ = lean_nat_mul(v___x_1622_, v_size_1616_);
v___x_1624_ = lean_nat_dec_lt(v___x_1623_, v_size_1617_);
lean_dec(v___x_1623_);
if (v___x_1624_ == 0)
{
lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1628_; 
lean_dec(v_r_1621_);
v___x_1625_ = lean_nat_add(v___x_1615_, v_size_1617_);
v___x_1626_ = lean_nat_add(v___x_1625_, v_size_1616_);
lean_dec(v_size_1616_);
lean_dec(v___x_1625_);
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 4, v_impl_1614_);
lean_ctor_set(v___x_1126_, 0, v___x_1626_);
v___x_1628_ = v___x_1126_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v___x_1626_);
lean_ctor_set(v_reuseFailAlloc_1629_, 1, v_k_1121_);
lean_ctor_set(v_reuseFailAlloc_1629_, 2, v_v_1122_);
lean_ctor_set(v_reuseFailAlloc_1629_, 3, v_l_1123_);
lean_ctor_set(v_reuseFailAlloc_1629_, 4, v_impl_1614_);
v___x_1628_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
return v___x_1628_;
}
}
else
{
lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1695_; 
lean_inc(v_l_1620_);
lean_inc(v_v_1619_);
lean_inc(v_k_1618_);
lean_inc(v_size_1617_);
v_isSharedCheck_1695_ = !lean_is_exclusive(v_l_1123_);
if (v_isSharedCheck_1695_ == 0)
{
lean_object* v_unused_1696_; lean_object* v_unused_1697_; lean_object* v_unused_1698_; lean_object* v_unused_1699_; lean_object* v_unused_1700_; 
v_unused_1696_ = lean_ctor_get(v_l_1123_, 4);
lean_dec(v_unused_1696_);
v_unused_1697_ = lean_ctor_get(v_l_1123_, 3);
lean_dec(v_unused_1697_);
v_unused_1698_ = lean_ctor_get(v_l_1123_, 2);
lean_dec(v_unused_1698_);
v_unused_1699_ = lean_ctor_get(v_l_1123_, 1);
lean_dec(v_unused_1699_);
v_unused_1700_ = lean_ctor_get(v_l_1123_, 0);
lean_dec(v_unused_1700_);
v___x_1631_ = v_l_1123_;
v_isShared_1632_ = v_isSharedCheck_1695_;
goto v_resetjp_1630_;
}
else
{
lean_dec(v_l_1123_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1695_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v_size_1633_; lean_object* v_size_1634_; lean_object* v_k_1635_; lean_object* v_v_1636_; lean_object* v_l_1637_; lean_object* v_r_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; uint8_t v___x_1641_; 
v_size_1633_ = lean_ctor_get(v_l_1620_, 0);
v_size_1634_ = lean_ctor_get(v_r_1621_, 0);
v_k_1635_ = lean_ctor_get(v_r_1621_, 1);
v_v_1636_ = lean_ctor_get(v_r_1621_, 2);
v_l_1637_ = lean_ctor_get(v_r_1621_, 3);
v_r_1638_ = lean_ctor_get(v_r_1621_, 4);
v___x_1639_ = lean_unsigned_to_nat(2u);
v___x_1640_ = lean_nat_mul(v___x_1639_, v_size_1633_);
v___x_1641_ = lean_nat_dec_lt(v_size_1634_, v___x_1640_);
lean_dec(v___x_1640_);
if (v___x_1641_ == 0)
{
lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1670_; 
lean_inc(v_r_1638_);
lean_inc(v_l_1637_);
lean_inc(v_v_1636_);
lean_inc(v_k_1635_);
v_isSharedCheck_1670_ = !lean_is_exclusive(v_r_1621_);
if (v_isSharedCheck_1670_ == 0)
{
lean_object* v_unused_1671_; lean_object* v_unused_1672_; lean_object* v_unused_1673_; lean_object* v_unused_1674_; lean_object* v_unused_1675_; 
v_unused_1671_ = lean_ctor_get(v_r_1621_, 4);
lean_dec(v_unused_1671_);
v_unused_1672_ = lean_ctor_get(v_r_1621_, 3);
lean_dec(v_unused_1672_);
v_unused_1673_ = lean_ctor_get(v_r_1621_, 2);
lean_dec(v_unused_1673_);
v_unused_1674_ = lean_ctor_get(v_r_1621_, 1);
lean_dec(v_unused_1674_);
v_unused_1675_ = lean_ctor_get(v_r_1621_, 0);
lean_dec(v_unused_1675_);
v___x_1643_ = v_r_1621_;
v_isShared_1644_ = v_isSharedCheck_1670_;
goto v_resetjp_1642_;
}
else
{
lean_dec(v_r_1621_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1670_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___y_1648_; lean_object* v___y_1649_; lean_object* v___y_1650_; lean_object* v___x_1658_; lean_object* v___y_1660_; 
v___x_1645_ = lean_nat_add(v___x_1615_, v_size_1617_);
lean_dec(v_size_1617_);
v___x_1646_ = lean_nat_add(v___x_1645_, v_size_1616_);
lean_dec(v___x_1645_);
v___x_1658_ = lean_nat_add(v___x_1615_, v_size_1633_);
if (lean_obj_tag(v_l_1637_) == 0)
{
lean_object* v_size_1668_; 
v_size_1668_ = lean_ctor_get(v_l_1637_, 0);
lean_inc(v_size_1668_);
v___y_1660_ = v_size_1668_;
goto v___jp_1659_;
}
else
{
lean_object* v___x_1669_; 
v___x_1669_ = lean_unsigned_to_nat(0u);
v___y_1660_ = v___x_1669_;
goto v___jp_1659_;
}
v___jp_1647_:
{
lean_object* v___x_1651_; lean_object* v___x_1653_; 
v___x_1651_ = lean_nat_add(v___y_1649_, v___y_1650_);
lean_dec(v___y_1650_);
lean_dec(v___y_1649_);
if (v_isShared_1644_ == 0)
{
lean_ctor_set(v___x_1643_, 4, v_impl_1614_);
lean_ctor_set(v___x_1643_, 3, v_r_1638_);
lean_ctor_set(v___x_1643_, 2, v_v_1122_);
lean_ctor_set(v___x_1643_, 1, v_k_1121_);
lean_ctor_set(v___x_1643_, 0, v___x_1651_);
v___x_1653_ = v___x_1643_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v___x_1651_);
lean_ctor_set(v_reuseFailAlloc_1657_, 1, v_k_1121_);
lean_ctor_set(v_reuseFailAlloc_1657_, 2, v_v_1122_);
lean_ctor_set(v_reuseFailAlloc_1657_, 3, v_r_1638_);
lean_ctor_set(v_reuseFailAlloc_1657_, 4, v_impl_1614_);
v___x_1653_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
lean_object* v___x_1655_; 
if (v_isShared_1632_ == 0)
{
lean_ctor_set(v___x_1631_, 4, v___x_1653_);
lean_ctor_set(v___x_1631_, 3, v___y_1648_);
lean_ctor_set(v___x_1631_, 2, v_v_1636_);
lean_ctor_set(v___x_1631_, 1, v_k_1635_);
lean_ctor_set(v___x_1631_, 0, v___x_1646_);
v___x_1655_ = v___x_1631_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v___x_1646_);
lean_ctor_set(v_reuseFailAlloc_1656_, 1, v_k_1635_);
lean_ctor_set(v_reuseFailAlloc_1656_, 2, v_v_1636_);
lean_ctor_set(v_reuseFailAlloc_1656_, 3, v___y_1648_);
lean_ctor_set(v_reuseFailAlloc_1656_, 4, v___x_1653_);
v___x_1655_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
return v___x_1655_;
}
}
}
v___jp_1659_:
{
lean_object* v___x_1661_; lean_object* v___x_1663_; 
v___x_1661_ = lean_nat_add(v___x_1658_, v___y_1660_);
lean_dec(v___y_1660_);
lean_dec(v___x_1658_);
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 4, v_l_1637_);
lean_ctor_set(v___x_1126_, 3, v_l_1620_);
lean_ctor_set(v___x_1126_, 2, v_v_1619_);
lean_ctor_set(v___x_1126_, 1, v_k_1618_);
lean_ctor_set(v___x_1126_, 0, v___x_1661_);
v___x_1663_ = v___x_1126_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v___x_1661_);
lean_ctor_set(v_reuseFailAlloc_1667_, 1, v_k_1618_);
lean_ctor_set(v_reuseFailAlloc_1667_, 2, v_v_1619_);
lean_ctor_set(v_reuseFailAlloc_1667_, 3, v_l_1620_);
lean_ctor_set(v_reuseFailAlloc_1667_, 4, v_l_1637_);
v___x_1663_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
lean_object* v___x_1664_; 
v___x_1664_ = lean_nat_add(v___x_1615_, v_size_1616_);
lean_dec(v_size_1616_);
if (lean_obj_tag(v_r_1638_) == 0)
{
lean_object* v_size_1665_; 
v_size_1665_ = lean_ctor_get(v_r_1638_, 0);
lean_inc(v_size_1665_);
v___y_1648_ = v___x_1663_;
v___y_1649_ = v___x_1664_;
v___y_1650_ = v_size_1665_;
goto v___jp_1647_;
}
else
{
lean_object* v___x_1666_; 
v___x_1666_ = lean_unsigned_to_nat(0u);
v___y_1648_ = v___x_1663_;
v___y_1649_ = v___x_1664_;
v___y_1650_ = v___x_1666_;
goto v___jp_1647_;
}
}
}
}
}
else
{
lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1681_; 
lean_del_object(v___x_1126_);
v___x_1676_ = lean_nat_add(v___x_1615_, v_size_1617_);
lean_dec(v_size_1617_);
v___x_1677_ = lean_nat_add(v___x_1676_, v_size_1616_);
lean_dec(v___x_1676_);
v___x_1678_ = lean_nat_add(v___x_1615_, v_size_1616_);
lean_dec(v_size_1616_);
v___x_1679_ = lean_nat_add(v___x_1678_, v_size_1634_);
lean_dec(v___x_1678_);
lean_inc_ref(v_impl_1614_);
if (v_isShared_1632_ == 0)
{
lean_ctor_set(v___x_1631_, 4, v_impl_1614_);
lean_ctor_set(v___x_1631_, 3, v_r_1621_);
lean_ctor_set(v___x_1631_, 2, v_v_1122_);
lean_ctor_set(v___x_1631_, 1, v_k_1121_);
lean_ctor_set(v___x_1631_, 0, v___x_1679_);
v___x_1681_ = v___x_1631_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v___x_1679_);
lean_ctor_set(v_reuseFailAlloc_1694_, 1, v_k_1121_);
lean_ctor_set(v_reuseFailAlloc_1694_, 2, v_v_1122_);
lean_ctor_set(v_reuseFailAlloc_1694_, 3, v_r_1621_);
lean_ctor_set(v_reuseFailAlloc_1694_, 4, v_impl_1614_);
v___x_1681_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1688_; 
v_isSharedCheck_1688_ = !lean_is_exclusive(v_impl_1614_);
if (v_isSharedCheck_1688_ == 0)
{
lean_object* v_unused_1689_; lean_object* v_unused_1690_; lean_object* v_unused_1691_; lean_object* v_unused_1692_; lean_object* v_unused_1693_; 
v_unused_1689_ = lean_ctor_get(v_impl_1614_, 4);
lean_dec(v_unused_1689_);
v_unused_1690_ = lean_ctor_get(v_impl_1614_, 3);
lean_dec(v_unused_1690_);
v_unused_1691_ = lean_ctor_get(v_impl_1614_, 2);
lean_dec(v_unused_1691_);
v_unused_1692_ = lean_ctor_get(v_impl_1614_, 1);
lean_dec(v_unused_1692_);
v_unused_1693_ = lean_ctor_get(v_impl_1614_, 0);
lean_dec(v_unused_1693_);
v___x_1683_ = v_impl_1614_;
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
else
{
lean_dec(v_impl_1614_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1688_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
lean_object* v___x_1686_; 
if (v_isShared_1684_ == 0)
{
lean_ctor_set(v___x_1683_, 4, v___x_1681_);
lean_ctor_set(v___x_1683_, 3, v_l_1620_);
lean_ctor_set(v___x_1683_, 2, v_v_1619_);
lean_ctor_set(v___x_1683_, 1, v_k_1618_);
lean_ctor_set(v___x_1683_, 0, v___x_1677_);
v___x_1686_ = v___x_1683_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v___x_1677_);
lean_ctor_set(v_reuseFailAlloc_1687_, 1, v_k_1618_);
lean_ctor_set(v_reuseFailAlloc_1687_, 2, v_v_1619_);
lean_ctor_set(v_reuseFailAlloc_1687_, 3, v_l_1620_);
lean_ctor_set(v_reuseFailAlloc_1687_, 4, v___x_1681_);
v___x_1686_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
return v___x_1686_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1701_; lean_object* v___x_1702_; lean_object* v___x_1704_; 
v_size_1701_ = lean_ctor_get(v_impl_1614_, 0);
lean_inc(v_size_1701_);
v___x_1702_ = lean_nat_add(v___x_1615_, v_size_1701_);
lean_dec(v_size_1701_);
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 4, v_impl_1614_);
lean_ctor_set(v___x_1126_, 0, v___x_1702_);
v___x_1704_ = v___x_1126_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v___x_1702_);
lean_ctor_set(v_reuseFailAlloc_1705_, 1, v_k_1121_);
lean_ctor_set(v_reuseFailAlloc_1705_, 2, v_v_1122_);
lean_ctor_set(v_reuseFailAlloc_1705_, 3, v_l_1123_);
lean_ctor_set(v_reuseFailAlloc_1705_, 4, v_impl_1614_);
v___x_1704_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
return v___x_1704_;
}
}
}
else
{
if (lean_obj_tag(v_l_1123_) == 0)
{
lean_object* v_l_1706_; 
v_l_1706_ = lean_ctor_get(v_l_1123_, 3);
if (lean_obj_tag(v_l_1706_) == 0)
{
lean_object* v_r_1707_; 
lean_inc_ref(v_l_1706_);
v_r_1707_ = lean_ctor_get(v_l_1123_, 4);
lean_inc(v_r_1707_);
if (lean_obj_tag(v_r_1707_) == 0)
{
lean_object* v_size_1708_; lean_object* v_k_1709_; lean_object* v_v_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1723_; 
v_size_1708_ = lean_ctor_get(v_l_1123_, 0);
v_k_1709_ = lean_ctor_get(v_l_1123_, 1);
v_v_1710_ = lean_ctor_get(v_l_1123_, 2);
v_isSharedCheck_1723_ = !lean_is_exclusive(v_l_1123_);
if (v_isSharedCheck_1723_ == 0)
{
lean_object* v_unused_1724_; lean_object* v_unused_1725_; 
v_unused_1724_ = lean_ctor_get(v_l_1123_, 4);
lean_dec(v_unused_1724_);
v_unused_1725_ = lean_ctor_get(v_l_1123_, 3);
lean_dec(v_unused_1725_);
v___x_1712_ = v_l_1123_;
v_isShared_1713_ = v_isSharedCheck_1723_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_v_1710_);
lean_inc(v_k_1709_);
lean_inc(v_size_1708_);
lean_dec(v_l_1123_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1723_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
lean_object* v_size_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1718_; 
v_size_1714_ = lean_ctor_get(v_r_1707_, 0);
v___x_1715_ = lean_nat_add(v___x_1615_, v_size_1708_);
lean_dec(v_size_1708_);
v___x_1716_ = lean_nat_add(v___x_1615_, v_size_1714_);
if (v_isShared_1713_ == 0)
{
lean_ctor_set(v___x_1712_, 4, v_impl_1614_);
lean_ctor_set(v___x_1712_, 3, v_r_1707_);
lean_ctor_set(v___x_1712_, 2, v_v_1122_);
lean_ctor_set(v___x_1712_, 1, v_k_1121_);
lean_ctor_set(v___x_1712_, 0, v___x_1716_);
v___x_1718_ = v___x_1712_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v___x_1716_);
lean_ctor_set(v_reuseFailAlloc_1722_, 1, v_k_1121_);
lean_ctor_set(v_reuseFailAlloc_1722_, 2, v_v_1122_);
lean_ctor_set(v_reuseFailAlloc_1722_, 3, v_r_1707_);
lean_ctor_set(v_reuseFailAlloc_1722_, 4, v_impl_1614_);
v___x_1718_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
lean_object* v___x_1720_; 
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 4, v___x_1718_);
lean_ctor_set(v___x_1126_, 3, v_l_1706_);
lean_ctor_set(v___x_1126_, 2, v_v_1710_);
lean_ctor_set(v___x_1126_, 1, v_k_1709_);
lean_ctor_set(v___x_1126_, 0, v___x_1715_);
v___x_1720_ = v___x_1126_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v___x_1715_);
lean_ctor_set(v_reuseFailAlloc_1721_, 1, v_k_1709_);
lean_ctor_set(v_reuseFailAlloc_1721_, 2, v_v_1710_);
lean_ctor_set(v_reuseFailAlloc_1721_, 3, v_l_1706_);
lean_ctor_set(v_reuseFailAlloc_1721_, 4, v___x_1718_);
v___x_1720_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
return v___x_1720_;
}
}
}
}
else
{
lean_object* v_k_1726_; lean_object* v_v_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1738_; 
v_k_1726_ = lean_ctor_get(v_l_1123_, 1);
v_v_1727_ = lean_ctor_get(v_l_1123_, 2);
v_isSharedCheck_1738_ = !lean_is_exclusive(v_l_1123_);
if (v_isSharedCheck_1738_ == 0)
{
lean_object* v_unused_1739_; lean_object* v_unused_1740_; lean_object* v_unused_1741_; 
v_unused_1739_ = lean_ctor_get(v_l_1123_, 4);
lean_dec(v_unused_1739_);
v_unused_1740_ = lean_ctor_get(v_l_1123_, 3);
lean_dec(v_unused_1740_);
v_unused_1741_ = lean_ctor_get(v_l_1123_, 0);
lean_dec(v_unused_1741_);
v___x_1729_ = v_l_1123_;
v_isShared_1730_ = v_isSharedCheck_1738_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_v_1727_);
lean_inc(v_k_1726_);
lean_dec(v_l_1123_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1738_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
lean_object* v___x_1731_; lean_object* v___x_1733_; 
v___x_1731_ = lean_unsigned_to_nat(3u);
if (v_isShared_1730_ == 0)
{
lean_ctor_set(v___x_1729_, 3, v_r_1707_);
lean_ctor_set(v___x_1729_, 2, v_v_1122_);
lean_ctor_set(v___x_1729_, 1, v_k_1121_);
lean_ctor_set(v___x_1729_, 0, v___x_1615_);
v___x_1733_ = v___x_1729_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v___x_1615_);
lean_ctor_set(v_reuseFailAlloc_1737_, 1, v_k_1121_);
lean_ctor_set(v_reuseFailAlloc_1737_, 2, v_v_1122_);
lean_ctor_set(v_reuseFailAlloc_1737_, 3, v_r_1707_);
lean_ctor_set(v_reuseFailAlloc_1737_, 4, v_r_1707_);
v___x_1733_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
lean_object* v___x_1735_; 
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 4, v___x_1733_);
lean_ctor_set(v___x_1126_, 3, v_l_1706_);
lean_ctor_set(v___x_1126_, 2, v_v_1727_);
lean_ctor_set(v___x_1126_, 1, v_k_1726_);
lean_ctor_set(v___x_1126_, 0, v___x_1731_);
v___x_1735_ = v___x_1126_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v___x_1731_);
lean_ctor_set(v_reuseFailAlloc_1736_, 1, v_k_1726_);
lean_ctor_set(v_reuseFailAlloc_1736_, 2, v_v_1727_);
lean_ctor_set(v_reuseFailAlloc_1736_, 3, v_l_1706_);
lean_ctor_set(v_reuseFailAlloc_1736_, 4, v___x_1733_);
v___x_1735_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
return v___x_1735_;
}
}
}
}
}
else
{
lean_object* v_r_1742_; 
v_r_1742_ = lean_ctor_get(v_l_1123_, 4);
lean_inc(v_r_1742_);
if (lean_obj_tag(v_r_1742_) == 0)
{
lean_object* v_k_1743_; lean_object* v_v_1744_; lean_object* v___x_1746_; uint8_t v_isShared_1747_; uint8_t v_isSharedCheck_1767_; 
lean_inc(v_l_1706_);
v_k_1743_ = lean_ctor_get(v_l_1123_, 1);
v_v_1744_ = lean_ctor_get(v_l_1123_, 2);
v_isSharedCheck_1767_ = !lean_is_exclusive(v_l_1123_);
if (v_isSharedCheck_1767_ == 0)
{
lean_object* v_unused_1768_; lean_object* v_unused_1769_; lean_object* v_unused_1770_; 
v_unused_1768_ = lean_ctor_get(v_l_1123_, 4);
lean_dec(v_unused_1768_);
v_unused_1769_ = lean_ctor_get(v_l_1123_, 3);
lean_dec(v_unused_1769_);
v_unused_1770_ = lean_ctor_get(v_l_1123_, 0);
lean_dec(v_unused_1770_);
v___x_1746_ = v_l_1123_;
v_isShared_1747_ = v_isSharedCheck_1767_;
goto v_resetjp_1745_;
}
else
{
lean_inc(v_v_1744_);
lean_inc(v_k_1743_);
lean_dec(v_l_1123_);
v___x_1746_ = lean_box(0);
v_isShared_1747_ = v_isSharedCheck_1767_;
goto v_resetjp_1745_;
}
v_resetjp_1745_:
{
lean_object* v_k_1748_; lean_object* v_v_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1763_; 
v_k_1748_ = lean_ctor_get(v_r_1742_, 1);
v_v_1749_ = lean_ctor_get(v_r_1742_, 2);
v_isSharedCheck_1763_ = !lean_is_exclusive(v_r_1742_);
if (v_isSharedCheck_1763_ == 0)
{
lean_object* v_unused_1764_; lean_object* v_unused_1765_; lean_object* v_unused_1766_; 
v_unused_1764_ = lean_ctor_get(v_r_1742_, 4);
lean_dec(v_unused_1764_);
v_unused_1765_ = lean_ctor_get(v_r_1742_, 3);
lean_dec(v_unused_1765_);
v_unused_1766_ = lean_ctor_get(v_r_1742_, 0);
lean_dec(v_unused_1766_);
v___x_1751_ = v_r_1742_;
v_isShared_1752_ = v_isSharedCheck_1763_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_v_1749_);
lean_inc(v_k_1748_);
lean_dec(v_r_1742_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1763_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
lean_object* v___x_1753_; lean_object* v___x_1755_; 
v___x_1753_ = lean_unsigned_to_nat(3u);
if (v_isShared_1752_ == 0)
{
lean_ctor_set(v___x_1751_, 4, v_l_1706_);
lean_ctor_set(v___x_1751_, 3, v_l_1706_);
lean_ctor_set(v___x_1751_, 2, v_v_1744_);
lean_ctor_set(v___x_1751_, 1, v_k_1743_);
lean_ctor_set(v___x_1751_, 0, v___x_1615_);
v___x_1755_ = v___x_1751_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v___x_1615_);
lean_ctor_set(v_reuseFailAlloc_1762_, 1, v_k_1743_);
lean_ctor_set(v_reuseFailAlloc_1762_, 2, v_v_1744_);
lean_ctor_set(v_reuseFailAlloc_1762_, 3, v_l_1706_);
lean_ctor_set(v_reuseFailAlloc_1762_, 4, v_l_1706_);
v___x_1755_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
lean_object* v___x_1757_; 
if (v_isShared_1747_ == 0)
{
lean_ctor_set(v___x_1746_, 4, v_l_1706_);
lean_ctor_set(v___x_1746_, 2, v_v_1122_);
lean_ctor_set(v___x_1746_, 1, v_k_1121_);
lean_ctor_set(v___x_1746_, 0, v___x_1615_);
v___x_1757_ = v___x_1746_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v___x_1615_);
lean_ctor_set(v_reuseFailAlloc_1761_, 1, v_k_1121_);
lean_ctor_set(v_reuseFailAlloc_1761_, 2, v_v_1122_);
lean_ctor_set(v_reuseFailAlloc_1761_, 3, v_l_1706_);
lean_ctor_set(v_reuseFailAlloc_1761_, 4, v_l_1706_);
v___x_1757_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
lean_object* v___x_1759_; 
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 4, v___x_1757_);
lean_ctor_set(v___x_1126_, 3, v___x_1755_);
lean_ctor_set(v___x_1126_, 2, v_v_1749_);
lean_ctor_set(v___x_1126_, 1, v_k_1748_);
lean_ctor_set(v___x_1126_, 0, v___x_1753_);
v___x_1759_ = v___x_1126_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v___x_1753_);
lean_ctor_set(v_reuseFailAlloc_1760_, 1, v_k_1748_);
lean_ctor_set(v_reuseFailAlloc_1760_, 2, v_v_1749_);
lean_ctor_set(v_reuseFailAlloc_1760_, 3, v___x_1755_);
lean_ctor_set(v_reuseFailAlloc_1760_, 4, v___x_1757_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
return v___x_1759_;
}
}
}
}
}
}
else
{
lean_object* v___x_1771_; lean_object* v___x_1773_; 
v___x_1771_ = lean_unsigned_to_nat(2u);
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 4, v_r_1742_);
lean_ctor_set(v___x_1126_, 0, v___x_1771_);
v___x_1773_ = v___x_1126_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v___x_1771_);
lean_ctor_set(v_reuseFailAlloc_1774_, 1, v_k_1121_);
lean_ctor_set(v_reuseFailAlloc_1774_, 2, v_v_1122_);
lean_ctor_set(v_reuseFailAlloc_1774_, 3, v_l_1123_);
lean_ctor_set(v_reuseFailAlloc_1774_, 4, v_r_1742_);
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
else
{
lean_object* v___x_1776_; 
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 4, v_l_1123_);
lean_ctor_set(v___x_1126_, 0, v___x_1615_);
v___x_1776_ = v___x_1126_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v___x_1615_);
lean_ctor_set(v_reuseFailAlloc_1777_, 1, v_k_1121_);
lean_ctor_set(v_reuseFailAlloc_1777_, 2, v_v_1122_);
lean_ctor_set(v_reuseFailAlloc_1777_, 3, v_l_1123_);
lean_ctor_set(v_reuseFailAlloc_1777_, 4, v_l_1123_);
v___x_1776_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
return v___x_1776_;
}
}
}
}
}
}
}
else
{
return v_t_1120_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg___boxed(lean_object* v_k_1780_, lean_object* v_t_1781_){
_start:
{
lean_object* v_res_1782_; 
v_res_1782_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_k_1780_, v_t_1781_);
lean_dec_ref(v_k_1780_);
return v_res_1782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___lam__0(lean_object* v_val_1783_, lean_object* v_s_1784_){
_start:
{
lean_object* v_toRing_1785_; lean_object* v_invFn_x3f_1786_; lean_object* v_semiringId_x3f_1787_; lean_object* v_commSemiringInst_1788_; lean_object* v_commRingInst_1789_; lean_object* v_noZeroDivInst_x3f_1790_; lean_object* v_fieldInst_x3f_1791_; lean_object* v_denoteEntries_1792_; lean_object* v_nextId_1793_; lean_object* v_steps_1794_; lean_object* v_queue_1795_; lean_object* v_basis_1796_; lean_object* v_diseqs_1797_; uint8_t v_recheck_1798_; lean_object* v_invSet_1799_; lean_object* v_numEq0_x3f_1800_; uint8_t v_numEq0Updated_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1809_; 
v_toRing_1785_ = lean_ctor_get(v_s_1784_, 0);
v_invFn_x3f_1786_ = lean_ctor_get(v_s_1784_, 1);
v_semiringId_x3f_1787_ = lean_ctor_get(v_s_1784_, 2);
v_commSemiringInst_1788_ = lean_ctor_get(v_s_1784_, 3);
v_commRingInst_1789_ = lean_ctor_get(v_s_1784_, 4);
v_noZeroDivInst_x3f_1790_ = lean_ctor_get(v_s_1784_, 5);
v_fieldInst_x3f_1791_ = lean_ctor_get(v_s_1784_, 6);
v_denoteEntries_1792_ = lean_ctor_get(v_s_1784_, 7);
v_nextId_1793_ = lean_ctor_get(v_s_1784_, 8);
v_steps_1794_ = lean_ctor_get(v_s_1784_, 9);
v_queue_1795_ = lean_ctor_get(v_s_1784_, 10);
v_basis_1796_ = lean_ctor_get(v_s_1784_, 11);
v_diseqs_1797_ = lean_ctor_get(v_s_1784_, 12);
v_recheck_1798_ = lean_ctor_get_uint8(v_s_1784_, sizeof(void*)*15);
v_invSet_1799_ = lean_ctor_get(v_s_1784_, 13);
v_numEq0_x3f_1800_ = lean_ctor_get(v_s_1784_, 14);
v_numEq0Updated_1801_ = lean_ctor_get_uint8(v_s_1784_, sizeof(void*)*15 + 1);
v_isSharedCheck_1809_ = !lean_is_exclusive(v_s_1784_);
if (v_isSharedCheck_1809_ == 0)
{
v___x_1803_ = v_s_1784_;
v_isShared_1804_ = v_isSharedCheck_1809_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_numEq0_x3f_1800_);
lean_inc(v_invSet_1799_);
lean_inc(v_diseqs_1797_);
lean_inc(v_basis_1796_);
lean_inc(v_queue_1795_);
lean_inc(v_steps_1794_);
lean_inc(v_nextId_1793_);
lean_inc(v_denoteEntries_1792_);
lean_inc(v_fieldInst_x3f_1791_);
lean_inc(v_noZeroDivInst_x3f_1790_);
lean_inc(v_commRingInst_1789_);
lean_inc(v_commSemiringInst_1788_);
lean_inc(v_semiringId_x3f_1787_);
lean_inc(v_invFn_x3f_1786_);
lean_inc(v_toRing_1785_);
lean_dec(v_s_1784_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1809_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v___x_1805_; lean_object* v___x_1807_; 
v___x_1805_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_val_1783_, v_queue_1795_);
if (v_isShared_1804_ == 0)
{
lean_ctor_set(v___x_1803_, 10, v___x_1805_);
v___x_1807_ = v___x_1803_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(0, 15, 2);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v_toRing_1785_);
lean_ctor_set(v_reuseFailAlloc_1808_, 1, v_invFn_x3f_1786_);
lean_ctor_set(v_reuseFailAlloc_1808_, 2, v_semiringId_x3f_1787_);
lean_ctor_set(v_reuseFailAlloc_1808_, 3, v_commSemiringInst_1788_);
lean_ctor_set(v_reuseFailAlloc_1808_, 4, v_commRingInst_1789_);
lean_ctor_set(v_reuseFailAlloc_1808_, 5, v_noZeroDivInst_x3f_1790_);
lean_ctor_set(v_reuseFailAlloc_1808_, 6, v_fieldInst_x3f_1791_);
lean_ctor_set(v_reuseFailAlloc_1808_, 7, v_denoteEntries_1792_);
lean_ctor_set(v_reuseFailAlloc_1808_, 8, v_nextId_1793_);
lean_ctor_set(v_reuseFailAlloc_1808_, 9, v_steps_1794_);
lean_ctor_set(v_reuseFailAlloc_1808_, 10, v___x_1805_);
lean_ctor_set(v_reuseFailAlloc_1808_, 11, v_basis_1796_);
lean_ctor_set(v_reuseFailAlloc_1808_, 12, v_diseqs_1797_);
lean_ctor_set(v_reuseFailAlloc_1808_, 13, v_invSet_1799_);
lean_ctor_set(v_reuseFailAlloc_1808_, 14, v_numEq0_x3f_1800_);
lean_ctor_set_uint8(v_reuseFailAlloc_1808_, sizeof(void*)*15, v_recheck_1798_);
lean_ctor_set_uint8(v_reuseFailAlloc_1808_, sizeof(void*)*15 + 1, v_numEq0Updated_1801_);
v___x_1807_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
return v___x_1807_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___lam__0___boxed(lean_object* v_val_1810_, lean_object* v_s_1811_){
_start:
{
lean_object* v_res_1812_; 
v_res_1812_ = l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___lam__0(v_val_1810_, v_s_1811_);
lean_dec_ref(v_val_1810_);
return v_res_1812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f(lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_){
_start:
{
lean_object* v___x_1825_; 
v___x_1825_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_, v_a_1823_);
if (lean_obj_tag(v___x_1825_) == 0)
{
lean_object* v_a_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1865_; 
v_a_1826_ = lean_ctor_get(v___x_1825_, 0);
v_isSharedCheck_1865_ = !lean_is_exclusive(v___x_1825_);
if (v_isSharedCheck_1865_ == 0)
{
v___x_1828_ = v___x_1825_;
v_isShared_1829_ = v_isSharedCheck_1865_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_a_1826_);
lean_dec(v___x_1825_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1865_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v_queue_1830_; lean_object* v___x_1831_; 
v_queue_1830_ = lean_ctor_get(v_a_1826_, 10);
lean_inc(v_queue_1830_);
lean_dec(v_a_1826_);
v___x_1831_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_queue_1830_);
lean_dec(v_queue_1830_);
if (lean_obj_tag(v___x_1831_) == 1)
{
lean_object* v_val_1832_; lean_object* v___f_1833_; lean_object* v___x_1834_; 
lean_del_object(v___x_1828_);
v_val_1832_ = lean_ctor_get(v___x_1831_, 0);
lean_inc(v_val_1832_);
v___f_1833_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1833_, 0, v_val_1832_);
v___x_1834_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_1833_, v_a_1813_, v_a_1814_);
if (lean_obj_tag(v___x_1834_) == 0)
{
lean_object* v___x_1835_; lean_object* v___x_1836_; 
lean_dec_ref(v___x_1834_);
v___x_1835_ = lean_unsigned_to_nat(1u);
v___x_1836_ = l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg(v___x_1835_, v_a_1814_);
if (lean_obj_tag(v___x_1836_) == 0)
{
lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1843_; 
v_isSharedCheck_1843_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1843_ == 0)
{
lean_object* v_unused_1844_; 
v_unused_1844_ = lean_ctor_get(v___x_1836_, 0);
lean_dec(v_unused_1844_);
v___x_1838_ = v___x_1836_;
v_isShared_1839_ = v_isSharedCheck_1843_;
goto v_resetjp_1837_;
}
else
{
lean_dec(v___x_1836_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1843_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v___x_1841_; 
if (v_isShared_1839_ == 0)
{
lean_ctor_set(v___x_1838_, 0, v___x_1831_);
v___x_1841_ = v___x_1838_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v___x_1831_);
v___x_1841_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
return v___x_1841_;
}
}
}
else
{
lean_object* v_a_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1852_; 
lean_dec_ref(v___x_1831_);
v_a_1845_ = lean_ctor_get(v___x_1836_, 0);
v_isSharedCheck_1852_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1852_ == 0)
{
v___x_1847_ = v___x_1836_;
v_isShared_1848_ = v_isSharedCheck_1852_;
goto v_resetjp_1846_;
}
else
{
lean_inc(v_a_1845_);
lean_dec(v___x_1836_);
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
else
{
lean_object* v_a_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1860_; 
lean_dec_ref(v___x_1831_);
v_a_1853_ = lean_ctor_get(v___x_1834_, 0);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1834_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1855_ = v___x_1834_;
v_isShared_1856_ = v_isSharedCheck_1860_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_a_1853_);
lean_dec(v___x_1834_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1860_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v___x_1858_; 
if (v_isShared_1856_ == 0)
{
v___x_1858_ = v___x_1855_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v_a_1853_);
v___x_1858_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
return v___x_1858_;
}
}
}
}
else
{
lean_object* v___x_1861_; lean_object* v___x_1863_; 
lean_dec(v___x_1831_);
lean_dec_ref(v_a_1813_);
v___x_1861_ = lean_box(0);
if (v_isShared_1829_ == 0)
{
lean_ctor_set(v___x_1828_, 0, v___x_1861_);
v___x_1863_ = v___x_1828_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v___x_1861_);
v___x_1863_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
return v___x_1863_;
}
}
}
}
else
{
lean_object* v_a_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1873_; 
lean_dec_ref(v_a_1813_);
v_a_1866_ = lean_ctor_get(v___x_1825_, 0);
v_isSharedCheck_1873_ = !lean_is_exclusive(v___x_1825_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1868_ = v___x_1825_;
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_a_1866_);
lean_dec(v___x_1825_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
lean_object* v___x_1871_; 
if (v_isShared_1869_ == 0)
{
v___x_1871_ = v___x_1868_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v_a_1866_);
v___x_1871_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
return v___x_1871_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___boxed(lean_object* v_a_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_){
_start:
{
lean_object* v_res_1886_; 
v_res_1886_ = l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f(v_a_1874_, v_a_1875_, v_a_1876_, v_a_1877_, v_a_1878_, v_a_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_, v_a_1884_);
lean_dec(v_a_1884_);
lean_dec_ref(v_a_1883_);
lean_dec(v_a_1882_);
lean_dec_ref(v_a_1881_);
lean_dec(v_a_1880_);
lean_dec_ref(v_a_1879_);
lean_dec(v_a_1878_);
lean_dec_ref(v_a_1877_);
lean_dec(v_a_1876_);
lean_dec(v_a_1875_);
return v_res_1886_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0(lean_object* v_00_u03b2_1887_, lean_object* v_k_1888_, lean_object* v_t_1889_, lean_object* v_h_1890_){
_start:
{
lean_object* v___x_1891_; 
v___x_1891_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_k_1888_, v_t_1889_);
return v___x_1891_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___boxed(lean_object* v_00_u03b2_1892_, lean_object* v_k_1893_, lean_object* v_t_1894_, lean_object* v_h_1895_){
_start:
{
lean_object* v_res_1896_; 
v_res_1896_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0(v_00_u03b2_1892_, v_k_1893_, v_t_1894_, v_h_1895_);
lean_dec_ref(v_k_1893_);
return v_res_1896_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_1897_, lean_object* v_x_1898_, lean_object* v_x_1899_, lean_object* v_x_1900_){
_start:
{
lean_object* v_ks_1901_; lean_object* v_vs_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1926_; 
v_ks_1901_ = lean_ctor_get(v_x_1897_, 0);
v_vs_1902_ = lean_ctor_get(v_x_1897_, 1);
v_isSharedCheck_1926_ = !lean_is_exclusive(v_x_1897_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1904_ = v_x_1897_;
v_isShared_1905_ = v_isSharedCheck_1926_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_vs_1902_);
lean_inc(v_ks_1901_);
lean_dec(v_x_1897_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1926_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
lean_object* v___x_1906_; uint8_t v___x_1907_; 
v___x_1906_ = lean_array_get_size(v_ks_1901_);
v___x_1907_ = lean_nat_dec_lt(v_x_1898_, v___x_1906_);
if (v___x_1907_ == 0)
{
lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1911_; 
lean_dec(v_x_1898_);
v___x_1908_ = lean_array_push(v_ks_1901_, v_x_1899_);
v___x_1909_ = lean_array_push(v_vs_1902_, v_x_1900_);
if (v_isShared_1905_ == 0)
{
lean_ctor_set(v___x_1904_, 1, v___x_1909_);
lean_ctor_set(v___x_1904_, 0, v___x_1908_);
v___x_1911_ = v___x_1904_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v___x_1908_);
lean_ctor_set(v_reuseFailAlloc_1912_, 1, v___x_1909_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
return v___x_1911_;
}
}
else
{
lean_object* v_k_x27_1913_; uint8_t v___x_1914_; 
v_k_x27_1913_ = lean_array_fget_borrowed(v_ks_1901_, v_x_1898_);
v___x_1914_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_1899_, v_k_x27_1913_);
if (v___x_1914_ == 0)
{
lean_object* v___x_1916_; 
if (v_isShared_1905_ == 0)
{
v___x_1916_ = v___x_1904_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v_ks_1901_);
lean_ctor_set(v_reuseFailAlloc_1920_, 1, v_vs_1902_);
v___x_1916_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
lean_object* v___x_1917_; lean_object* v___x_1918_; 
v___x_1917_ = lean_unsigned_to_nat(1u);
v___x_1918_ = lean_nat_add(v_x_1898_, v___x_1917_);
lean_dec(v_x_1898_);
v_x_1897_ = v___x_1916_;
v_x_1898_ = v___x_1918_;
goto _start;
}
}
else
{
lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1924_; 
v___x_1921_ = lean_array_fset(v_ks_1901_, v_x_1898_, v_x_1899_);
v___x_1922_ = lean_array_fset(v_vs_1902_, v_x_1898_, v_x_1900_);
lean_dec(v_x_1898_);
if (v_isShared_1905_ == 0)
{
lean_ctor_set(v___x_1904_, 1, v___x_1922_);
lean_ctor_set(v___x_1904_, 0, v___x_1921_);
v___x_1924_ = v___x_1904_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v___x_1921_);
lean_ctor_set(v_reuseFailAlloc_1925_, 1, v___x_1922_);
v___x_1924_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
return v___x_1924_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1___redArg(lean_object* v_n_1927_, lean_object* v_k_1928_, lean_object* v_v_1929_){
_start:
{
lean_object* v___x_1930_; lean_object* v___x_1931_; 
v___x_1930_ = lean_unsigned_to_nat(0u);
v___x_1931_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1927_, v___x_1930_, v_k_1928_, v_v_1929_);
return v___x_1931_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1932_; 
v___x_1932_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1932_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(lean_object* v_x_1933_, size_t v_x_1934_, size_t v_x_1935_, lean_object* v_x_1936_, lean_object* v_x_1937_){
_start:
{
if (lean_obj_tag(v_x_1933_) == 0)
{
lean_object* v_es_1938_; size_t v___x_1939_; size_t v___x_1940_; size_t v___x_1941_; size_t v___x_1942_; lean_object* v_j_1943_; lean_object* v___x_1944_; uint8_t v___x_1945_; 
v_es_1938_ = lean_ctor_get(v_x_1933_, 0);
v___x_1939_ = ((size_t)5ULL);
v___x_1940_ = ((size_t)1ULL);
v___x_1941_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__1);
v___x_1942_ = lean_usize_land(v_x_1934_, v___x_1941_);
v_j_1943_ = lean_usize_to_nat(v___x_1942_);
v___x_1944_ = lean_array_get_size(v_es_1938_);
v___x_1945_ = lean_nat_dec_lt(v_j_1943_, v___x_1944_);
if (v___x_1945_ == 0)
{
lean_dec(v_j_1943_);
lean_dec(v_x_1937_);
lean_dec_ref(v_x_1936_);
return v_x_1933_;
}
else
{
lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1982_; 
lean_inc_ref(v_es_1938_);
v_isSharedCheck_1982_ = !lean_is_exclusive(v_x_1933_);
if (v_isSharedCheck_1982_ == 0)
{
lean_object* v_unused_1983_; 
v_unused_1983_ = lean_ctor_get(v_x_1933_, 0);
lean_dec(v_unused_1983_);
v___x_1947_ = v_x_1933_;
v_isShared_1948_ = v_isSharedCheck_1982_;
goto v_resetjp_1946_;
}
else
{
lean_dec(v_x_1933_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1982_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v_v_1949_; lean_object* v___x_1950_; lean_object* v_xs_x27_1951_; lean_object* v___y_1953_; 
v_v_1949_ = lean_array_fget(v_es_1938_, v_j_1943_);
v___x_1950_ = lean_box(0);
v_xs_x27_1951_ = lean_array_fset(v_es_1938_, v_j_1943_, v___x_1950_);
switch(lean_obj_tag(v_v_1949_))
{
case 0:
{
lean_object* v_key_1958_; lean_object* v_val_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1969_; 
v_key_1958_ = lean_ctor_get(v_v_1949_, 0);
v_val_1959_ = lean_ctor_get(v_v_1949_, 1);
v_isSharedCheck_1969_ = !lean_is_exclusive(v_v_1949_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1961_ = v_v_1949_;
v_isShared_1962_ = v_isSharedCheck_1969_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_val_1959_);
lean_inc(v_key_1958_);
lean_dec(v_v_1949_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_1969_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
uint8_t v___x_1963_; 
v___x_1963_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_1936_, v_key_1958_);
if (v___x_1963_ == 0)
{
lean_object* v___x_1964_; lean_object* v___x_1965_; 
lean_del_object(v___x_1961_);
v___x_1964_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1958_, v_val_1959_, v_x_1936_, v_x_1937_);
v___x_1965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1965_, 0, v___x_1964_);
v___y_1953_ = v___x_1965_;
goto v___jp_1952_;
}
else
{
lean_object* v___x_1967_; 
lean_dec(v_val_1959_);
lean_dec(v_key_1958_);
if (v_isShared_1962_ == 0)
{
lean_ctor_set(v___x_1961_, 1, v_x_1937_);
lean_ctor_set(v___x_1961_, 0, v_x_1936_);
v___x_1967_ = v___x_1961_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v_x_1936_);
lean_ctor_set(v_reuseFailAlloc_1968_, 1, v_x_1937_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
v___y_1953_ = v___x_1967_;
goto v___jp_1952_;
}
}
}
}
case 1:
{
lean_object* v_node_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1980_; 
v_node_1970_ = lean_ctor_get(v_v_1949_, 0);
v_isSharedCheck_1980_ = !lean_is_exclusive(v_v_1949_);
if (v_isSharedCheck_1980_ == 0)
{
v___x_1972_ = v_v_1949_;
v_isShared_1973_ = v_isSharedCheck_1980_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_node_1970_);
lean_dec(v_v_1949_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1980_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
size_t v___x_1974_; size_t v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1978_; 
v___x_1974_ = lean_usize_shift_right(v_x_1934_, v___x_1939_);
v___x_1975_ = lean_usize_add(v_x_1935_, v___x_1940_);
v___x_1976_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_node_1970_, v___x_1974_, v___x_1975_, v_x_1936_, v_x_1937_);
if (v_isShared_1973_ == 0)
{
lean_ctor_set(v___x_1972_, 0, v___x_1976_);
v___x_1978_ = v___x_1972_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v___x_1976_);
v___x_1978_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
v___y_1953_ = v___x_1978_;
goto v___jp_1952_;
}
}
}
default: 
{
lean_object* v___x_1981_; 
v___x_1981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1981_, 0, v_x_1936_);
lean_ctor_set(v___x_1981_, 1, v_x_1937_);
v___y_1953_ = v___x_1981_;
goto v___jp_1952_;
}
}
v___jp_1952_:
{
lean_object* v___x_1954_; lean_object* v___x_1956_; 
v___x_1954_ = lean_array_fset(v_xs_x27_1951_, v_j_1943_, v___y_1953_);
lean_dec(v_j_1943_);
if (v_isShared_1948_ == 0)
{
lean_ctor_set(v___x_1947_, 0, v___x_1954_);
v___x_1956_ = v___x_1947_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v___x_1954_);
v___x_1956_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
return v___x_1956_;
}
}
}
}
}
else
{
lean_object* v_ks_1984_; lean_object* v_vs_1985_; lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_2005_; 
v_ks_1984_ = lean_ctor_get(v_x_1933_, 0);
v_vs_1985_ = lean_ctor_get(v_x_1933_, 1);
v_isSharedCheck_2005_ = !lean_is_exclusive(v_x_1933_);
if (v_isSharedCheck_2005_ == 0)
{
v___x_1987_ = v_x_1933_;
v_isShared_1988_ = v_isSharedCheck_2005_;
goto v_resetjp_1986_;
}
else
{
lean_inc(v_vs_1985_);
lean_inc(v_ks_1984_);
lean_dec(v_x_1933_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_2005_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
lean_object* v___x_1990_; 
if (v_isShared_1988_ == 0)
{
v___x_1990_ = v___x_1987_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v_ks_1984_);
lean_ctor_set(v_reuseFailAlloc_2004_, 1, v_vs_1985_);
v___x_1990_ = v_reuseFailAlloc_2004_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
lean_object* v_newNode_1991_; uint8_t v___y_1993_; size_t v___x_1999_; uint8_t v___x_2000_; 
v_newNode_1991_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1___redArg(v___x_1990_, v_x_1936_, v_x_1937_);
v___x_1999_ = ((size_t)7ULL);
v___x_2000_ = lean_usize_dec_le(v___x_1999_, v_x_1935_);
if (v___x_2000_ == 0)
{
lean_object* v___x_2001_; lean_object* v___x_2002_; uint8_t v___x_2003_; 
v___x_2001_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1991_);
v___x_2002_ = lean_unsigned_to_nat(4u);
v___x_2003_ = lean_nat_dec_lt(v___x_2001_, v___x_2002_);
lean_dec(v___x_2001_);
v___y_1993_ = v___x_2003_;
goto v___jp_1992_;
}
else
{
v___y_1993_ = v___x_2000_;
goto v___jp_1992_;
}
v___jp_1992_:
{
if (v___y_1993_ == 0)
{
lean_object* v_ks_1994_; lean_object* v_vs_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; 
v_ks_1994_ = lean_ctor_get(v_newNode_1991_, 0);
lean_inc_ref(v_ks_1994_);
v_vs_1995_ = lean_ctor_get(v_newNode_1991_, 1);
lean_inc_ref(v_vs_1995_);
lean_dec_ref(v_newNode_1991_);
v___x_1996_ = lean_unsigned_to_nat(0u);
v___x_1997_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0);
v___x_1998_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg(v_x_1935_, v_ks_1994_, v_vs_1995_, v___x_1996_, v___x_1997_);
lean_dec_ref(v_vs_1995_);
lean_dec_ref(v_ks_1994_);
return v___x_1998_;
}
else
{
return v_newNode_1991_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg(size_t v_depth_2006_, lean_object* v_keys_2007_, lean_object* v_vals_2008_, lean_object* v_i_2009_, lean_object* v_entries_2010_){
_start:
{
lean_object* v___x_2011_; uint8_t v___x_2012_; 
v___x_2011_ = lean_array_get_size(v_keys_2007_);
v___x_2012_ = lean_nat_dec_lt(v_i_2009_, v___x_2011_);
if (v___x_2012_ == 0)
{
lean_dec(v_i_2009_);
return v_entries_2010_;
}
else
{
lean_object* v_k_2013_; lean_object* v_v_2014_; uint64_t v___x_2015_; size_t v_h_2016_; size_t v___x_2017_; lean_object* v___x_2018_; size_t v___x_2019_; size_t v___x_2020_; size_t v___x_2021_; size_t v_h_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; 
v_k_2013_ = lean_array_fget_borrowed(v_keys_2007_, v_i_2009_);
v_v_2014_ = lean_array_fget_borrowed(v_vals_2008_, v_i_2009_);
v___x_2015_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_2013_);
v_h_2016_ = lean_uint64_to_usize(v___x_2015_);
v___x_2017_ = ((size_t)5ULL);
v___x_2018_ = lean_unsigned_to_nat(1u);
v___x_2019_ = ((size_t)1ULL);
v___x_2020_ = lean_usize_sub(v_depth_2006_, v___x_2019_);
v___x_2021_ = lean_usize_mul(v___x_2017_, v___x_2020_);
v_h_2022_ = lean_usize_shift_right(v_h_2016_, v___x_2021_);
v___x_2023_ = lean_nat_add(v_i_2009_, v___x_2018_);
lean_dec(v_i_2009_);
lean_inc(v_v_2014_);
lean_inc(v_k_2013_);
v___x_2024_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_entries_2010_, v_h_2022_, v_depth_2006_, v_k_2013_, v_v_2014_);
v_i_2009_ = v___x_2023_;
v_entries_2010_ = v___x_2024_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_2026_, lean_object* v_keys_2027_, lean_object* v_vals_2028_, lean_object* v_i_2029_, lean_object* v_entries_2030_){
_start:
{
size_t v_depth_boxed_2031_; lean_object* v_res_2032_; 
v_depth_boxed_2031_ = lean_unbox_usize(v_depth_2026_);
lean_dec(v_depth_2026_);
v_res_2032_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg(v_depth_boxed_2031_, v_keys_2027_, v_vals_2028_, v_i_2029_, v_entries_2030_);
lean_dec_ref(v_vals_2028_);
lean_dec_ref(v_keys_2027_);
return v_res_2032_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___boxed(lean_object* v_x_2033_, lean_object* v_x_2034_, lean_object* v_x_2035_, lean_object* v_x_2036_, lean_object* v_x_2037_){
_start:
{
size_t v_x_8479__boxed_2038_; size_t v_x_8480__boxed_2039_; lean_object* v_res_2040_; 
v_x_8479__boxed_2038_ = lean_unbox_usize(v_x_2034_);
lean_dec(v_x_2034_);
v_x_8480__boxed_2039_ = lean_unbox_usize(v_x_2035_);
lean_dec(v_x_2035_);
v_res_2040_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_x_2033_, v_x_8479__boxed_2038_, v_x_8480__boxed_2039_, v_x_2036_, v_x_2037_);
return v_res_2040_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0___redArg(lean_object* v_x_2041_, lean_object* v_x_2042_, lean_object* v_x_2043_){
_start:
{
uint64_t v___x_2044_; size_t v___x_2045_; size_t v___x_2046_; lean_object* v___x_2047_; 
v___x_2044_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_2042_);
v___x_2045_ = lean_uint64_to_usize(v___x_2044_);
v___x_2046_ = ((size_t)1ULL);
v___x_2047_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_x_2041_, v___x_2045_, v___x_2046_, v_x_2042_, v_x_2043_);
return v___x_2047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___lam__0(lean_object* v_e_2048_, lean_object* v_ringId_2049_, lean_object* v_s_2050_){
_start:
{
lean_object* v_rings_2051_; lean_object* v_typeIdOf_2052_; lean_object* v_exprToRingId_2053_; lean_object* v_semirings_2054_; lean_object* v_stypeIdOf_2055_; lean_object* v_exprToSemiringId_2056_; lean_object* v_ncRings_2057_; lean_object* v_exprToNCRingId_2058_; lean_object* v_nctypeIdOf_2059_; lean_object* v_ncSemirings_2060_; lean_object* v_exprToNCSemiringId_2061_; lean_object* v_ncstypeIdOf_2062_; lean_object* v_steps_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2071_; 
v_rings_2051_ = lean_ctor_get(v_s_2050_, 0);
v_typeIdOf_2052_ = lean_ctor_get(v_s_2050_, 1);
v_exprToRingId_2053_ = lean_ctor_get(v_s_2050_, 2);
v_semirings_2054_ = lean_ctor_get(v_s_2050_, 3);
v_stypeIdOf_2055_ = lean_ctor_get(v_s_2050_, 4);
v_exprToSemiringId_2056_ = lean_ctor_get(v_s_2050_, 5);
v_ncRings_2057_ = lean_ctor_get(v_s_2050_, 6);
v_exprToNCRingId_2058_ = lean_ctor_get(v_s_2050_, 7);
v_nctypeIdOf_2059_ = lean_ctor_get(v_s_2050_, 8);
v_ncSemirings_2060_ = lean_ctor_get(v_s_2050_, 9);
v_exprToNCSemiringId_2061_ = lean_ctor_get(v_s_2050_, 10);
v_ncstypeIdOf_2062_ = lean_ctor_get(v_s_2050_, 11);
v_steps_2063_ = lean_ctor_get(v_s_2050_, 12);
v_isSharedCheck_2071_ = !lean_is_exclusive(v_s_2050_);
if (v_isSharedCheck_2071_ == 0)
{
v___x_2065_ = v_s_2050_;
v_isShared_2066_ = v_isSharedCheck_2071_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_steps_2063_);
lean_inc(v_ncstypeIdOf_2062_);
lean_inc(v_exprToNCSemiringId_2061_);
lean_inc(v_ncSemirings_2060_);
lean_inc(v_nctypeIdOf_2059_);
lean_inc(v_exprToNCRingId_2058_);
lean_inc(v_ncRings_2057_);
lean_inc(v_exprToSemiringId_2056_);
lean_inc(v_stypeIdOf_2055_);
lean_inc(v_semirings_2054_);
lean_inc(v_exprToRingId_2053_);
lean_inc(v_typeIdOf_2052_);
lean_inc(v_rings_2051_);
lean_dec(v_s_2050_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2071_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v___x_2067_; lean_object* v___x_2069_; 
v___x_2067_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0___redArg(v_exprToRingId_2053_, v_e_2048_, v_ringId_2049_);
if (v_isShared_2066_ == 0)
{
lean_ctor_set(v___x_2065_, 2, v___x_2067_);
v___x_2069_ = v___x_2065_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v_rings_2051_);
lean_ctor_set(v_reuseFailAlloc_2070_, 1, v_typeIdOf_2052_);
lean_ctor_set(v_reuseFailAlloc_2070_, 2, v___x_2067_);
lean_ctor_set(v_reuseFailAlloc_2070_, 3, v_semirings_2054_);
lean_ctor_set(v_reuseFailAlloc_2070_, 4, v_stypeIdOf_2055_);
lean_ctor_set(v_reuseFailAlloc_2070_, 5, v_exprToSemiringId_2056_);
lean_ctor_set(v_reuseFailAlloc_2070_, 6, v_ncRings_2057_);
lean_ctor_set(v_reuseFailAlloc_2070_, 7, v_exprToNCRingId_2058_);
lean_ctor_set(v_reuseFailAlloc_2070_, 8, v_nctypeIdOf_2059_);
lean_ctor_set(v_reuseFailAlloc_2070_, 9, v_ncSemirings_2060_);
lean_ctor_set(v_reuseFailAlloc_2070_, 10, v_exprToNCSemiringId_2061_);
lean_ctor_set(v_reuseFailAlloc_2070_, 11, v_ncstypeIdOf_2062_);
lean_ctor_set(v_reuseFailAlloc_2070_, 12, v_steps_2063_);
v___x_2069_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
return v___x_2069_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___closed__1(void){
_start:
{
lean_object* v___x_2073_; lean_object* v___x_2074_; 
v___x_2073_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___closed__0));
v___x_2074_ = l_Lean_stringToMessageData(v___x_2073_);
return v___x_2074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId(lean_object* v_e_2075_, lean_object* v_a_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_){
_start:
{
lean_object* v___x_2091_; 
v___x_2091_ = l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg(v_e_2075_, v_a_2077_, v_a_2085_);
if (lean_obj_tag(v___x_2091_) == 0)
{
lean_object* v_a_2092_; 
v_a_2092_ = lean_ctor_get(v___x_2091_, 0);
lean_inc(v_a_2092_);
lean_dec_ref(v___x_2091_);
if (lean_obj_tag(v_a_2092_) == 1)
{
lean_object* v_ringId_2093_; lean_object* v_val_2094_; uint8_t v___x_2095_; 
v_ringId_2093_ = lean_ctor_get(v_a_2076_, 0);
lean_inc(v_ringId_2093_);
lean_dec_ref(v_a_2076_);
v_val_2094_ = lean_ctor_get(v_a_2092_, 0);
lean_inc(v_val_2094_);
lean_dec_ref(v_a_2092_);
v___x_2095_ = lean_nat_dec_eq(v_val_2094_, v_ringId_2093_);
lean_dec(v_ringId_2093_);
lean_dec(v_val_2094_);
if (v___x_2095_ == 0)
{
lean_object* v___x_2096_; 
v___x_2096_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_2079_);
if (lean_obj_tag(v___x_2096_) == 0)
{
lean_object* v_a_2097_; uint8_t v_verbose_2098_; 
v_a_2097_ = lean_ctor_get(v___x_2096_, 0);
lean_inc(v_a_2097_);
lean_dec_ref(v___x_2096_);
v_verbose_2098_ = lean_ctor_get_uint8(v_a_2097_, sizeof(void*)*11 + 15);
lean_dec(v_a_2097_);
if (v_verbose_2098_ == 0)
{
lean_dec_ref(v_e_2075_);
goto v___jp_2088_;
}
else
{
lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; 
v___x_2099_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___closed__1);
v___x_2100_ = l_Lean_indentExpr(v_e_2075_);
v___x_2101_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2101_, 0, v___x_2099_);
lean_ctor_set(v___x_2101_, 1, v___x_2100_);
v___x_2102_ = l_Lean_Meta_Grind_reportIssue(v___x_2101_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_);
if (lean_obj_tag(v___x_2102_) == 0)
{
lean_dec_ref(v___x_2102_);
goto v___jp_2088_;
}
else
{
return v___x_2102_;
}
}
}
else
{
lean_object* v_a_2103_; lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2110_; 
lean_dec_ref(v_e_2075_);
v_a_2103_ = lean_ctor_get(v___x_2096_, 0);
v_isSharedCheck_2110_ = !lean_is_exclusive(v___x_2096_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2105_ = v___x_2096_;
v_isShared_2106_ = v_isSharedCheck_2110_;
goto v_resetjp_2104_;
}
else
{
lean_inc(v_a_2103_);
lean_dec(v___x_2096_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2110_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
lean_object* v___x_2108_; 
if (v_isShared_2106_ == 0)
{
v___x_2108_ = v___x_2105_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v_a_2103_);
v___x_2108_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
return v___x_2108_;
}
}
}
}
else
{
lean_dec_ref(v_e_2075_);
goto v___jp_2088_;
}
}
else
{
lean_object* v_ringId_2111_; lean_object* v___f_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; 
lean_dec(v_a_2092_);
v_ringId_2111_ = lean_ctor_get(v_a_2076_, 0);
lean_inc(v_ringId_2111_);
lean_dec_ref(v_a_2076_);
v___f_2112_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___lam__0), 3, 2);
lean_closure_set(v___f_2112_, 0, v_e_2075_);
lean_closure_set(v___f_2112_, 1, v_ringId_2111_);
v___x_2113_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_2114_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2113_, v___f_2112_, v_a_2077_);
return v___x_2114_;
}
}
else
{
lean_object* v_a_2115_; lean_object* v___x_2117_; uint8_t v_isShared_2118_; uint8_t v_isSharedCheck_2122_; 
lean_dec_ref(v_a_2076_);
lean_dec_ref(v_e_2075_);
v_a_2115_ = lean_ctor_get(v___x_2091_, 0);
v_isSharedCheck_2122_ = !lean_is_exclusive(v___x_2091_);
if (v_isSharedCheck_2122_ == 0)
{
v___x_2117_ = v___x_2091_;
v_isShared_2118_ = v_isSharedCheck_2122_;
goto v_resetjp_2116_;
}
else
{
lean_inc(v_a_2115_);
lean_dec(v___x_2091_);
v___x_2117_ = lean_box(0);
v_isShared_2118_ = v_isSharedCheck_2122_;
goto v_resetjp_2116_;
}
v_resetjp_2116_:
{
lean_object* v___x_2120_; 
if (v_isShared_2118_ == 0)
{
v___x_2120_ = v___x_2117_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v_a_2115_);
v___x_2120_ = v_reuseFailAlloc_2121_;
goto v_reusejp_2119_;
}
v_reusejp_2119_:
{
return v___x_2120_;
}
}
}
v___jp_2088_:
{
lean_object* v___x_2089_; lean_object* v___x_2090_; 
v___x_2089_ = lean_box(0);
v___x_2090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2090_, 0, v___x_2089_);
return v___x_2090_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___boxed(lean_object* v_e_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_){
_start:
{
lean_object* v_res_2136_; 
v_res_2136_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId(v_e_2123_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_, v_a_2130_, v_a_2131_, v_a_2132_, v_a_2133_, v_a_2134_);
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
return v_res_2136_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0(lean_object* v_00_u03b2_2137_, lean_object* v_x_2138_, lean_object* v_x_2139_, lean_object* v_x_2140_){
_start:
{
lean_object* v___x_2141_; 
v___x_2141_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0___redArg(v_x_2138_, v_x_2139_, v_x_2140_);
return v___x_2141_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0(lean_object* v_00_u03b2_2142_, lean_object* v_x_2143_, size_t v_x_2144_, size_t v_x_2145_, lean_object* v_x_2146_, lean_object* v_x_2147_){
_start:
{
lean_object* v___x_2148_; 
v___x_2148_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_x_2143_, v_x_2144_, v_x_2145_, v_x_2146_, v_x_2147_);
return v___x_2148_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2149_, lean_object* v_x_2150_, lean_object* v_x_2151_, lean_object* v_x_2152_, lean_object* v_x_2153_, lean_object* v_x_2154_){
_start:
{
size_t v_x_8784__boxed_2155_; size_t v_x_8785__boxed_2156_; lean_object* v_res_2157_; 
v_x_8784__boxed_2155_ = lean_unbox_usize(v_x_2151_);
lean_dec(v_x_2151_);
v_x_8785__boxed_2156_ = lean_unbox_usize(v_x_2152_);
lean_dec(v_x_2152_);
v_res_2157_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0(v_00_u03b2_2149_, v_x_2150_, v_x_8784__boxed_2155_, v_x_8785__boxed_2156_, v_x_2153_, v_x_2154_);
return v_res_2157_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2158_, lean_object* v_n_2159_, lean_object* v_k_2160_, lean_object* v_v_2161_){
_start:
{
lean_object* v___x_2162_; 
v___x_2162_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1___redArg(v_n_2159_, v_k_2160_, v_v_2161_);
return v___x_2162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_2163_, size_t v_depth_2164_, lean_object* v_keys_2165_, lean_object* v_vals_2166_, lean_object* v_heq_2167_, lean_object* v_i_2168_, lean_object* v_entries_2169_){
_start:
{
lean_object* v___x_2170_; 
v___x_2170_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg(v_depth_2164_, v_keys_2165_, v_vals_2166_, v_i_2168_, v_entries_2169_);
return v___x_2170_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2171_, lean_object* v_depth_2172_, lean_object* v_keys_2173_, lean_object* v_vals_2174_, lean_object* v_heq_2175_, lean_object* v_i_2176_, lean_object* v_entries_2177_){
_start:
{
size_t v_depth_boxed_2178_; lean_object* v_res_2179_; 
v_depth_boxed_2178_ = lean_unbox_usize(v_depth_2172_);
lean_dec(v_depth_2172_);
v_res_2179_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2(v_00_u03b2_2171_, v_depth_boxed_2178_, v_keys_2173_, v_vals_2174_, v_heq_2175_, v_i_2176_, v_entries_2177_);
lean_dec_ref(v_vals_2174_);
lean_dec_ref(v_keys_2173_);
return v_res_2179_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2180_, lean_object* v_x_2181_, lean_object* v_x_2182_, lean_object* v_x_2183_, lean_object* v_x_2184_){
_start:
{
lean_object* v___x_2185_; 
v___x_2185_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1_spec__2___redArg(v_x_2181_, v_x_2182_, v_x_2183_, v_x_2184_);
return v___x_2185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__0(lean_object* v_e_2186_, lean_object* v___f_2187_, lean_object* v___f_2188_, lean_object* v_size_2189_, lean_object* v_s_2190_){
_start:
{
lean_object* v_id_2191_; lean_object* v_type_2192_; lean_object* v_u_2193_; lean_object* v_ringInst_2194_; lean_object* v_semiringInst_2195_; lean_object* v_charInst_x3f_2196_; lean_object* v_addFn_x3f_2197_; lean_object* v_mulFn_x3f_2198_; lean_object* v_subFn_x3f_2199_; lean_object* v_negFn_x3f_2200_; lean_object* v_powFn_x3f_2201_; lean_object* v_intCastFn_x3f_2202_; lean_object* v_natCastFn_x3f_2203_; lean_object* v_one_x3f_2204_; lean_object* v_vars_2205_; lean_object* v_varMap_2206_; lean_object* v_denote_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2216_; 
v_id_2191_ = lean_ctor_get(v_s_2190_, 0);
v_type_2192_ = lean_ctor_get(v_s_2190_, 1);
v_u_2193_ = lean_ctor_get(v_s_2190_, 2);
v_ringInst_2194_ = lean_ctor_get(v_s_2190_, 3);
v_semiringInst_2195_ = lean_ctor_get(v_s_2190_, 4);
v_charInst_x3f_2196_ = lean_ctor_get(v_s_2190_, 5);
v_addFn_x3f_2197_ = lean_ctor_get(v_s_2190_, 6);
v_mulFn_x3f_2198_ = lean_ctor_get(v_s_2190_, 7);
v_subFn_x3f_2199_ = lean_ctor_get(v_s_2190_, 8);
v_negFn_x3f_2200_ = lean_ctor_get(v_s_2190_, 9);
v_powFn_x3f_2201_ = lean_ctor_get(v_s_2190_, 10);
v_intCastFn_x3f_2202_ = lean_ctor_get(v_s_2190_, 11);
v_natCastFn_x3f_2203_ = lean_ctor_get(v_s_2190_, 12);
v_one_x3f_2204_ = lean_ctor_get(v_s_2190_, 13);
v_vars_2205_ = lean_ctor_get(v_s_2190_, 14);
v_varMap_2206_ = lean_ctor_get(v_s_2190_, 15);
v_denote_2207_ = lean_ctor_get(v_s_2190_, 16);
v_isSharedCheck_2216_ = !lean_is_exclusive(v_s_2190_);
if (v_isSharedCheck_2216_ == 0)
{
v___x_2209_ = v_s_2190_;
v_isShared_2210_ = v_isSharedCheck_2216_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_denote_2207_);
lean_inc(v_varMap_2206_);
lean_inc(v_vars_2205_);
lean_inc(v_one_x3f_2204_);
lean_inc(v_natCastFn_x3f_2203_);
lean_inc(v_intCastFn_x3f_2202_);
lean_inc(v_powFn_x3f_2201_);
lean_inc(v_negFn_x3f_2200_);
lean_inc(v_subFn_x3f_2199_);
lean_inc(v_mulFn_x3f_2198_);
lean_inc(v_addFn_x3f_2197_);
lean_inc(v_charInst_x3f_2196_);
lean_inc(v_semiringInst_2195_);
lean_inc(v_ringInst_2194_);
lean_inc(v_u_2193_);
lean_inc(v_type_2192_);
lean_inc(v_id_2191_);
lean_dec(v_s_2190_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2216_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2214_; 
lean_inc_ref(v_e_2186_);
v___x_2211_ = l_Lean_PersistentArray_push___redArg(v_vars_2205_, v_e_2186_);
v___x_2212_ = l_Lean_PersistentHashMap_insert___redArg(v___f_2187_, v___f_2188_, v_varMap_2206_, v_e_2186_, v_size_2189_);
if (v_isShared_2210_ == 0)
{
lean_ctor_set(v___x_2209_, 15, v___x_2212_);
lean_ctor_set(v___x_2209_, 14, v___x_2211_);
v___x_2214_ = v___x_2209_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v_id_2191_);
lean_ctor_set(v_reuseFailAlloc_2215_, 1, v_type_2192_);
lean_ctor_set(v_reuseFailAlloc_2215_, 2, v_u_2193_);
lean_ctor_set(v_reuseFailAlloc_2215_, 3, v_ringInst_2194_);
lean_ctor_set(v_reuseFailAlloc_2215_, 4, v_semiringInst_2195_);
lean_ctor_set(v_reuseFailAlloc_2215_, 5, v_charInst_x3f_2196_);
lean_ctor_set(v_reuseFailAlloc_2215_, 6, v_addFn_x3f_2197_);
lean_ctor_set(v_reuseFailAlloc_2215_, 7, v_mulFn_x3f_2198_);
lean_ctor_set(v_reuseFailAlloc_2215_, 8, v_subFn_x3f_2199_);
lean_ctor_set(v_reuseFailAlloc_2215_, 9, v_negFn_x3f_2200_);
lean_ctor_set(v_reuseFailAlloc_2215_, 10, v_powFn_x3f_2201_);
lean_ctor_set(v_reuseFailAlloc_2215_, 11, v_intCastFn_x3f_2202_);
lean_ctor_set(v_reuseFailAlloc_2215_, 12, v_natCastFn_x3f_2203_);
lean_ctor_set(v_reuseFailAlloc_2215_, 13, v_one_x3f_2204_);
lean_ctor_set(v_reuseFailAlloc_2215_, 14, v___x_2211_);
lean_ctor_set(v_reuseFailAlloc_2215_, 15, v___x_2212_);
lean_ctor_set(v_reuseFailAlloc_2215_, 16, v_denote_2207_);
v___x_2214_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
return v___x_2214_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__1(lean_object* v_toPure_2217_, lean_object* v_size_2218_, lean_object* v_____r_2219_){
_start:
{
lean_object* v___x_2220_; 
v___x_2220_ = lean_apply_2(v_toPure_2217_, lean_box(0), v_size_2218_);
return v___x_2220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__2(lean_object* v_e_2221_, lean_object* v_inst_2222_, lean_object* v_toBind_2223_, lean_object* v___f_2224_, lean_object* v_____r_2225_){
_start:
{
lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; 
v___x_2226_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_2227_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_SolverExtension_markTerm___boxed), 14, 3);
lean_closure_set(v___x_2227_, 0, lean_box(0));
lean_closure_set(v___x_2227_, 1, v___x_2226_);
lean_closure_set(v___x_2227_, 2, v_e_2221_);
v___x_2228_ = lean_apply_2(v_inst_2222_, lean_box(0), v___x_2227_);
v___x_2229_ = lean_apply_4(v_toBind_2223_, lean_box(0), lean_box(0), v___x_2228_, v___f_2224_);
return v___x_2229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__3(lean_object* v_inst_2230_, lean_object* v_e_2231_, lean_object* v_toBind_2232_, lean_object* v___f_2233_, lean_object* v_____r_2234_){
_start:
{
lean_object* v___x_2235_; lean_object* v___x_2236_; 
v___x_2235_ = lean_apply_1(v_inst_2230_, v_e_2231_);
v___x_2236_ = lean_apply_4(v_toBind_2232_, lean_box(0), lean_box(0), v___x_2235_, v___f_2233_);
return v___x_2236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__4(lean_object* v___f_2237_, lean_object* v___f_2238_, lean_object* v_e_2239_, lean_object* v_toPure_2240_, lean_object* v_inst_2241_, lean_object* v_toBind_2242_, lean_object* v_inst_2243_, lean_object* v_modifyRing_2244_, lean_object* v_s_2245_){
_start:
{
lean_object* v_vars_2246_; lean_object* v_varMap_2247_; lean_object* v___x_2248_; 
v_vars_2246_ = lean_ctor_get(v_s_2245_, 14);
lean_inc_ref(v_vars_2246_);
v_varMap_2247_ = lean_ctor_get(v_s_2245_, 15);
lean_inc_ref(v_varMap_2247_);
lean_dec_ref(v_s_2245_);
lean_inc_ref(v_e_2239_);
lean_inc_ref(v___f_2238_);
lean_inc_ref(v___f_2237_);
v___x_2248_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_2237_, v___f_2238_, v_varMap_2247_, v_e_2239_);
if (lean_obj_tag(v___x_2248_) == 1)
{
lean_object* v_val_2249_; lean_object* v___x_2250_; 
lean_dec_ref(v_vars_2246_);
lean_dec(v_modifyRing_2244_);
lean_dec(v_inst_2243_);
lean_dec(v_toBind_2242_);
lean_dec(v_inst_2241_);
lean_dec_ref(v_e_2239_);
lean_dec_ref(v___f_2238_);
lean_dec_ref(v___f_2237_);
v_val_2249_ = lean_ctor_get(v___x_2248_, 0);
lean_inc(v_val_2249_);
lean_dec_ref(v___x_2248_);
v___x_2250_ = lean_apply_2(v_toPure_2240_, lean_box(0), v_val_2249_);
return v___x_2250_;
}
else
{
lean_object* v_size_2251_; lean_object* v___f_2252_; lean_object* v___f_2253_; lean_object* v___f_2254_; lean_object* v___f_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; 
lean_dec(v___x_2248_);
v_size_2251_ = lean_ctor_get(v_vars_2246_, 2);
lean_inc(v_size_2251_);
lean_dec_ref(v_vars_2246_);
lean_inc(v_size_2251_);
lean_inc_ref(v_e_2239_);
v___f_2252_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2252_, 0, v_e_2239_);
lean_closure_set(v___f_2252_, 1, v___f_2237_);
lean_closure_set(v___f_2252_, 2, v___f_2238_);
lean_closure_set(v___f_2252_, 3, v_size_2251_);
v___f_2253_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2253_, 0, v_toPure_2240_);
lean_closure_set(v___f_2253_, 1, v_size_2251_);
lean_inc(v_toBind_2242_);
lean_inc_ref(v_e_2239_);
v___f_2254_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2254_, 0, v_e_2239_);
lean_closure_set(v___f_2254_, 1, v_inst_2241_);
lean_closure_set(v___f_2254_, 2, v_toBind_2242_);
lean_closure_set(v___f_2254_, 3, v___f_2253_);
lean_inc(v_toBind_2242_);
v___f_2255_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__3), 5, 4);
lean_closure_set(v___f_2255_, 0, v_inst_2243_);
lean_closure_set(v___f_2255_, 1, v_e_2239_);
lean_closure_set(v___f_2255_, 2, v_toBind_2242_);
lean_closure_set(v___f_2255_, 3, v___f_2254_);
v___x_2256_ = lean_apply_1(v_modifyRing_2244_, v___f_2252_);
v___x_2257_ = lean_apply_4(v_toBind_2242_, lean_box(0), lean_box(0), v___x_2256_, v___f_2255_);
return v___x_2257_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg(lean_object* v_inst_2260_, lean_object* v_inst_2261_, lean_object* v_inst_2262_, lean_object* v_inst_2263_, lean_object* v_e_2264_){
_start:
{
lean_object* v_toApplicative_2265_; lean_object* v_toBind_2266_; lean_object* v_getRing_2267_; lean_object* v_modifyRing_2268_; lean_object* v_toPure_2269_; lean_object* v___f_2270_; lean_object* v___f_2271_; lean_object* v___f_2272_; lean_object* v___x_2273_; 
v_toApplicative_2265_ = lean_ctor_get(v_inst_2261_, 0);
lean_inc_ref(v_toApplicative_2265_);
v_toBind_2266_ = lean_ctor_get(v_inst_2261_, 1);
lean_inc(v_toBind_2266_);
lean_dec_ref(v_inst_2261_);
v_getRing_2267_ = lean_ctor_get(v_inst_2262_, 0);
lean_inc(v_getRing_2267_);
v_modifyRing_2268_ = lean_ctor_get(v_inst_2262_, 1);
lean_inc(v_modifyRing_2268_);
lean_dec_ref(v_inst_2262_);
v_toPure_2269_ = lean_ctor_get(v_toApplicative_2265_, 1);
lean_inc(v_toPure_2269_);
lean_dec_ref(v_toApplicative_2265_);
v___f_2270_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___closed__0));
v___f_2271_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___closed__1));
lean_inc(v_toBind_2266_);
v___f_2272_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__4), 9, 8);
lean_closure_set(v___f_2272_, 0, v___f_2270_);
lean_closure_set(v___f_2272_, 1, v___f_2271_);
lean_closure_set(v___f_2272_, 2, v_e_2264_);
lean_closure_set(v___f_2272_, 3, v_toPure_2269_);
lean_closure_set(v___f_2272_, 4, v_inst_2260_);
lean_closure_set(v___f_2272_, 5, v_toBind_2266_);
lean_closure_set(v___f_2272_, 6, v_inst_2263_);
lean_closure_set(v___f_2272_, 7, v_modifyRing_2268_);
v___x_2273_ = lean_apply_4(v_toBind_2266_, lean_box(0), lean_box(0), v_getRing_2267_, v___f_2272_);
return v___x_2273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore(lean_object* v_m_2274_, lean_object* v_inst_2275_, lean_object* v_inst_2276_, lean_object* v_inst_2277_, lean_object* v_inst_2278_, lean_object* v_e_2279_){
_start:
{
lean_object* v___x_2280_; 
v___x_2280_ = l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg(v_inst_2275_, v_inst_2276_, v_inst_2277_, v_inst_2278_, v_e_2279_);
return v___x_2280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkVar_spec__0___lam__0(lean_object* v_e_2283_, lean_object* v_size_2284_, lean_object* v_s_2285_){
_start:
{
lean_object* v_toRing_2286_; lean_object* v_invFn_x3f_2287_; lean_object* v_semiringId_x3f_2288_; lean_object* v_commSemiringInst_2289_; lean_object* v_commRingInst_2290_; lean_object* v_noZeroDivInst_x3f_2291_; lean_object* v_fieldInst_x3f_2292_; lean_object* v_denoteEntries_2293_; lean_object* v_nextId_2294_; lean_object* v_steps_2295_; lean_object* v_queue_2296_; lean_object* v_basis_2297_; lean_object* v_diseqs_2298_; uint8_t v_recheck_2299_; lean_object* v_invSet_2300_; lean_object* v_numEq0_x3f_2301_; uint8_t v_numEq0Updated_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2335_; 
v_toRing_2286_ = lean_ctor_get(v_s_2285_, 0);
v_invFn_x3f_2287_ = lean_ctor_get(v_s_2285_, 1);
v_semiringId_x3f_2288_ = lean_ctor_get(v_s_2285_, 2);
v_commSemiringInst_2289_ = lean_ctor_get(v_s_2285_, 3);
v_commRingInst_2290_ = lean_ctor_get(v_s_2285_, 4);
v_noZeroDivInst_x3f_2291_ = lean_ctor_get(v_s_2285_, 5);
v_fieldInst_x3f_2292_ = lean_ctor_get(v_s_2285_, 6);
v_denoteEntries_2293_ = lean_ctor_get(v_s_2285_, 7);
v_nextId_2294_ = lean_ctor_get(v_s_2285_, 8);
v_steps_2295_ = lean_ctor_get(v_s_2285_, 9);
v_queue_2296_ = lean_ctor_get(v_s_2285_, 10);
v_basis_2297_ = lean_ctor_get(v_s_2285_, 11);
v_diseqs_2298_ = lean_ctor_get(v_s_2285_, 12);
v_recheck_2299_ = lean_ctor_get_uint8(v_s_2285_, sizeof(void*)*15);
v_invSet_2300_ = lean_ctor_get(v_s_2285_, 13);
v_numEq0_x3f_2301_ = lean_ctor_get(v_s_2285_, 14);
v_numEq0Updated_2302_ = lean_ctor_get_uint8(v_s_2285_, sizeof(void*)*15 + 1);
v_isSharedCheck_2335_ = !lean_is_exclusive(v_s_2285_);
if (v_isSharedCheck_2335_ == 0)
{
v___x_2304_ = v_s_2285_;
v_isShared_2305_ = v_isSharedCheck_2335_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_numEq0_x3f_2301_);
lean_inc(v_invSet_2300_);
lean_inc(v_diseqs_2298_);
lean_inc(v_basis_2297_);
lean_inc(v_queue_2296_);
lean_inc(v_steps_2295_);
lean_inc(v_nextId_2294_);
lean_inc(v_denoteEntries_2293_);
lean_inc(v_fieldInst_x3f_2292_);
lean_inc(v_noZeroDivInst_x3f_2291_);
lean_inc(v_commRingInst_2290_);
lean_inc(v_commSemiringInst_2289_);
lean_inc(v_semiringId_x3f_2288_);
lean_inc(v_invFn_x3f_2287_);
lean_inc(v_toRing_2286_);
lean_dec(v_s_2285_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2335_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
lean_object* v_id_2306_; lean_object* v_type_2307_; lean_object* v_u_2308_; lean_object* v_ringInst_2309_; lean_object* v_semiringInst_2310_; lean_object* v_charInst_x3f_2311_; lean_object* v_addFn_x3f_2312_; lean_object* v_mulFn_x3f_2313_; lean_object* v_subFn_x3f_2314_; lean_object* v_negFn_x3f_2315_; lean_object* v_powFn_x3f_2316_; lean_object* v_intCastFn_x3f_2317_; lean_object* v_natCastFn_x3f_2318_; lean_object* v_one_x3f_2319_; lean_object* v_vars_2320_; lean_object* v_varMap_2321_; lean_object* v_denote_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2334_; 
v_id_2306_ = lean_ctor_get(v_toRing_2286_, 0);
v_type_2307_ = lean_ctor_get(v_toRing_2286_, 1);
v_u_2308_ = lean_ctor_get(v_toRing_2286_, 2);
v_ringInst_2309_ = lean_ctor_get(v_toRing_2286_, 3);
v_semiringInst_2310_ = lean_ctor_get(v_toRing_2286_, 4);
v_charInst_x3f_2311_ = lean_ctor_get(v_toRing_2286_, 5);
v_addFn_x3f_2312_ = lean_ctor_get(v_toRing_2286_, 6);
v_mulFn_x3f_2313_ = lean_ctor_get(v_toRing_2286_, 7);
v_subFn_x3f_2314_ = lean_ctor_get(v_toRing_2286_, 8);
v_negFn_x3f_2315_ = lean_ctor_get(v_toRing_2286_, 9);
v_powFn_x3f_2316_ = lean_ctor_get(v_toRing_2286_, 10);
v_intCastFn_x3f_2317_ = lean_ctor_get(v_toRing_2286_, 11);
v_natCastFn_x3f_2318_ = lean_ctor_get(v_toRing_2286_, 12);
v_one_x3f_2319_ = lean_ctor_get(v_toRing_2286_, 13);
v_vars_2320_ = lean_ctor_get(v_toRing_2286_, 14);
v_varMap_2321_ = lean_ctor_get(v_toRing_2286_, 15);
v_denote_2322_ = lean_ctor_get(v_toRing_2286_, 16);
v_isSharedCheck_2334_ = !lean_is_exclusive(v_toRing_2286_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2324_ = v_toRing_2286_;
v_isShared_2325_ = v_isSharedCheck_2334_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_denote_2322_);
lean_inc(v_varMap_2321_);
lean_inc(v_vars_2320_);
lean_inc(v_one_x3f_2319_);
lean_inc(v_natCastFn_x3f_2318_);
lean_inc(v_intCastFn_x3f_2317_);
lean_inc(v_powFn_x3f_2316_);
lean_inc(v_negFn_x3f_2315_);
lean_inc(v_subFn_x3f_2314_);
lean_inc(v_mulFn_x3f_2313_);
lean_inc(v_addFn_x3f_2312_);
lean_inc(v_charInst_x3f_2311_);
lean_inc(v_semiringInst_2310_);
lean_inc(v_ringInst_2309_);
lean_inc(v_u_2308_);
lean_inc(v_type_2307_);
lean_inc(v_id_2306_);
lean_dec(v_toRing_2286_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2334_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2329_; 
lean_inc_ref(v_e_2283_);
v___x_2326_ = l_Lean_PersistentArray_push___redArg(v_vars_2320_, v_e_2283_);
v___x_2327_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0___redArg(v_varMap_2321_, v_e_2283_, v_size_2284_);
if (v_isShared_2325_ == 0)
{
lean_ctor_set(v___x_2324_, 15, v___x_2327_);
lean_ctor_set(v___x_2324_, 14, v___x_2326_);
v___x_2329_ = v___x_2324_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v_id_2306_);
lean_ctor_set(v_reuseFailAlloc_2333_, 1, v_type_2307_);
lean_ctor_set(v_reuseFailAlloc_2333_, 2, v_u_2308_);
lean_ctor_set(v_reuseFailAlloc_2333_, 3, v_ringInst_2309_);
lean_ctor_set(v_reuseFailAlloc_2333_, 4, v_semiringInst_2310_);
lean_ctor_set(v_reuseFailAlloc_2333_, 5, v_charInst_x3f_2311_);
lean_ctor_set(v_reuseFailAlloc_2333_, 6, v_addFn_x3f_2312_);
lean_ctor_set(v_reuseFailAlloc_2333_, 7, v_mulFn_x3f_2313_);
lean_ctor_set(v_reuseFailAlloc_2333_, 8, v_subFn_x3f_2314_);
lean_ctor_set(v_reuseFailAlloc_2333_, 9, v_negFn_x3f_2315_);
lean_ctor_set(v_reuseFailAlloc_2333_, 10, v_powFn_x3f_2316_);
lean_ctor_set(v_reuseFailAlloc_2333_, 11, v_intCastFn_x3f_2317_);
lean_ctor_set(v_reuseFailAlloc_2333_, 12, v_natCastFn_x3f_2318_);
lean_ctor_set(v_reuseFailAlloc_2333_, 13, v_one_x3f_2319_);
lean_ctor_set(v_reuseFailAlloc_2333_, 14, v___x_2326_);
lean_ctor_set(v_reuseFailAlloc_2333_, 15, v___x_2327_);
lean_ctor_set(v_reuseFailAlloc_2333_, 16, v_denote_2322_);
v___x_2329_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
lean_object* v___x_2331_; 
if (v_isShared_2305_ == 0)
{
lean_ctor_set(v___x_2304_, 0, v___x_2329_);
v___x_2331_ = v___x_2304_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(0, 15, 2);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v___x_2329_);
lean_ctor_set(v_reuseFailAlloc_2332_, 1, v_invFn_x3f_2287_);
lean_ctor_set(v_reuseFailAlloc_2332_, 2, v_semiringId_x3f_2288_);
lean_ctor_set(v_reuseFailAlloc_2332_, 3, v_commSemiringInst_2289_);
lean_ctor_set(v_reuseFailAlloc_2332_, 4, v_commRingInst_2290_);
lean_ctor_set(v_reuseFailAlloc_2332_, 5, v_noZeroDivInst_x3f_2291_);
lean_ctor_set(v_reuseFailAlloc_2332_, 6, v_fieldInst_x3f_2292_);
lean_ctor_set(v_reuseFailAlloc_2332_, 7, v_denoteEntries_2293_);
lean_ctor_set(v_reuseFailAlloc_2332_, 8, v_nextId_2294_);
lean_ctor_set(v_reuseFailAlloc_2332_, 9, v_steps_2295_);
lean_ctor_set(v_reuseFailAlloc_2332_, 10, v_queue_2296_);
lean_ctor_set(v_reuseFailAlloc_2332_, 11, v_basis_2297_);
lean_ctor_set(v_reuseFailAlloc_2332_, 12, v_diseqs_2298_);
lean_ctor_set(v_reuseFailAlloc_2332_, 13, v_invSet_2300_);
lean_ctor_set(v_reuseFailAlloc_2332_, 14, v_numEq0_x3f_2301_);
lean_ctor_set_uint8(v_reuseFailAlloc_2332_, sizeof(void*)*15, v_recheck_2299_);
lean_ctor_set_uint8(v_reuseFailAlloc_2332_, sizeof(void*)*15 + 1, v_numEq0Updated_2302_);
v___x_2331_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
return v___x_2331_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkVar_spec__0(lean_object* v_e_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_){
_start:
{
lean_object* v___x_2349_; 
v___x_2349_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_);
if (lean_obj_tag(v___x_2349_) == 0)
{
lean_object* v_a_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2400_; 
v_a_2350_ = lean_ctor_get(v___x_2349_, 0);
v_isSharedCheck_2400_ = !lean_is_exclusive(v___x_2349_);
if (v_isSharedCheck_2400_ == 0)
{
v___x_2352_ = v___x_2349_;
v_isShared_2353_ = v_isSharedCheck_2400_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_a_2350_);
lean_dec(v___x_2349_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2400_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v_toRing_2354_; lean_object* v_vars_2355_; lean_object* v_varMap_2356_; lean_object* v___x_2357_; 
v_toRing_2354_ = lean_ctor_get(v_a_2350_, 0);
lean_inc_ref(v_toRing_2354_);
lean_dec(v_a_2350_);
v_vars_2355_ = lean_ctor_get(v_toRing_2354_, 14);
lean_inc_ref(v_vars_2355_);
v_varMap_2356_ = lean_ctor_get(v_toRing_2354_, 15);
lean_inc_ref(v_varMap_2356_);
lean_dec_ref(v_toRing_2354_);
v___x_2357_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(v_varMap_2356_, v_e_2336_);
if (lean_obj_tag(v___x_2357_) == 1)
{
lean_object* v_val_2358_; lean_object* v___x_2360_; 
lean_dec_ref(v_vars_2355_);
lean_dec(v___y_2347_);
lean_dec_ref(v___y_2346_);
lean_dec(v___y_2345_);
lean_dec_ref(v___y_2344_);
lean_dec(v___y_2343_);
lean_dec_ref(v___y_2342_);
lean_dec(v___y_2341_);
lean_dec_ref(v___y_2340_);
lean_dec(v___y_2339_);
lean_dec(v___y_2338_);
lean_dec_ref(v___y_2337_);
lean_dec_ref(v_e_2336_);
v_val_2358_ = lean_ctor_get(v___x_2357_, 0);
lean_inc(v_val_2358_);
lean_dec_ref(v___x_2357_);
if (v_isShared_2353_ == 0)
{
lean_ctor_set(v___x_2352_, 0, v_val_2358_);
v___x_2360_ = v___x_2352_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v_val_2358_);
v___x_2360_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
return v___x_2360_;
}
}
else
{
lean_object* v_size_2362_; lean_object* v___f_2363_; lean_object* v___x_2364_; 
lean_dec(v___x_2357_);
lean_del_object(v___x_2352_);
v_size_2362_ = lean_ctor_get(v_vars_2355_, 2);
lean_inc(v_size_2362_);
lean_dec_ref(v_vars_2355_);
lean_inc(v_size_2362_);
lean_inc_ref(v_e_2336_);
v___f_2363_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkVar_spec__0___lam__0), 3, 2);
lean_closure_set(v___f_2363_, 0, v_e_2336_);
lean_closure_set(v___f_2363_, 1, v_size_2362_);
lean_inc_ref(v___y_2337_);
v___x_2364_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_2363_, v___y_2337_, v___y_2338_);
if (lean_obj_tag(v___x_2364_) == 0)
{
lean_object* v___x_2365_; 
lean_dec_ref(v___x_2364_);
lean_inc_ref(v_e_2336_);
v___x_2365_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId(v_e_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_);
if (lean_obj_tag(v___x_2365_) == 0)
{
lean_object* v___x_2366_; lean_object* v___x_2367_; 
lean_dec_ref(v___x_2365_);
v___x_2366_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_2367_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_2366_, v_e_2336_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_);
if (lean_obj_tag(v___x_2367_) == 0)
{
lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2374_; 
v_isSharedCheck_2374_ = !lean_is_exclusive(v___x_2367_);
if (v_isSharedCheck_2374_ == 0)
{
lean_object* v_unused_2375_; 
v_unused_2375_ = lean_ctor_get(v___x_2367_, 0);
lean_dec(v_unused_2375_);
v___x_2369_ = v___x_2367_;
v_isShared_2370_ = v_isSharedCheck_2374_;
goto v_resetjp_2368_;
}
else
{
lean_dec(v___x_2367_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2374_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
lean_object* v___x_2372_; 
if (v_isShared_2370_ == 0)
{
lean_ctor_set(v___x_2369_, 0, v_size_2362_);
v___x_2372_ = v___x_2369_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2373_; 
v_reuseFailAlloc_2373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2373_, 0, v_size_2362_);
v___x_2372_ = v_reuseFailAlloc_2373_;
goto v_reusejp_2371_;
}
v_reusejp_2371_:
{
return v___x_2372_;
}
}
}
else
{
lean_object* v_a_2376_; lean_object* v___x_2378_; uint8_t v_isShared_2379_; uint8_t v_isSharedCheck_2383_; 
lean_dec(v_size_2362_);
v_a_2376_ = lean_ctor_get(v___x_2367_, 0);
v_isSharedCheck_2383_ = !lean_is_exclusive(v___x_2367_);
if (v_isSharedCheck_2383_ == 0)
{
v___x_2378_ = v___x_2367_;
v_isShared_2379_ = v_isSharedCheck_2383_;
goto v_resetjp_2377_;
}
else
{
lean_inc(v_a_2376_);
lean_dec(v___x_2367_);
v___x_2378_ = lean_box(0);
v_isShared_2379_ = v_isSharedCheck_2383_;
goto v_resetjp_2377_;
}
v_resetjp_2377_:
{
lean_object* v___x_2381_; 
if (v_isShared_2379_ == 0)
{
v___x_2381_ = v___x_2378_;
goto v_reusejp_2380_;
}
else
{
lean_object* v_reuseFailAlloc_2382_; 
v_reuseFailAlloc_2382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2382_, 0, v_a_2376_);
v___x_2381_ = v_reuseFailAlloc_2382_;
goto v_reusejp_2380_;
}
v_reusejp_2380_:
{
return v___x_2381_;
}
}
}
}
else
{
lean_object* v_a_2384_; lean_object* v___x_2386_; uint8_t v_isShared_2387_; uint8_t v_isSharedCheck_2391_; 
lean_dec(v_size_2362_);
lean_dec(v___y_2347_);
lean_dec_ref(v___y_2346_);
lean_dec(v___y_2345_);
lean_dec_ref(v___y_2344_);
lean_dec(v___y_2343_);
lean_dec_ref(v___y_2342_);
lean_dec(v___y_2341_);
lean_dec_ref(v___y_2340_);
lean_dec(v___y_2339_);
lean_dec(v___y_2338_);
lean_dec_ref(v_e_2336_);
v_a_2384_ = lean_ctor_get(v___x_2365_, 0);
v_isSharedCheck_2391_ = !lean_is_exclusive(v___x_2365_);
if (v_isSharedCheck_2391_ == 0)
{
v___x_2386_ = v___x_2365_;
v_isShared_2387_ = v_isSharedCheck_2391_;
goto v_resetjp_2385_;
}
else
{
lean_inc(v_a_2384_);
lean_dec(v___x_2365_);
v___x_2386_ = lean_box(0);
v_isShared_2387_ = v_isSharedCheck_2391_;
goto v_resetjp_2385_;
}
v_resetjp_2385_:
{
lean_object* v___x_2389_; 
if (v_isShared_2387_ == 0)
{
v___x_2389_ = v___x_2386_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2390_; 
v_reuseFailAlloc_2390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2390_, 0, v_a_2384_);
v___x_2389_ = v_reuseFailAlloc_2390_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
return v___x_2389_;
}
}
}
}
else
{
lean_object* v_a_2392_; lean_object* v___x_2394_; uint8_t v_isShared_2395_; uint8_t v_isSharedCheck_2399_; 
lean_dec(v_size_2362_);
lean_dec(v___y_2347_);
lean_dec_ref(v___y_2346_);
lean_dec(v___y_2345_);
lean_dec_ref(v___y_2344_);
lean_dec(v___y_2343_);
lean_dec_ref(v___y_2342_);
lean_dec(v___y_2341_);
lean_dec_ref(v___y_2340_);
lean_dec(v___y_2339_);
lean_dec(v___y_2338_);
lean_dec_ref(v___y_2337_);
lean_dec_ref(v_e_2336_);
v_a_2392_ = lean_ctor_get(v___x_2364_, 0);
v_isSharedCheck_2399_ = !lean_is_exclusive(v___x_2364_);
if (v_isSharedCheck_2399_ == 0)
{
v___x_2394_ = v___x_2364_;
v_isShared_2395_ = v_isSharedCheck_2399_;
goto v_resetjp_2393_;
}
else
{
lean_inc(v_a_2392_);
lean_dec(v___x_2364_);
v___x_2394_ = lean_box(0);
v_isShared_2395_ = v_isSharedCheck_2399_;
goto v_resetjp_2393_;
}
v_resetjp_2393_:
{
lean_object* v___x_2397_; 
if (v_isShared_2395_ == 0)
{
v___x_2397_ = v___x_2394_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v_a_2392_);
v___x_2397_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2396_;
}
v_reusejp_2396_:
{
return v___x_2397_;
}
}
}
}
}
}
else
{
lean_object* v_a_2401_; lean_object* v___x_2403_; uint8_t v_isShared_2404_; uint8_t v_isSharedCheck_2408_; 
lean_dec(v___y_2347_);
lean_dec_ref(v___y_2346_);
lean_dec(v___y_2345_);
lean_dec_ref(v___y_2344_);
lean_dec(v___y_2343_);
lean_dec_ref(v___y_2342_);
lean_dec(v___y_2341_);
lean_dec_ref(v___y_2340_);
lean_dec(v___y_2339_);
lean_dec(v___y_2338_);
lean_dec_ref(v___y_2337_);
lean_dec_ref(v_e_2336_);
v_a_2401_ = lean_ctor_get(v___x_2349_, 0);
v_isSharedCheck_2408_ = !lean_is_exclusive(v___x_2349_);
if (v_isSharedCheck_2408_ == 0)
{
v___x_2403_ = v___x_2349_;
v_isShared_2404_ = v_isSharedCheck_2408_;
goto v_resetjp_2402_;
}
else
{
lean_inc(v_a_2401_);
lean_dec(v___x_2349_);
v___x_2403_ = lean_box(0);
v_isShared_2404_ = v_isSharedCheck_2408_;
goto v_resetjp_2402_;
}
v_resetjp_2402_:
{
lean_object* v___x_2406_; 
if (v_isShared_2404_ == 0)
{
v___x_2406_ = v___x_2403_;
goto v_reusejp_2405_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v_a_2401_);
v___x_2406_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2405_;
}
v_reusejp_2405_:
{
return v___x_2406_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkVar_spec__0___boxed(lean_object* v_e_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_){
_start:
{
lean_object* v_res_2422_; 
v_res_2422_ = l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkVar_spec__0(v_e_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_);
return v_res_2422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVar(lean_object* v_e_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_){
_start:
{
lean_object* v___x_2436_; 
v___x_2436_ = l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkVar_spec__0(v_e_2423_, v_a_2424_, v_a_2425_, v_a_2426_, v_a_2427_, v_a_2428_, v_a_2429_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_);
return v___x_2436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVar___boxed(lean_object* v_e_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_){
_start:
{
lean_object* v_res_2450_; 
v_res_2450_ = l_Lean_Meta_Grind_Arith_CommRing_mkVar(v_e_2437_, v_a_2438_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_);
return v_res_2450_;
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
