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
lean_inc(v_a_138_);
lean_inc_ref(v_a_137_);
lean_inc(v_a_136_);
lean_inc_ref(v_a_135_);
lean_inc(v_a_134_);
lean_inc_ref(v_a_133_);
lean_inc(v_a_132_);
lean_inc_ref(v_a_131_);
lean_inc(v_a_130_);
lean_inc(v_a_129_);
v___x_142_ = lean_apply_12(v_x_128_, v___x_141_, v_a_129_, v_a_130_, v_a_131_, v_a_132_, v_a_133_, v_a_134_, v_a_135_, v_a_136_, v_a_137_, v_a_138_, lean_box(0));
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_run___redArg___boxed(lean_object* v_ringId_143_, lean_object* v_x_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_run___redArg(v_ringId_143_, v_x_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_, v_a_149_, v_a_150_, v_a_151_, v_a_152_, v_a_153_, v_a_154_);
lean_dec(v_a_154_);
lean_dec_ref(v_a_153_);
lean_dec(v_a_152_);
lean_dec_ref(v_a_151_);
lean_dec(v_a_150_);
lean_dec_ref(v_a_149_);
lean_dec(v_a_148_);
lean_dec_ref(v_a_147_);
lean_dec(v_a_146_);
lean_dec(v_a_145_);
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
lean_inc(v_a_169_);
lean_inc_ref(v_a_168_);
lean_inc(v_a_167_);
lean_inc_ref(v_a_166_);
lean_inc(v_a_165_);
lean_inc_ref(v_a_164_);
lean_inc(v_a_163_);
lean_inc_ref(v_a_162_);
lean_inc(v_a_161_);
lean_inc(v_a_160_);
v___x_173_ = lean_apply_12(v_x_159_, v___x_172_, v_a_160_, v_a_161_, v_a_162_, v_a_163_, v_a_164_, v_a_165_, v_a_166_, v_a_167_, v_a_168_, v_a_169_, lean_box(0));
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_run___boxed(lean_object* v_00_u03b1_174_, lean_object* v_ringId_175_, lean_object* v_x_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_run(v_00_u03b1_174_, v_ringId_175_, v_x_176_, v_a_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_, v_a_182_, v_a_183_, v_a_184_, v_a_185_, v_a_186_);
lean_dec(v_a_186_);
lean_dec_ref(v_a_185_);
lean_dec(v_a_184_);
lean_dec_ref(v_a_183_);
lean_dec(v_a_182_);
lean_dec_ref(v_a_181_);
lean_dec(v_a_180_);
lean_dec_ref(v_a_179_);
lean_dec(v_a_178_);
lean_dec(v_a_177_);
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
lean_inc(v___y_234_);
lean_inc_ref(v___y_233_);
lean_inc(v___y_232_);
lean_inc_ref(v___y_231_);
lean_inc(v___y_230_);
lean_inc_ref(v___y_229_);
lean_inc(v___y_228_);
lean_inc_ref(v___y_227_);
lean_inc(v___y_226_);
lean_inc(v___y_225_);
v___x_236_ = lean_grind_canon(v_e_223_, v___y_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_);
if (lean_obj_tag(v___x_236_) == 0)
{
lean_object* v_a_237_; lean_object* v___x_238_; 
v_a_237_ = lean_ctor_get(v___x_236_, 0);
lean_inc(v_a_237_);
lean_dec_ref(v___x_236_);
v___x_238_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_237_, v___y_230_);
return v___x_238_;
}
else
{
return v___x_236_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__0___boxed(lean_object* v_e_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__0(v_e_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_);
lean_dec(v___y_250_);
lean_dec_ref(v___y_249_);
lean_dec(v___y_248_);
lean_dec_ref(v___y_247_);
lean_dec(v___y_246_);
lean_dec_ref(v___y_245_);
lean_dec(v___y_244_);
lean_dec_ref(v___y_243_);
lean_dec(v___y_242_);
lean_dec(v___y_241_);
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
lean_dec(v___y_278_);
lean_dec_ref(v___y_277_);
lean_dec(v___y_276_);
lean_dec_ref(v___y_275_);
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
lean_inc_ref(v_a_476_);
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
lean_dec_ref(v_a_490_);
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
lean_object* v_ringId_521_; uint8_t v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
v_ringId_521_ = lean_ctor_get(v_a_509_, 0);
v___x_522_ = 1;
lean_inc(v_ringId_521_);
v___x_523_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_523_, 0, v_ringId_521_);
lean_ctor_set_uint8(v___x_523_, sizeof(void*)*1, v___x_522_);
lean_inc(v_a_519_);
lean_inc_ref(v_a_518_);
lean_inc(v_a_517_);
lean_inc_ref(v_a_516_);
lean_inc(v_a_515_);
lean_inc_ref(v_a_514_);
lean_inc(v_a_513_);
lean_inc_ref(v_a_512_);
lean_inc(v_a_511_);
lean_inc(v_a_510_);
v___x_524_ = lean_apply_12(v_x_508_, v___x_523_, v_a_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_, v_a_517_, v_a_518_, v_a_519_, lean_box(0));
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd___redArg___boxed(lean_object* v_x_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd___redArg(v_x_525_, v_a_526_, v_a_527_, v_a_528_, v_a_529_, v_a_530_, v_a_531_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_);
lean_dec(v_a_536_);
lean_dec_ref(v_a_535_);
lean_dec(v_a_534_);
lean_dec_ref(v_a_533_);
lean_dec(v_a_532_);
lean_dec_ref(v_a_531_);
lean_dec(v_a_530_);
lean_dec_ref(v_a_529_);
lean_dec(v_a_528_);
lean_dec(v_a_527_);
lean_dec_ref(v_a_526_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd(lean_object* v_00_u03b1_539_, lean_object* v_x_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_){
_start:
{
lean_object* v_ringId_553_; uint8_t v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v_ringId_553_ = lean_ctor_get(v_a_541_, 0);
v___x_554_ = 1;
lean_inc(v_ringId_553_);
v___x_555_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_555_, 0, v_ringId_553_);
lean_ctor_set_uint8(v___x_555_, sizeof(void*)*1, v___x_554_);
lean_inc(v_a_551_);
lean_inc_ref(v_a_550_);
lean_inc(v_a_549_);
lean_inc_ref(v_a_548_);
lean_inc(v_a_547_);
lean_inc_ref(v_a_546_);
lean_inc(v_a_545_);
lean_inc_ref(v_a_544_);
lean_inc(v_a_543_);
lean_inc(v_a_542_);
v___x_556_ = lean_apply_12(v_x_540_, v___x_555_, v_a_542_, v_a_543_, v_a_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_, v_a_549_, v_a_550_, v_a_551_, lean_box(0));
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd___boxed(lean_object* v_00_u03b1_557_, lean_object* v_x_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd(v_00_u03b1_557_, v_x_558_, v_a_559_, v_a_560_, v_a_561_, v_a_562_, v_a_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_);
lean_dec(v_a_569_);
lean_dec_ref(v_a_568_);
lean_dec(v_a_567_);
lean_dec_ref(v_a_566_);
lean_dec(v_a_565_);
lean_dec_ref(v_a_564_);
lean_dec(v_a_563_);
lean_dec_ref(v_a_562_);
lean_dec(v_a_561_);
lean_dec(v_a_560_);
lean_dec_ref(v_a_559_);
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___redArg(lean_object* v_a_572_){
_start:
{
uint8_t v_checkCoeffDvd_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v_checkCoeffDvd_574_ = lean_ctor_get_uint8(v_a_572_, sizeof(void*)*1);
v___x_575_ = lean_box(v_checkCoeffDvd_574_);
v___x_576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_576_, 0, v___x_575_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___redArg___boxed(lean_object* v_a_577_, lean_object* v_a_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___redArg(v_a_577_);
lean_dec_ref(v_a_577_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd(lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_){
_start:
{
lean_object* v___x_592_; 
v___x_592_ = l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___redArg(v_a_580_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___boxed(lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_){
_start:
{
lean_object* v_res_605_; 
v_res_605_ = l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd(v_a_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_, v_a_603_);
lean_dec(v_a_603_);
lean_dec_ref(v_a_602_);
lean_dec(v_a_601_);
lean_dec_ref(v_a_600_);
lean_dec(v_a_599_);
lean_dec_ref(v_a_598_);
lean_dec(v_a_597_);
lean_dec_ref(v_a_596_);
lean_dec(v_a_595_);
lean_dec(v_a_594_);
lean_dec_ref(v_a_593_);
return v_res_605_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_606_, lean_object* v_vals_607_, lean_object* v_i_608_, lean_object* v_k_609_){
_start:
{
lean_object* v___x_610_; uint8_t v___x_611_; 
v___x_610_ = lean_array_get_size(v_keys_606_);
v___x_611_ = lean_nat_dec_lt(v_i_608_, v___x_610_);
if (v___x_611_ == 0)
{
lean_object* v___x_612_; 
lean_dec(v_i_608_);
v___x_612_ = lean_box(0);
return v___x_612_;
}
else
{
lean_object* v_k_x27_613_; uint8_t v___x_614_; 
v_k_x27_613_ = lean_array_fget_borrowed(v_keys_606_, v_i_608_);
v___x_614_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_609_, v_k_x27_613_);
if (v___x_614_ == 0)
{
lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_615_ = lean_unsigned_to_nat(1u);
v___x_616_ = lean_nat_add(v_i_608_, v___x_615_);
lean_dec(v_i_608_);
v_i_608_ = v___x_616_;
goto _start;
}
else
{
lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_618_ = lean_array_fget_borrowed(v_vals_607_, v_i_608_);
lean_dec(v_i_608_);
lean_inc(v___x_618_);
v___x_619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_619_, 0, v___x_618_);
return v___x_619_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_620_, lean_object* v_vals_621_, lean_object* v_i_622_, lean_object* v_k_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_620_, v_vals_621_, v_i_622_, v_k_623_);
lean_dec_ref(v_k_623_);
lean_dec_ref(v_vals_621_);
lean_dec_ref(v_keys_620_);
return v_res_624_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_625_; size_t v___x_626_; size_t v___x_627_; 
v___x_625_ = ((size_t)5ULL);
v___x_626_ = ((size_t)1ULL);
v___x_627_ = lean_usize_shift_left(v___x_626_, v___x_625_);
return v___x_627_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_628_; size_t v___x_629_; size_t v___x_630_; 
v___x_628_ = ((size_t)1ULL);
v___x_629_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__0);
v___x_630_ = lean_usize_sub(v___x_629_, v___x_628_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg(lean_object* v_x_631_, size_t v_x_632_, lean_object* v_x_633_){
_start:
{
if (lean_obj_tag(v_x_631_) == 0)
{
lean_object* v_es_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_655_; 
v_es_634_ = lean_ctor_get(v_x_631_, 0);
v_isSharedCheck_655_ = !lean_is_exclusive(v_x_631_);
if (v_isSharedCheck_655_ == 0)
{
v___x_636_ = v_x_631_;
v_isShared_637_ = v_isSharedCheck_655_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_es_634_);
lean_dec(v_x_631_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_655_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_638_; size_t v___x_639_; size_t v___x_640_; size_t v___x_641_; lean_object* v_j_642_; lean_object* v___x_643_; 
v___x_638_ = lean_box(2);
v___x_639_ = ((size_t)5ULL);
v___x_640_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__1);
v___x_641_ = lean_usize_land(v_x_632_, v___x_640_);
v_j_642_ = lean_usize_to_nat(v___x_641_);
v___x_643_ = lean_array_get(v___x_638_, v_es_634_, v_j_642_);
lean_dec(v_j_642_);
lean_dec_ref(v_es_634_);
switch(lean_obj_tag(v___x_643_))
{
case 0:
{
lean_object* v_key_644_; lean_object* v_val_645_; uint8_t v___x_646_; 
v_key_644_ = lean_ctor_get(v___x_643_, 0);
lean_inc(v_key_644_);
v_val_645_ = lean_ctor_get(v___x_643_, 1);
lean_inc(v_val_645_);
lean_dec_ref(v___x_643_);
v___x_646_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_633_, v_key_644_);
lean_dec(v_key_644_);
if (v___x_646_ == 0)
{
lean_object* v___x_647_; 
lean_dec(v_val_645_);
lean_del_object(v___x_636_);
v___x_647_ = lean_box(0);
return v___x_647_;
}
else
{
lean_object* v___x_649_; 
if (v_isShared_637_ == 0)
{
lean_ctor_set_tag(v___x_636_, 1);
lean_ctor_set(v___x_636_, 0, v_val_645_);
v___x_649_ = v___x_636_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v_val_645_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
}
case 1:
{
lean_object* v_node_651_; size_t v___x_652_; 
lean_del_object(v___x_636_);
v_node_651_ = lean_ctor_get(v___x_643_, 0);
lean_inc(v_node_651_);
lean_dec_ref(v___x_643_);
v___x_652_ = lean_usize_shift_right(v_x_632_, v___x_639_);
v_x_631_ = v_node_651_;
v_x_632_ = v___x_652_;
goto _start;
}
default: 
{
lean_object* v___x_654_; 
lean_del_object(v___x_636_);
v___x_654_ = lean_box(0);
return v___x_654_;
}
}
}
}
else
{
lean_object* v_ks_656_; lean_object* v_vs_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v_ks_656_ = lean_ctor_get(v_x_631_, 0);
lean_inc_ref(v_ks_656_);
v_vs_657_ = lean_ctor_get(v_x_631_, 1);
lean_inc_ref(v_vs_657_);
lean_dec_ref(v_x_631_);
v___x_658_ = lean_unsigned_to_nat(0u);
v___x_659_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_656_, v_vs_657_, v___x_658_, v_x_633_);
lean_dec_ref(v_vs_657_);
lean_dec_ref(v_ks_656_);
return v___x_659_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_660_, lean_object* v_x_661_, lean_object* v_x_662_){
_start:
{
size_t v_x_867__boxed_663_; lean_object* v_res_664_; 
v_x_867__boxed_663_ = lean_unbox_usize(v_x_661_);
lean_dec(v_x_661_);
v_res_664_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg(v_x_660_, v_x_867__boxed_663_, v_x_662_);
lean_dec_ref(v_x_662_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(lean_object* v_x_665_, lean_object* v_x_666_){
_start:
{
uint64_t v___x_667_; size_t v___x_668_; lean_object* v___x_669_; 
v___x_667_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_666_);
v___x_668_ = lean_uint64_to_usize(v___x_667_);
v___x_669_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg(v_x_665_, v___x_668_, v_x_666_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg___boxed(lean_object* v_x_670_, lean_object* v_x_671_){
_start:
{
lean_object* v_res_672_; 
v_res_672_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(v_x_670_, v_x_671_);
lean_dec_ref(v_x_671_);
return v_res_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg(lean_object* v_e_673_, lean_object* v_a_674_, lean_object* v_a_675_){
_start:
{
lean_object* v___x_677_; 
v___x_677_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_674_, v_a_675_);
if (lean_obj_tag(v___x_677_) == 0)
{
lean_object* v_a_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_687_; 
v_a_678_ = lean_ctor_get(v___x_677_, 0);
v_isSharedCheck_687_ = !lean_is_exclusive(v___x_677_);
if (v_isSharedCheck_687_ == 0)
{
v___x_680_ = v___x_677_;
v_isShared_681_ = v_isSharedCheck_687_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_a_678_);
lean_dec(v___x_677_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_687_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v_exprToRingId_682_; lean_object* v___x_683_; lean_object* v___x_685_; 
v_exprToRingId_682_ = lean_ctor_get(v_a_678_, 2);
lean_inc_ref(v_exprToRingId_682_);
lean_dec(v_a_678_);
v___x_683_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(v_exprToRingId_682_, v_e_673_);
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 0, v___x_683_);
v___x_685_ = v___x_680_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v___x_683_);
v___x_685_ = v_reuseFailAlloc_686_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
return v___x_685_;
}
}
}
else
{
lean_object* v_a_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_695_; 
v_a_688_ = lean_ctor_get(v___x_677_, 0);
v_isSharedCheck_695_ = !lean_is_exclusive(v___x_677_);
if (v_isSharedCheck_695_ == 0)
{
v___x_690_ = v___x_677_;
v_isShared_691_ = v_isSharedCheck_695_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_a_688_);
lean_dec(v___x_677_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_695_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v___x_693_; 
if (v_isShared_691_ == 0)
{
v___x_693_ = v___x_690_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v_a_688_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
return v___x_693_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg___boxed(lean_object* v_e_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg(v_e_696_, v_a_697_, v_a_698_);
lean_dec_ref(v_a_698_);
lean_dec(v_a_697_);
lean_dec_ref(v_e_696_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f(lean_object* v_e_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_){
_start:
{
lean_object* v___x_713_; 
v___x_713_ = l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg(v_e_701_, v_a_702_, v_a_710_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___boxed(lean_object* v_e_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_){
_start:
{
lean_object* v_res_726_; 
v_res_726_ = l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f(v_e_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_, v_a_724_);
lean_dec(v_a_724_);
lean_dec_ref(v_a_723_);
lean_dec(v_a_722_);
lean_dec_ref(v_a_721_);
lean_dec(v_a_720_);
lean_dec_ref(v_a_719_);
lean_dec(v_a_718_);
lean_dec_ref(v_a_717_);
lean_dec(v_a_716_);
lean_dec(v_a_715_);
lean_dec_ref(v_e_714_);
return v_res_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0(lean_object* v_00_u03b2_727_, lean_object* v_x_728_, lean_object* v_x_729_){
_start:
{
lean_object* v___x_730_; 
v___x_730_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(v_x_728_, v_x_729_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___boxed(lean_object* v_00_u03b2_731_, lean_object* v_x_732_, lean_object* v_x_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0(v_00_u03b2_731_, v_x_732_, v_x_733_);
lean_dec_ref(v_x_733_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_735_, lean_object* v_x_736_, size_t v_x_737_, lean_object* v_x_738_){
_start:
{
lean_object* v___x_739_; 
v___x_739_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg(v_x_736_, v_x_737_, v_x_738_);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_740_, lean_object* v_x_741_, lean_object* v_x_742_, lean_object* v_x_743_){
_start:
{
size_t v_x_996__boxed_744_; lean_object* v_res_745_; 
v_x_996__boxed_744_ = lean_unbox_usize(v_x_742_);
lean_dec(v_x_742_);
v_res_745_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0(v_00_u03b2_740_, v_x_741_, v_x_996__boxed_744_, v_x_743_);
lean_dec_ref(v_x_743_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_746_, lean_object* v_keys_747_, lean_object* v_vals_748_, lean_object* v_heq_749_, lean_object* v_i_750_, lean_object* v_k_751_){
_start:
{
lean_object* v___x_752_; 
v___x_752_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_747_, v_vals_748_, v_i_750_, v_k_751_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_753_, lean_object* v_keys_754_, lean_object* v_vals_755_, lean_object* v_heq_756_, lean_object* v_i_757_, lean_object* v_k_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_753_, v_keys_754_, v_vals_755_, v_heq_756_, v_i_757_, v_k_758_);
lean_dec_ref(v_k_758_);
lean_dec_ref(v_vals_755_);
lean_dec_ref(v_keys_754_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg___lam__0(lean_object* v_toPure_760_, lean_object* v_____do__lift_761_){
_start:
{
lean_object* v_charInst_x3f_765_; 
v_charInst_x3f_765_ = lean_ctor_get(v_____do__lift_761_, 5);
lean_inc(v_charInst_x3f_765_);
lean_dec_ref(v_____do__lift_761_);
if (lean_obj_tag(v_charInst_x3f_765_) == 1)
{
lean_object* v_val_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_777_; 
v_val_766_ = lean_ctor_get(v_charInst_x3f_765_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v_charInst_x3f_765_);
if (v_isSharedCheck_777_ == 0)
{
v___x_768_ = v_charInst_x3f_765_;
v_isShared_769_ = v_isSharedCheck_777_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_val_766_);
lean_dec(v_charInst_x3f_765_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_777_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v_snd_770_; lean_object* v___x_771_; uint8_t v___x_772_; 
v_snd_770_ = lean_ctor_get(v_val_766_, 1);
lean_inc(v_snd_770_);
lean_dec(v_val_766_);
v___x_771_ = lean_unsigned_to_nat(0u);
v___x_772_ = lean_nat_dec_eq(v_snd_770_, v___x_771_);
if (v___x_772_ == 0)
{
lean_object* v___x_774_; 
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 0, v_snd_770_);
v___x_774_ = v___x_768_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_snd_770_);
v___x_774_ = v_reuseFailAlloc_776_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
lean_object* v___x_775_; 
v___x_775_ = lean_apply_2(v_toPure_760_, lean_box(0), v___x_774_);
return v___x_775_;
}
}
else
{
lean_dec(v_snd_770_);
lean_del_object(v___x_768_);
goto v___jp_762_;
}
}
}
else
{
lean_dec(v_charInst_x3f_765_);
goto v___jp_762_;
}
v___jp_762_:
{
lean_object* v___x_763_; lean_object* v___x_764_; 
v___x_763_ = lean_box(0);
v___x_764_ = lean_apply_2(v_toPure_760_, lean_box(0), v___x_763_);
return v___x_764_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg(lean_object* v_inst_778_, lean_object* v_inst_779_){
_start:
{
lean_object* v_toApplicative_780_; lean_object* v_toBind_781_; lean_object* v_getRing_782_; lean_object* v_toPure_783_; lean_object* v___f_784_; lean_object* v___x_785_; 
v_toApplicative_780_ = lean_ctor_get(v_inst_778_, 0);
lean_inc_ref(v_toApplicative_780_);
v_toBind_781_ = lean_ctor_get(v_inst_778_, 1);
lean_inc(v_toBind_781_);
lean_dec_ref(v_inst_778_);
v_getRing_782_ = lean_ctor_get(v_inst_779_, 0);
lean_inc(v_getRing_782_);
lean_dec_ref(v_inst_779_);
v_toPure_783_ = lean_ctor_get(v_toApplicative_780_, 1);
lean_inc(v_toPure_783_);
lean_dec_ref(v_toApplicative_780_);
v___f_784_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_784_, 0, v_toPure_783_);
v___x_785_ = lean_apply_4(v_toBind_781_, lean_box(0), lean_box(0), v_getRing_782_, v___f_784_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f(lean_object* v_m_786_, lean_object* v_inst_787_, lean_object* v_inst_788_){
_start:
{
lean_object* v___x_789_; 
v___x_789_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg(v_inst_787_, v_inst_788_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f___redArg___lam__0(lean_object* v_toPure_790_, lean_object* v_____do__lift_791_){
_start:
{
lean_object* v_charInst_x3f_795_; 
v_charInst_x3f_795_ = lean_ctor_get(v_____do__lift_791_, 5);
lean_inc(v_charInst_x3f_795_);
lean_dec_ref(v_____do__lift_791_);
if (lean_obj_tag(v_charInst_x3f_795_) == 1)
{
lean_object* v_val_796_; lean_object* v_snd_797_; lean_object* v___x_798_; uint8_t v___x_799_; 
v_val_796_ = lean_ctor_get(v_charInst_x3f_795_, 0);
v_snd_797_ = lean_ctor_get(v_val_796_, 1);
v___x_798_ = lean_unsigned_to_nat(0u);
v___x_799_ = lean_nat_dec_eq(v_snd_797_, v___x_798_);
if (v___x_799_ == 0)
{
lean_object* v___x_800_; 
v___x_800_ = lean_apply_2(v_toPure_790_, lean_box(0), v_charInst_x3f_795_);
return v___x_800_;
}
else
{
lean_dec_ref(v_charInst_x3f_795_);
goto v___jp_792_;
}
}
else
{
lean_dec(v_charInst_x3f_795_);
goto v___jp_792_;
}
v___jp_792_:
{
lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_793_ = lean_box(0);
v___x_794_ = lean_apply_2(v_toPure_790_, lean_box(0), v___x_793_);
return v___x_794_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f___redArg(lean_object* v_inst_801_, lean_object* v_inst_802_){
_start:
{
lean_object* v_toApplicative_803_; lean_object* v_toBind_804_; lean_object* v_getRing_805_; lean_object* v_toPure_806_; lean_object* v___f_807_; lean_object* v___x_808_; 
v_toApplicative_803_ = lean_ctor_get(v_inst_801_, 0);
lean_inc_ref(v_toApplicative_803_);
v_toBind_804_ = lean_ctor_get(v_inst_801_, 1);
lean_inc(v_toBind_804_);
lean_dec_ref(v_inst_801_);
v_getRing_805_ = lean_ctor_get(v_inst_802_, 0);
lean_inc(v_getRing_805_);
lean_dec_ref(v_inst_802_);
v_toPure_806_ = lean_ctor_get(v_toApplicative_803_, 1);
lean_inc(v_toPure_806_);
lean_dec_ref(v_toApplicative_803_);
v___f_807_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_807_, 0, v_toPure_806_);
v___x_808_ = lean_apply_4(v_toBind_804_, lean_box(0), lean_box(0), v_getRing_805_, v___f_807_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f(lean_object* v_m_809_, lean_object* v_inst_810_, lean_object* v_inst_811_){
_start:
{
lean_object* v___x_812_; 
v___x_812_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f___redArg(v_inst_810_, v_inst_811_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisorsInst_x3f(lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_){
_start:
{
lean_object* v___x_825_; 
v___x_825_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_, v_a_820_, v_a_821_, v_a_822_, v_a_823_);
if (lean_obj_tag(v___x_825_) == 0)
{
lean_object* v_a_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_834_; 
v_a_826_ = lean_ctor_get(v___x_825_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_825_);
if (v_isSharedCheck_834_ == 0)
{
v___x_828_ = v___x_825_;
v_isShared_829_ = v_isSharedCheck_834_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_a_826_);
lean_dec(v___x_825_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_834_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v_noZeroDivInst_x3f_830_; lean_object* v___x_832_; 
v_noZeroDivInst_x3f_830_ = lean_ctor_get(v_a_826_, 5);
lean_inc(v_noZeroDivInst_x3f_830_);
lean_dec(v_a_826_);
if (v_isShared_829_ == 0)
{
lean_ctor_set(v___x_828_, 0, v_noZeroDivInst_x3f_830_);
v___x_832_ = v___x_828_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_noZeroDivInst_x3f_830_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
}
else
{
lean_object* v_a_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_842_; 
v_a_835_ = lean_ctor_get(v___x_825_, 0);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_825_);
if (v_isSharedCheck_842_ == 0)
{
v___x_837_ = v___x_825_;
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_a_835_);
lean_dec(v___x_825_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_840_; 
if (v_isShared_838_ == 0)
{
v___x_840_ = v___x_837_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_a_835_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisorsInst_x3f___boxed(lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisorsInst_x3f(v_a_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_);
lean_dec(v_a_853_);
lean_dec_ref(v_a_852_);
lean_dec(v_a_851_);
lean_dec_ref(v_a_850_);
lean_dec(v_a_849_);
lean_dec_ref(v_a_848_);
lean_dec(v_a_847_);
lean_dec_ref(v_a_846_);
lean_dec(v_a_845_);
lean_dec(v_a_844_);
lean_dec_ref(v_a_843_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisors(lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_){
_start:
{
lean_object* v___x_868_; 
v___x_868_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_856_, v_a_857_, v_a_858_, v_a_859_, v_a_860_, v_a_861_, v_a_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_);
if (lean_obj_tag(v___x_868_) == 0)
{
lean_object* v_a_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_884_; 
v_a_869_ = lean_ctor_get(v___x_868_, 0);
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_868_);
if (v_isSharedCheck_884_ == 0)
{
v___x_871_ = v___x_868_;
v_isShared_872_ = v_isSharedCheck_884_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_a_869_);
lean_dec(v___x_868_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_884_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v_noZeroDivInst_x3f_873_; 
v_noZeroDivInst_x3f_873_ = lean_ctor_get(v_a_869_, 5);
lean_inc(v_noZeroDivInst_x3f_873_);
lean_dec(v_a_869_);
if (lean_obj_tag(v_noZeroDivInst_x3f_873_) == 0)
{
uint8_t v___x_874_; lean_object* v___x_875_; lean_object* v___x_877_; 
v___x_874_ = 0;
v___x_875_ = lean_box(v___x_874_);
if (v_isShared_872_ == 0)
{
lean_ctor_set(v___x_871_, 0, v___x_875_);
v___x_877_ = v___x_871_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v___x_875_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
else
{
uint8_t v___x_879_; lean_object* v___x_880_; lean_object* v___x_882_; 
lean_dec_ref(v_noZeroDivInst_x3f_873_);
v___x_879_ = 1;
v___x_880_ = lean_box(v___x_879_);
if (v_isShared_872_ == 0)
{
lean_ctor_set(v___x_871_, 0, v___x_880_);
v___x_882_ = v___x_871_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v___x_880_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
}
}
else
{
lean_object* v_a_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_892_; 
v_a_885_ = lean_ctor_get(v___x_868_, 0);
v_isSharedCheck_892_ = !lean_is_exclusive(v___x_868_);
if (v_isSharedCheck_892_ == 0)
{
v___x_887_ = v___x_868_;
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_a_885_);
lean_dec(v___x_868_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___x_890_; 
if (v_isShared_888_ == 0)
{
v___x_890_ = v___x_887_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_a_885_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisors___boxed(lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisors(v_a_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_);
lean_dec(v_a_903_);
lean_dec_ref(v_a_902_);
lean_dec(v_a_901_);
lean_dec_ref(v_a_900_);
lean_dec(v_a_899_);
lean_dec_ref(v_a_898_);
lean_dec(v_a_897_);
lean_dec_ref(v_a_896_);
lean_dec(v_a_895_);
lean_dec(v_a_894_);
lean_dec_ref(v_a_893_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_hasChar(lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_){
_start:
{
lean_object* v___x_918_; 
v___x_918_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_);
if (lean_obj_tag(v___x_918_) == 0)
{
lean_object* v_a_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_935_; 
v_a_919_ = lean_ctor_get(v___x_918_, 0);
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_918_);
if (v_isSharedCheck_935_ == 0)
{
v___x_921_ = v___x_918_;
v_isShared_922_ = v_isSharedCheck_935_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_a_919_);
lean_dec(v___x_918_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_935_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v_toRing_923_; lean_object* v_charInst_x3f_924_; 
v_toRing_923_ = lean_ctor_get(v_a_919_, 0);
lean_inc_ref(v_toRing_923_);
lean_dec(v_a_919_);
v_charInst_x3f_924_ = lean_ctor_get(v_toRing_923_, 5);
lean_inc(v_charInst_x3f_924_);
lean_dec_ref(v_toRing_923_);
if (lean_obj_tag(v_charInst_x3f_924_) == 0)
{
uint8_t v___x_925_; lean_object* v___x_926_; lean_object* v___x_928_; 
v___x_925_ = 0;
v___x_926_ = lean_box(v___x_925_);
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 0, v___x_926_);
v___x_928_ = v___x_921_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v___x_926_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
else
{
uint8_t v___x_930_; lean_object* v___x_931_; lean_object* v___x_933_; 
lean_dec_ref(v_charInst_x3f_924_);
v___x_930_ = 1;
v___x_931_ = lean_box(v___x_930_);
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 0, v___x_931_);
v___x_933_ = v___x_921_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v___x_931_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
return v___x_933_;
}
}
}
}
else
{
lean_object* v_a_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_943_; 
v_a_936_ = lean_ctor_get(v___x_918_, 0);
v_isSharedCheck_943_ = !lean_is_exclusive(v___x_918_);
if (v_isSharedCheck_943_ == 0)
{
v___x_938_ = v___x_918_;
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_a_936_);
lean_dec(v___x_918_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_941_; 
if (v_isShared_939_ == 0)
{
v___x_941_ = v___x_938_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v_a_936_);
v___x_941_ = v_reuseFailAlloc_942_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
return v___x_941_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_hasChar___boxed(lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_){
_start:
{
lean_object* v_res_956_; 
v_res_956_ = l_Lean_Meta_Grind_Arith_CommRing_hasChar(v_a_944_, v_a_945_, v_a_946_, v_a_947_, v_a_948_, v_a_949_, v_a_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_);
lean_dec(v_a_954_);
lean_dec_ref(v_a_953_);
lean_dec(v_a_952_);
lean_dec_ref(v_a_951_);
lean_dec(v_a_950_);
lean_dec_ref(v_a_949_);
lean_dec(v_a_948_);
lean_dec_ref(v_a_947_);
lean_dec(v_a_946_);
lean_dec(v_a_945_);
lean_dec_ref(v_a_944_);
return v_res_956_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__1(void){
_start:
{
lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_958_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__0));
v___x_959_ = l_Lean_stringToMessageData(v___x_958_);
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCharInst(lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_){
_start:
{
lean_object* v___x_972_; 
v___x_972_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
if (lean_obj_tag(v___x_972_) == 0)
{
lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_985_; 
v_a_973_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_985_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_985_ == 0)
{
v___x_975_ = v___x_972_;
v_isShared_976_ = v_isSharedCheck_985_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_a_973_);
lean_dec(v___x_972_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_985_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v_toRing_977_; lean_object* v_charInst_x3f_978_; 
v_toRing_977_ = lean_ctor_get(v_a_973_, 0);
lean_inc_ref(v_toRing_977_);
lean_dec(v_a_973_);
v_charInst_x3f_978_ = lean_ctor_get(v_toRing_977_, 5);
lean_inc(v_charInst_x3f_978_);
lean_dec_ref(v_toRing_977_);
if (lean_obj_tag(v_charInst_x3f_978_) == 1)
{
lean_object* v_val_979_; lean_object* v___x_981_; 
v_val_979_ = lean_ctor_get(v_charInst_x3f_978_, 0);
lean_inc(v_val_979_);
lean_dec_ref(v_charInst_x3f_978_);
if (v_isShared_976_ == 0)
{
lean_ctor_set(v___x_975_, 0, v_val_979_);
v___x_981_ = v___x_975_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v_val_979_);
v___x_981_ = v_reuseFailAlloc_982_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
return v___x_981_;
}
}
else
{
lean_object* v___x_983_; lean_object* v___x_984_; 
lean_dec(v_charInst_x3f_978_);
lean_del_object(v___x_975_);
v___x_983_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__1);
v___x_984_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg(v___x_983_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
return v___x_984_;
}
}
}
else
{
lean_object* v_a_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_993_; 
v_a_986_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_993_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_993_ == 0)
{
v___x_988_ = v___x_972_;
v_isShared_989_ = v_isSharedCheck_993_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_a_986_);
lean_dec(v___x_972_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_993_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v___x_991_; 
if (v_isShared_989_ == 0)
{
v___x_991_ = v___x_988_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v_a_986_);
v___x_991_ = v_reuseFailAlloc_992_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
return v___x_991_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCharInst___boxed(lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_){
_start:
{
lean_object* v_res_1006_; 
v_res_1006_ = l_Lean_Meta_Grind_Arith_CommRing_getCharInst(v_a_994_, v_a_995_, v_a_996_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_, v_a_1004_);
lean_dec(v_a_1004_);
lean_dec_ref(v_a_1003_);
lean_dec(v_a_1002_);
lean_dec_ref(v_a_1001_);
lean_dec(v_a_1000_);
lean_dec_ref(v_a_999_);
lean_dec(v_a_998_);
lean_dec_ref(v_a_997_);
lean_dec(v_a_996_);
lean_dec(v_a_995_);
lean_dec_ref(v_a_994_);
return v_res_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isField(lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_){
_start:
{
lean_object* v___x_1019_; 
v___x_1019_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_);
if (lean_obj_tag(v___x_1019_) == 0)
{
lean_object* v_a_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1035_; 
v_a_1020_ = lean_ctor_get(v___x_1019_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_1019_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1022_ = v___x_1019_;
v_isShared_1023_ = v_isSharedCheck_1035_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_a_1020_);
lean_dec(v___x_1019_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1035_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v_fieldInst_x3f_1024_; 
v_fieldInst_x3f_1024_ = lean_ctor_get(v_a_1020_, 6);
lean_inc(v_fieldInst_x3f_1024_);
lean_dec(v_a_1020_);
if (lean_obj_tag(v_fieldInst_x3f_1024_) == 0)
{
uint8_t v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1028_; 
v___x_1025_ = 0;
v___x_1026_ = lean_box(v___x_1025_);
if (v_isShared_1023_ == 0)
{
lean_ctor_set(v___x_1022_, 0, v___x_1026_);
v___x_1028_ = v___x_1022_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v___x_1026_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
else
{
uint8_t v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1033_; 
lean_dec_ref(v_fieldInst_x3f_1024_);
v___x_1030_ = 1;
v___x_1031_ = lean_box(v___x_1030_);
if (v_isShared_1023_ == 0)
{
lean_ctor_set(v___x_1022_, 0, v___x_1031_);
v___x_1033_ = v___x_1022_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v___x_1031_);
v___x_1033_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
return v___x_1033_;
}
}
}
}
else
{
lean_object* v_a_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1043_; 
v_a_1036_ = lean_ctor_get(v___x_1019_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_1019_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1038_ = v___x_1019_;
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_a_1036_);
lean_dec(v___x_1019_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1041_; 
if (v_isShared_1039_ == 0)
{
v___x_1041_ = v___x_1038_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_a_1036_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isField___boxed(lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l_Lean_Meta_Grind_Arith_CommRing_isField(v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_);
lean_dec(v_a_1054_);
lean_dec_ref(v_a_1053_);
lean_dec(v_a_1052_);
lean_dec_ref(v_a_1051_);
lean_dec(v_a_1050_);
lean_dec_ref(v_a_1049_);
lean_dec(v_a_1048_);
lean_dec_ref(v_a_1047_);
lean_dec(v_a_1046_);
lean_dec(v_a_1045_);
lean_dec_ref(v_a_1044_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty(lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_){
_start:
{
lean_object* v___x_1069_; 
v___x_1069_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1057_, v_a_1058_, v_a_1059_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_);
if (lean_obj_tag(v___x_1069_) == 0)
{
lean_object* v_a_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1085_; 
v_a_1070_ = lean_ctor_get(v___x_1069_, 0);
v_isSharedCheck_1085_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1072_ = v___x_1069_;
v_isShared_1073_ = v_isSharedCheck_1085_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_a_1070_);
lean_dec(v___x_1069_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1085_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v_queue_1074_; 
v_queue_1074_ = lean_ctor_get(v_a_1070_, 10);
lean_inc(v_queue_1074_);
lean_dec(v_a_1070_);
if (lean_obj_tag(v_queue_1074_) == 0)
{
uint8_t v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1078_; 
lean_dec_ref(v_queue_1074_);
v___x_1075_ = 0;
v___x_1076_ = lean_box(v___x_1075_);
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 0, v___x_1076_);
v___x_1078_ = v___x_1072_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v___x_1076_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
else
{
uint8_t v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1083_; 
v___x_1080_ = 1;
v___x_1081_ = lean_box(v___x_1080_);
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 0, v___x_1081_);
v___x_1083_ = v___x_1072_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v___x_1081_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
return v___x_1083_;
}
}
}
}
else
{
lean_object* v_a_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1093_; 
v_a_1086_ = lean_ctor_get(v___x_1069_, 0);
v_isSharedCheck_1093_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1088_ = v___x_1069_;
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_a_1086_);
lean_dec(v___x_1069_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1091_; 
if (v_isShared_1089_ == 0)
{
v___x_1091_ = v___x_1088_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_a_1086_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty___boxed(lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_){
_start:
{
lean_object* v_res_1106_; 
v_res_1106_ = l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty(v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_);
lean_dec(v_a_1104_);
lean_dec_ref(v_a_1103_);
lean_dec(v_a_1102_);
lean_dec_ref(v_a_1101_);
lean_dec(v_a_1100_);
lean_dec_ref(v_a_1099_);
lean_dec(v_a_1098_);
lean_dec_ref(v_a_1097_);
lean_dec(v_a_1096_);
lean_dec(v_a_1095_);
lean_dec_ref(v_a_1094_);
return v_res_1106_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(lean_object* v_k_1107_, lean_object* v_t_1108_){
_start:
{
if (lean_obj_tag(v_t_1108_) == 0)
{
lean_object* v_k_1109_; lean_object* v_v_1110_; lean_object* v_l_1111_; lean_object* v_r_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1766_; 
v_k_1109_ = lean_ctor_get(v_t_1108_, 1);
v_v_1110_ = lean_ctor_get(v_t_1108_, 2);
v_l_1111_ = lean_ctor_get(v_t_1108_, 3);
v_r_1112_ = lean_ctor_get(v_t_1108_, 4);
v_isSharedCheck_1766_ = !lean_is_exclusive(v_t_1108_);
if (v_isSharedCheck_1766_ == 0)
{
lean_object* v_unused_1767_; 
v_unused_1767_ = lean_ctor_get(v_t_1108_, 0);
lean_dec(v_unused_1767_);
v___x_1114_ = v_t_1108_;
v_isShared_1115_ = v_isSharedCheck_1766_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_r_1112_);
lean_inc(v_l_1111_);
lean_inc(v_v_1110_);
lean_inc(v_k_1109_);
lean_dec(v_t_1108_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1766_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
uint8_t v___x_1116_; 
v___x_1116_ = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_compare(v_k_1107_, v_k_1109_);
switch(v___x_1116_)
{
case 0:
{
lean_object* v_impl_1117_; lean_object* v___x_1118_; 
v_impl_1117_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_k_1107_, v_l_1111_);
v___x_1118_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1117_) == 0)
{
if (lean_obj_tag(v_r_1112_) == 0)
{
lean_object* v_size_1119_; lean_object* v_size_1120_; lean_object* v_k_1121_; lean_object* v_v_1122_; lean_object* v_l_1123_; lean_object* v_r_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; uint8_t v___x_1127_; 
v_size_1119_ = lean_ctor_get(v_impl_1117_, 0);
lean_inc(v_size_1119_);
v_size_1120_ = lean_ctor_get(v_r_1112_, 0);
v_k_1121_ = lean_ctor_get(v_r_1112_, 1);
v_v_1122_ = lean_ctor_get(v_r_1112_, 2);
v_l_1123_ = lean_ctor_get(v_r_1112_, 3);
lean_inc(v_l_1123_);
v_r_1124_ = lean_ctor_get(v_r_1112_, 4);
v___x_1125_ = lean_unsigned_to_nat(3u);
v___x_1126_ = lean_nat_mul(v___x_1125_, v_size_1119_);
v___x_1127_ = lean_nat_dec_lt(v___x_1126_, v_size_1120_);
lean_dec(v___x_1126_);
if (v___x_1127_ == 0)
{
lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1131_; 
lean_dec(v_l_1123_);
v___x_1128_ = lean_nat_add(v___x_1118_, v_size_1119_);
lean_dec(v_size_1119_);
v___x_1129_ = lean_nat_add(v___x_1128_, v_size_1120_);
lean_dec(v___x_1128_);
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 3, v_impl_1117_);
lean_ctor_set(v___x_1114_, 0, v___x_1129_);
v___x_1131_ = v___x_1114_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v___x_1129_);
lean_ctor_set(v_reuseFailAlloc_1132_, 1, v_k_1109_);
lean_ctor_set(v_reuseFailAlloc_1132_, 2, v_v_1110_);
lean_ctor_set(v_reuseFailAlloc_1132_, 3, v_impl_1117_);
lean_ctor_set(v_reuseFailAlloc_1132_, 4, v_r_1112_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
return v___x_1131_;
}
}
else
{
lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1196_; 
lean_inc(v_r_1124_);
lean_inc(v_v_1122_);
lean_inc(v_k_1121_);
lean_inc(v_size_1120_);
v_isSharedCheck_1196_ = !lean_is_exclusive(v_r_1112_);
if (v_isSharedCheck_1196_ == 0)
{
lean_object* v_unused_1197_; lean_object* v_unused_1198_; lean_object* v_unused_1199_; lean_object* v_unused_1200_; lean_object* v_unused_1201_; 
v_unused_1197_ = lean_ctor_get(v_r_1112_, 4);
lean_dec(v_unused_1197_);
v_unused_1198_ = lean_ctor_get(v_r_1112_, 3);
lean_dec(v_unused_1198_);
v_unused_1199_ = lean_ctor_get(v_r_1112_, 2);
lean_dec(v_unused_1199_);
v_unused_1200_ = lean_ctor_get(v_r_1112_, 1);
lean_dec(v_unused_1200_);
v_unused_1201_ = lean_ctor_get(v_r_1112_, 0);
lean_dec(v_unused_1201_);
v___x_1134_ = v_r_1112_;
v_isShared_1135_ = v_isSharedCheck_1196_;
goto v_resetjp_1133_;
}
else
{
lean_dec(v_r_1112_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1196_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v_size_1136_; lean_object* v_k_1137_; lean_object* v_v_1138_; lean_object* v_l_1139_; lean_object* v_r_1140_; lean_object* v_size_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; uint8_t v___x_1144_; 
v_size_1136_ = lean_ctor_get(v_l_1123_, 0);
v_k_1137_ = lean_ctor_get(v_l_1123_, 1);
v_v_1138_ = lean_ctor_get(v_l_1123_, 2);
v_l_1139_ = lean_ctor_get(v_l_1123_, 3);
v_r_1140_ = lean_ctor_get(v_l_1123_, 4);
v_size_1141_ = lean_ctor_get(v_r_1124_, 0);
v___x_1142_ = lean_unsigned_to_nat(2u);
v___x_1143_ = lean_nat_mul(v___x_1142_, v_size_1141_);
v___x_1144_ = lean_nat_dec_lt(v_size_1136_, v___x_1143_);
lean_dec(v___x_1143_);
if (v___x_1144_ == 0)
{
lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1172_; 
lean_inc(v_r_1140_);
lean_inc(v_l_1139_);
lean_inc(v_v_1138_);
lean_inc(v_k_1137_);
v_isSharedCheck_1172_ = !lean_is_exclusive(v_l_1123_);
if (v_isSharedCheck_1172_ == 0)
{
lean_object* v_unused_1173_; lean_object* v_unused_1174_; lean_object* v_unused_1175_; lean_object* v_unused_1176_; lean_object* v_unused_1177_; 
v_unused_1173_ = lean_ctor_get(v_l_1123_, 4);
lean_dec(v_unused_1173_);
v_unused_1174_ = lean_ctor_get(v_l_1123_, 3);
lean_dec(v_unused_1174_);
v_unused_1175_ = lean_ctor_get(v_l_1123_, 2);
lean_dec(v_unused_1175_);
v_unused_1176_ = lean_ctor_get(v_l_1123_, 1);
lean_dec(v_unused_1176_);
v_unused_1177_ = lean_ctor_get(v_l_1123_, 0);
lean_dec(v_unused_1177_);
v___x_1146_ = v_l_1123_;
v_isShared_1147_ = v_isSharedCheck_1172_;
goto v_resetjp_1145_;
}
else
{
lean_dec(v_l_1123_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1172_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___y_1151_; lean_object* v___y_1152_; lean_object* v___y_1153_; lean_object* v___y_1162_; 
v___x_1148_ = lean_nat_add(v___x_1118_, v_size_1119_);
lean_dec(v_size_1119_);
v___x_1149_ = lean_nat_add(v___x_1148_, v_size_1120_);
lean_dec(v_size_1120_);
if (lean_obj_tag(v_l_1139_) == 0)
{
lean_object* v_size_1170_; 
v_size_1170_ = lean_ctor_get(v_l_1139_, 0);
lean_inc(v_size_1170_);
v___y_1162_ = v_size_1170_;
goto v___jp_1161_;
}
else
{
lean_object* v___x_1171_; 
v___x_1171_ = lean_unsigned_to_nat(0u);
v___y_1162_ = v___x_1171_;
goto v___jp_1161_;
}
v___jp_1150_:
{
lean_object* v___x_1154_; lean_object* v___x_1156_; 
v___x_1154_ = lean_nat_add(v___y_1151_, v___y_1153_);
lean_dec(v___y_1153_);
lean_dec(v___y_1151_);
if (v_isShared_1147_ == 0)
{
lean_ctor_set(v___x_1146_, 4, v_r_1124_);
lean_ctor_set(v___x_1146_, 3, v_r_1140_);
lean_ctor_set(v___x_1146_, 2, v_v_1122_);
lean_ctor_set(v___x_1146_, 1, v_k_1121_);
lean_ctor_set(v___x_1146_, 0, v___x_1154_);
v___x_1156_ = v___x_1146_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v___x_1154_);
lean_ctor_set(v_reuseFailAlloc_1160_, 1, v_k_1121_);
lean_ctor_set(v_reuseFailAlloc_1160_, 2, v_v_1122_);
lean_ctor_set(v_reuseFailAlloc_1160_, 3, v_r_1140_);
lean_ctor_set(v_reuseFailAlloc_1160_, 4, v_r_1124_);
v___x_1156_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
lean_object* v___x_1158_; 
if (v_isShared_1135_ == 0)
{
lean_ctor_set(v___x_1134_, 4, v___x_1156_);
lean_ctor_set(v___x_1134_, 3, v___y_1152_);
lean_ctor_set(v___x_1134_, 2, v_v_1138_);
lean_ctor_set(v___x_1134_, 1, v_k_1137_);
lean_ctor_set(v___x_1134_, 0, v___x_1149_);
v___x_1158_ = v___x_1134_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v___x_1149_);
lean_ctor_set(v_reuseFailAlloc_1159_, 1, v_k_1137_);
lean_ctor_set(v_reuseFailAlloc_1159_, 2, v_v_1138_);
lean_ctor_set(v_reuseFailAlloc_1159_, 3, v___y_1152_);
lean_ctor_set(v_reuseFailAlloc_1159_, 4, v___x_1156_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
}
v___jp_1161_:
{
lean_object* v___x_1163_; lean_object* v___x_1165_; 
v___x_1163_ = lean_nat_add(v___x_1148_, v___y_1162_);
lean_dec(v___y_1162_);
lean_dec(v___x_1148_);
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 4, v_l_1139_);
lean_ctor_set(v___x_1114_, 3, v_impl_1117_);
lean_ctor_set(v___x_1114_, 0, v___x_1163_);
v___x_1165_ = v___x_1114_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v___x_1163_);
lean_ctor_set(v_reuseFailAlloc_1169_, 1, v_k_1109_);
lean_ctor_set(v_reuseFailAlloc_1169_, 2, v_v_1110_);
lean_ctor_set(v_reuseFailAlloc_1169_, 3, v_impl_1117_);
lean_ctor_set(v_reuseFailAlloc_1169_, 4, v_l_1139_);
v___x_1165_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
lean_object* v___x_1166_; 
v___x_1166_ = lean_nat_add(v___x_1118_, v_size_1141_);
if (lean_obj_tag(v_r_1140_) == 0)
{
lean_object* v_size_1167_; 
v_size_1167_ = lean_ctor_get(v_r_1140_, 0);
lean_inc(v_size_1167_);
v___y_1151_ = v___x_1166_;
v___y_1152_ = v___x_1165_;
v___y_1153_ = v_size_1167_;
goto v___jp_1150_;
}
else
{
lean_object* v___x_1168_; 
v___x_1168_ = lean_unsigned_to_nat(0u);
v___y_1151_ = v___x_1166_;
v___y_1152_ = v___x_1165_;
v___y_1153_ = v___x_1168_;
goto v___jp_1150_;
}
}
}
}
}
else
{
lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1182_; 
lean_del_object(v___x_1114_);
v___x_1178_ = lean_nat_add(v___x_1118_, v_size_1119_);
lean_dec(v_size_1119_);
v___x_1179_ = lean_nat_add(v___x_1178_, v_size_1120_);
lean_dec(v_size_1120_);
v___x_1180_ = lean_nat_add(v___x_1178_, v_size_1136_);
lean_dec(v___x_1178_);
lean_inc_ref(v_impl_1117_);
if (v_isShared_1135_ == 0)
{
lean_ctor_set(v___x_1134_, 4, v_l_1123_);
lean_ctor_set(v___x_1134_, 3, v_impl_1117_);
lean_ctor_set(v___x_1134_, 2, v_v_1110_);
lean_ctor_set(v___x_1134_, 1, v_k_1109_);
lean_ctor_set(v___x_1134_, 0, v___x_1180_);
v___x_1182_ = v___x_1134_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v___x_1180_);
lean_ctor_set(v_reuseFailAlloc_1195_, 1, v_k_1109_);
lean_ctor_set(v_reuseFailAlloc_1195_, 2, v_v_1110_);
lean_ctor_set(v_reuseFailAlloc_1195_, 3, v_impl_1117_);
lean_ctor_set(v_reuseFailAlloc_1195_, 4, v_l_1123_);
v___x_1182_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1189_; 
v_isSharedCheck_1189_ = !lean_is_exclusive(v_impl_1117_);
if (v_isSharedCheck_1189_ == 0)
{
lean_object* v_unused_1190_; lean_object* v_unused_1191_; lean_object* v_unused_1192_; lean_object* v_unused_1193_; lean_object* v_unused_1194_; 
v_unused_1190_ = lean_ctor_get(v_impl_1117_, 4);
lean_dec(v_unused_1190_);
v_unused_1191_ = lean_ctor_get(v_impl_1117_, 3);
lean_dec(v_unused_1191_);
v_unused_1192_ = lean_ctor_get(v_impl_1117_, 2);
lean_dec(v_unused_1192_);
v_unused_1193_ = lean_ctor_get(v_impl_1117_, 1);
lean_dec(v_unused_1193_);
v_unused_1194_ = lean_ctor_get(v_impl_1117_, 0);
lean_dec(v_unused_1194_);
v___x_1184_ = v_impl_1117_;
v_isShared_1185_ = v_isSharedCheck_1189_;
goto v_resetjp_1183_;
}
else
{
lean_dec(v_impl_1117_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1189_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v___x_1187_; 
if (v_isShared_1185_ == 0)
{
lean_ctor_set(v___x_1184_, 4, v_r_1124_);
lean_ctor_set(v___x_1184_, 3, v___x_1182_);
lean_ctor_set(v___x_1184_, 2, v_v_1122_);
lean_ctor_set(v___x_1184_, 1, v_k_1121_);
lean_ctor_set(v___x_1184_, 0, v___x_1179_);
v___x_1187_ = v___x_1184_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v___x_1179_);
lean_ctor_set(v_reuseFailAlloc_1188_, 1, v_k_1121_);
lean_ctor_set(v_reuseFailAlloc_1188_, 2, v_v_1122_);
lean_ctor_set(v_reuseFailAlloc_1188_, 3, v___x_1182_);
lean_ctor_set(v_reuseFailAlloc_1188_, 4, v_r_1124_);
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
}
else
{
lean_object* v_size_1202_; lean_object* v___x_1203_; lean_object* v___x_1205_; 
v_size_1202_ = lean_ctor_get(v_impl_1117_, 0);
lean_inc(v_size_1202_);
v___x_1203_ = lean_nat_add(v___x_1118_, v_size_1202_);
lean_dec(v_size_1202_);
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 3, v_impl_1117_);
lean_ctor_set(v___x_1114_, 0, v___x_1203_);
v___x_1205_ = v___x_1114_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v___x_1203_);
lean_ctor_set(v_reuseFailAlloc_1206_, 1, v_k_1109_);
lean_ctor_set(v_reuseFailAlloc_1206_, 2, v_v_1110_);
lean_ctor_set(v_reuseFailAlloc_1206_, 3, v_impl_1117_);
lean_ctor_set(v_reuseFailAlloc_1206_, 4, v_r_1112_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
}
else
{
if (lean_obj_tag(v_r_1112_) == 0)
{
lean_object* v_l_1207_; 
v_l_1207_ = lean_ctor_get(v_r_1112_, 3);
lean_inc(v_l_1207_);
if (lean_obj_tag(v_l_1207_) == 0)
{
lean_object* v_r_1208_; 
v_r_1208_ = lean_ctor_get(v_r_1112_, 4);
lean_inc(v_r_1208_);
if (lean_obj_tag(v_r_1208_) == 0)
{
lean_object* v_size_1209_; lean_object* v_k_1210_; lean_object* v_v_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1224_; 
v_size_1209_ = lean_ctor_get(v_r_1112_, 0);
v_k_1210_ = lean_ctor_get(v_r_1112_, 1);
v_v_1211_ = lean_ctor_get(v_r_1112_, 2);
v_isSharedCheck_1224_ = !lean_is_exclusive(v_r_1112_);
if (v_isSharedCheck_1224_ == 0)
{
lean_object* v_unused_1225_; lean_object* v_unused_1226_; 
v_unused_1225_ = lean_ctor_get(v_r_1112_, 4);
lean_dec(v_unused_1225_);
v_unused_1226_ = lean_ctor_get(v_r_1112_, 3);
lean_dec(v_unused_1226_);
v___x_1213_ = v_r_1112_;
v_isShared_1214_ = v_isSharedCheck_1224_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_v_1211_);
lean_inc(v_k_1210_);
lean_inc(v_size_1209_);
lean_dec(v_r_1112_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1224_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v_size_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1219_; 
v_size_1215_ = lean_ctor_get(v_l_1207_, 0);
v___x_1216_ = lean_nat_add(v___x_1118_, v_size_1209_);
lean_dec(v_size_1209_);
v___x_1217_ = lean_nat_add(v___x_1118_, v_size_1215_);
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 4, v_l_1207_);
lean_ctor_set(v___x_1213_, 3, v_impl_1117_);
lean_ctor_set(v___x_1213_, 2, v_v_1110_);
lean_ctor_set(v___x_1213_, 1, v_k_1109_);
lean_ctor_set(v___x_1213_, 0, v___x_1217_);
v___x_1219_ = v___x_1213_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v___x_1217_);
lean_ctor_set(v_reuseFailAlloc_1223_, 1, v_k_1109_);
lean_ctor_set(v_reuseFailAlloc_1223_, 2, v_v_1110_);
lean_ctor_set(v_reuseFailAlloc_1223_, 3, v_impl_1117_);
lean_ctor_set(v_reuseFailAlloc_1223_, 4, v_l_1207_);
v___x_1219_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
lean_object* v___x_1221_; 
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 4, v_r_1208_);
lean_ctor_set(v___x_1114_, 3, v___x_1219_);
lean_ctor_set(v___x_1114_, 2, v_v_1211_);
lean_ctor_set(v___x_1114_, 1, v_k_1210_);
lean_ctor_set(v___x_1114_, 0, v___x_1216_);
v___x_1221_ = v___x_1114_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v___x_1216_);
lean_ctor_set(v_reuseFailAlloc_1222_, 1, v_k_1210_);
lean_ctor_set(v_reuseFailAlloc_1222_, 2, v_v_1211_);
lean_ctor_set(v_reuseFailAlloc_1222_, 3, v___x_1219_);
lean_ctor_set(v_reuseFailAlloc_1222_, 4, v_r_1208_);
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
lean_object* v_k_1227_; lean_object* v_v_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1251_; 
v_k_1227_ = lean_ctor_get(v_r_1112_, 1);
v_v_1228_ = lean_ctor_get(v_r_1112_, 2);
v_isSharedCheck_1251_ = !lean_is_exclusive(v_r_1112_);
if (v_isSharedCheck_1251_ == 0)
{
lean_object* v_unused_1252_; lean_object* v_unused_1253_; lean_object* v_unused_1254_; 
v_unused_1252_ = lean_ctor_get(v_r_1112_, 4);
lean_dec(v_unused_1252_);
v_unused_1253_ = lean_ctor_get(v_r_1112_, 3);
lean_dec(v_unused_1253_);
v_unused_1254_ = lean_ctor_get(v_r_1112_, 0);
lean_dec(v_unused_1254_);
v___x_1230_ = v_r_1112_;
v_isShared_1231_ = v_isSharedCheck_1251_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_v_1228_);
lean_inc(v_k_1227_);
lean_dec(v_r_1112_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1251_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v_k_1232_; lean_object* v_v_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1247_; 
v_k_1232_ = lean_ctor_get(v_l_1207_, 1);
v_v_1233_ = lean_ctor_get(v_l_1207_, 2);
v_isSharedCheck_1247_ = !lean_is_exclusive(v_l_1207_);
if (v_isSharedCheck_1247_ == 0)
{
lean_object* v_unused_1248_; lean_object* v_unused_1249_; lean_object* v_unused_1250_; 
v_unused_1248_ = lean_ctor_get(v_l_1207_, 4);
lean_dec(v_unused_1248_);
v_unused_1249_ = lean_ctor_get(v_l_1207_, 3);
lean_dec(v_unused_1249_);
v_unused_1250_ = lean_ctor_get(v_l_1207_, 0);
lean_dec(v_unused_1250_);
v___x_1235_ = v_l_1207_;
v_isShared_1236_ = v_isSharedCheck_1247_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_v_1233_);
lean_inc(v_k_1232_);
lean_dec(v_l_1207_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1247_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v___x_1237_; lean_object* v___x_1239_; 
v___x_1237_ = lean_unsigned_to_nat(3u);
if (v_isShared_1236_ == 0)
{
lean_ctor_set(v___x_1235_, 4, v_r_1208_);
lean_ctor_set(v___x_1235_, 3, v_r_1208_);
lean_ctor_set(v___x_1235_, 2, v_v_1110_);
lean_ctor_set(v___x_1235_, 1, v_k_1109_);
lean_ctor_set(v___x_1235_, 0, v___x_1118_);
v___x_1239_ = v___x_1235_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v___x_1118_);
lean_ctor_set(v_reuseFailAlloc_1246_, 1, v_k_1109_);
lean_ctor_set(v_reuseFailAlloc_1246_, 2, v_v_1110_);
lean_ctor_set(v_reuseFailAlloc_1246_, 3, v_r_1208_);
lean_ctor_set(v_reuseFailAlloc_1246_, 4, v_r_1208_);
v___x_1239_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
lean_object* v___x_1241_; 
if (v_isShared_1231_ == 0)
{
lean_ctor_set(v___x_1230_, 3, v_r_1208_);
lean_ctor_set(v___x_1230_, 0, v___x_1118_);
v___x_1241_ = v___x_1230_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v___x_1118_);
lean_ctor_set(v_reuseFailAlloc_1245_, 1, v_k_1227_);
lean_ctor_set(v_reuseFailAlloc_1245_, 2, v_v_1228_);
lean_ctor_set(v_reuseFailAlloc_1245_, 3, v_r_1208_);
lean_ctor_set(v_reuseFailAlloc_1245_, 4, v_r_1208_);
v___x_1241_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
lean_object* v___x_1243_; 
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 4, v___x_1241_);
lean_ctor_set(v___x_1114_, 3, v___x_1239_);
lean_ctor_set(v___x_1114_, 2, v_v_1233_);
lean_ctor_set(v___x_1114_, 1, v_k_1232_);
lean_ctor_set(v___x_1114_, 0, v___x_1237_);
v___x_1243_ = v___x_1114_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v___x_1237_);
lean_ctor_set(v_reuseFailAlloc_1244_, 1, v_k_1232_);
lean_ctor_set(v_reuseFailAlloc_1244_, 2, v_v_1233_);
lean_ctor_set(v_reuseFailAlloc_1244_, 3, v___x_1239_);
lean_ctor_set(v_reuseFailAlloc_1244_, 4, v___x_1241_);
v___x_1243_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
return v___x_1243_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_1255_; 
v_r_1255_ = lean_ctor_get(v_r_1112_, 4);
lean_inc(v_r_1255_);
if (lean_obj_tag(v_r_1255_) == 0)
{
lean_object* v_k_1256_; lean_object* v_v_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1268_; 
v_k_1256_ = lean_ctor_get(v_r_1112_, 1);
v_v_1257_ = lean_ctor_get(v_r_1112_, 2);
v_isSharedCheck_1268_ = !lean_is_exclusive(v_r_1112_);
if (v_isSharedCheck_1268_ == 0)
{
lean_object* v_unused_1269_; lean_object* v_unused_1270_; lean_object* v_unused_1271_; 
v_unused_1269_ = lean_ctor_get(v_r_1112_, 4);
lean_dec(v_unused_1269_);
v_unused_1270_ = lean_ctor_get(v_r_1112_, 3);
lean_dec(v_unused_1270_);
v_unused_1271_ = lean_ctor_get(v_r_1112_, 0);
lean_dec(v_unused_1271_);
v___x_1259_ = v_r_1112_;
v_isShared_1260_ = v_isSharedCheck_1268_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_v_1257_);
lean_inc(v_k_1256_);
lean_dec(v_r_1112_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1268_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1261_; lean_object* v___x_1263_; 
v___x_1261_ = lean_unsigned_to_nat(3u);
if (v_isShared_1260_ == 0)
{
lean_ctor_set(v___x_1259_, 4, v_l_1207_);
lean_ctor_set(v___x_1259_, 2, v_v_1110_);
lean_ctor_set(v___x_1259_, 1, v_k_1109_);
lean_ctor_set(v___x_1259_, 0, v___x_1118_);
v___x_1263_ = v___x_1259_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v___x_1118_);
lean_ctor_set(v_reuseFailAlloc_1267_, 1, v_k_1109_);
lean_ctor_set(v_reuseFailAlloc_1267_, 2, v_v_1110_);
lean_ctor_set(v_reuseFailAlloc_1267_, 3, v_l_1207_);
lean_ctor_set(v_reuseFailAlloc_1267_, 4, v_l_1207_);
v___x_1263_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
lean_object* v___x_1265_; 
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 4, v_r_1255_);
lean_ctor_set(v___x_1114_, 3, v___x_1263_);
lean_ctor_set(v___x_1114_, 2, v_v_1257_);
lean_ctor_set(v___x_1114_, 1, v_k_1256_);
lean_ctor_set(v___x_1114_, 0, v___x_1261_);
v___x_1265_ = v___x_1114_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v___x_1261_);
lean_ctor_set(v_reuseFailAlloc_1266_, 1, v_k_1256_);
lean_ctor_set(v_reuseFailAlloc_1266_, 2, v_v_1257_);
lean_ctor_set(v_reuseFailAlloc_1266_, 3, v___x_1263_);
lean_ctor_set(v_reuseFailAlloc_1266_, 4, v_r_1255_);
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
lean_object* v_size_1272_; lean_object* v_k_1273_; lean_object* v_v_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1285_; 
v_size_1272_ = lean_ctor_get(v_r_1112_, 0);
v_k_1273_ = lean_ctor_get(v_r_1112_, 1);
v_v_1274_ = lean_ctor_get(v_r_1112_, 2);
v_isSharedCheck_1285_ = !lean_is_exclusive(v_r_1112_);
if (v_isSharedCheck_1285_ == 0)
{
lean_object* v_unused_1286_; lean_object* v_unused_1287_; 
v_unused_1286_ = lean_ctor_get(v_r_1112_, 4);
lean_dec(v_unused_1286_);
v_unused_1287_ = lean_ctor_get(v_r_1112_, 3);
lean_dec(v_unused_1287_);
v___x_1276_ = v_r_1112_;
v_isShared_1277_ = v_isSharedCheck_1285_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_v_1274_);
lean_inc(v_k_1273_);
lean_inc(v_size_1272_);
lean_dec(v_r_1112_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1285_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v___x_1279_; 
if (v_isShared_1277_ == 0)
{
lean_ctor_set(v___x_1276_, 3, v_r_1255_);
v___x_1279_ = v___x_1276_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_size_1272_);
lean_ctor_set(v_reuseFailAlloc_1284_, 1, v_k_1273_);
lean_ctor_set(v_reuseFailAlloc_1284_, 2, v_v_1274_);
lean_ctor_set(v_reuseFailAlloc_1284_, 3, v_r_1255_);
lean_ctor_set(v_reuseFailAlloc_1284_, 4, v_r_1255_);
v___x_1279_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
lean_object* v___x_1280_; lean_object* v___x_1282_; 
v___x_1280_ = lean_unsigned_to_nat(2u);
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 4, v___x_1279_);
lean_ctor_set(v___x_1114_, 3, v_r_1255_);
lean_ctor_set(v___x_1114_, 0, v___x_1280_);
v___x_1282_ = v___x_1114_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v___x_1280_);
lean_ctor_set(v_reuseFailAlloc_1283_, 1, v_k_1109_);
lean_ctor_set(v_reuseFailAlloc_1283_, 2, v_v_1110_);
lean_ctor_set(v_reuseFailAlloc_1283_, 3, v_r_1255_);
lean_ctor_set(v_reuseFailAlloc_1283_, 4, v___x_1279_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
return v___x_1282_;
}
}
}
}
}
}
else
{
lean_object* v___x_1289_; 
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 3, v_r_1112_);
lean_ctor_set(v___x_1114_, 0, v___x_1118_);
v___x_1289_ = v___x_1114_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v___x_1118_);
lean_ctor_set(v_reuseFailAlloc_1290_, 1, v_k_1109_);
lean_ctor_set(v_reuseFailAlloc_1290_, 2, v_v_1110_);
lean_ctor_set(v_reuseFailAlloc_1290_, 3, v_r_1112_);
lean_ctor_set(v_reuseFailAlloc_1290_, 4, v_r_1112_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
}
case 1:
{
lean_del_object(v___x_1114_);
lean_dec(v_v_1110_);
lean_dec(v_k_1109_);
if (lean_obj_tag(v_l_1111_) == 0)
{
if (lean_obj_tag(v_r_1112_) == 0)
{
lean_object* v_size_1291_; lean_object* v_k_1292_; lean_object* v_v_1293_; lean_object* v_l_1294_; lean_object* v_r_1295_; lean_object* v_size_1296_; lean_object* v_k_1297_; lean_object* v_v_1298_; lean_object* v_l_1299_; lean_object* v_r_1300_; lean_object* v___x_1301_; uint8_t v___x_1302_; 
v_size_1291_ = lean_ctor_get(v_l_1111_, 0);
v_k_1292_ = lean_ctor_get(v_l_1111_, 1);
v_v_1293_ = lean_ctor_get(v_l_1111_, 2);
v_l_1294_ = lean_ctor_get(v_l_1111_, 3);
v_r_1295_ = lean_ctor_get(v_l_1111_, 4);
lean_inc(v_r_1295_);
v_size_1296_ = lean_ctor_get(v_r_1112_, 0);
v_k_1297_ = lean_ctor_get(v_r_1112_, 1);
v_v_1298_ = lean_ctor_get(v_r_1112_, 2);
v_l_1299_ = lean_ctor_get(v_r_1112_, 3);
lean_inc(v_l_1299_);
v_r_1300_ = lean_ctor_get(v_r_1112_, 4);
v___x_1301_ = lean_unsigned_to_nat(1u);
v___x_1302_ = lean_nat_dec_lt(v_size_1291_, v_size_1296_);
if (v___x_1302_ == 0)
{
lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1438_; 
lean_inc(v_l_1294_);
lean_inc(v_v_1293_);
lean_inc(v_k_1292_);
v_isSharedCheck_1438_ = !lean_is_exclusive(v_l_1111_);
if (v_isSharedCheck_1438_ == 0)
{
lean_object* v_unused_1439_; lean_object* v_unused_1440_; lean_object* v_unused_1441_; lean_object* v_unused_1442_; lean_object* v_unused_1443_; 
v_unused_1439_ = lean_ctor_get(v_l_1111_, 4);
lean_dec(v_unused_1439_);
v_unused_1440_ = lean_ctor_get(v_l_1111_, 3);
lean_dec(v_unused_1440_);
v_unused_1441_ = lean_ctor_get(v_l_1111_, 2);
lean_dec(v_unused_1441_);
v_unused_1442_ = lean_ctor_get(v_l_1111_, 1);
lean_dec(v_unused_1442_);
v_unused_1443_ = lean_ctor_get(v_l_1111_, 0);
lean_dec(v_unused_1443_);
v___x_1304_ = v_l_1111_;
v_isShared_1305_ = v_isSharedCheck_1438_;
goto v_resetjp_1303_;
}
else
{
lean_dec(v_l_1111_);
v___x_1304_ = lean_box(0);
v_isShared_1305_ = v_isSharedCheck_1438_;
goto v_resetjp_1303_;
}
v_resetjp_1303_:
{
lean_object* v___x_1306_; lean_object* v_tree_1307_; 
v___x_1306_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_1292_, v_v_1293_, v_l_1294_, v_r_1295_);
v_tree_1307_ = lean_ctor_get(v___x_1306_, 2);
lean_inc(v_tree_1307_);
if (lean_obj_tag(v_tree_1307_) == 0)
{
lean_object* v_k_1308_; lean_object* v_v_1309_; lean_object* v_size_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; uint8_t v___x_1313_; 
v_k_1308_ = lean_ctor_get(v___x_1306_, 0);
lean_inc(v_k_1308_);
v_v_1309_ = lean_ctor_get(v___x_1306_, 1);
lean_inc(v_v_1309_);
lean_dec_ref(v___x_1306_);
v_size_1310_ = lean_ctor_get(v_tree_1307_, 0);
v___x_1311_ = lean_unsigned_to_nat(3u);
v___x_1312_ = lean_nat_mul(v___x_1311_, v_size_1310_);
v___x_1313_ = lean_nat_dec_lt(v___x_1312_, v_size_1296_);
lean_dec(v___x_1312_);
if (v___x_1313_ == 0)
{
lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1317_; 
lean_dec(v_l_1299_);
v___x_1314_ = lean_nat_add(v___x_1301_, v_size_1310_);
v___x_1315_ = lean_nat_add(v___x_1314_, v_size_1296_);
lean_dec(v___x_1314_);
if (v_isShared_1305_ == 0)
{
lean_ctor_set(v___x_1304_, 4, v_r_1112_);
lean_ctor_set(v___x_1304_, 3, v_tree_1307_);
lean_ctor_set(v___x_1304_, 2, v_v_1309_);
lean_ctor_set(v___x_1304_, 1, v_k_1308_);
lean_ctor_set(v___x_1304_, 0, v___x_1315_);
v___x_1317_ = v___x_1304_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v___x_1315_);
lean_ctor_set(v_reuseFailAlloc_1318_, 1, v_k_1308_);
lean_ctor_set(v_reuseFailAlloc_1318_, 2, v_v_1309_);
lean_ctor_set(v_reuseFailAlloc_1318_, 3, v_tree_1307_);
lean_ctor_set(v_reuseFailAlloc_1318_, 4, v_r_1112_);
v___x_1317_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
return v___x_1317_;
}
}
else
{
lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1373_; 
lean_inc(v_r_1300_);
lean_inc(v_v_1298_);
lean_inc(v_k_1297_);
lean_inc(v_size_1296_);
v_isSharedCheck_1373_ = !lean_is_exclusive(v_r_1112_);
if (v_isSharedCheck_1373_ == 0)
{
lean_object* v_unused_1374_; lean_object* v_unused_1375_; lean_object* v_unused_1376_; lean_object* v_unused_1377_; lean_object* v_unused_1378_; 
v_unused_1374_ = lean_ctor_get(v_r_1112_, 4);
lean_dec(v_unused_1374_);
v_unused_1375_ = lean_ctor_get(v_r_1112_, 3);
lean_dec(v_unused_1375_);
v_unused_1376_ = lean_ctor_get(v_r_1112_, 2);
lean_dec(v_unused_1376_);
v_unused_1377_ = lean_ctor_get(v_r_1112_, 1);
lean_dec(v_unused_1377_);
v_unused_1378_ = lean_ctor_get(v_r_1112_, 0);
lean_dec(v_unused_1378_);
v___x_1320_ = v_r_1112_;
v_isShared_1321_ = v_isSharedCheck_1373_;
goto v_resetjp_1319_;
}
else
{
lean_dec(v_r_1112_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1373_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v_size_1322_; lean_object* v_k_1323_; lean_object* v_v_1324_; lean_object* v_l_1325_; lean_object* v_r_1326_; lean_object* v_size_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; uint8_t v___x_1330_; 
v_size_1322_ = lean_ctor_get(v_l_1299_, 0);
v_k_1323_ = lean_ctor_get(v_l_1299_, 1);
v_v_1324_ = lean_ctor_get(v_l_1299_, 2);
v_l_1325_ = lean_ctor_get(v_l_1299_, 3);
v_r_1326_ = lean_ctor_get(v_l_1299_, 4);
v_size_1327_ = lean_ctor_get(v_r_1300_, 0);
v___x_1328_ = lean_unsigned_to_nat(2u);
v___x_1329_ = lean_nat_mul(v___x_1328_, v_size_1327_);
v___x_1330_ = lean_nat_dec_lt(v_size_1322_, v___x_1329_);
lean_dec(v___x_1329_);
if (v___x_1330_ == 0)
{
lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1358_; 
lean_inc(v_r_1326_);
lean_inc(v_l_1325_);
lean_inc(v_v_1324_);
lean_inc(v_k_1323_);
v_isSharedCheck_1358_ = !lean_is_exclusive(v_l_1299_);
if (v_isSharedCheck_1358_ == 0)
{
lean_object* v_unused_1359_; lean_object* v_unused_1360_; lean_object* v_unused_1361_; lean_object* v_unused_1362_; lean_object* v_unused_1363_; 
v_unused_1359_ = lean_ctor_get(v_l_1299_, 4);
lean_dec(v_unused_1359_);
v_unused_1360_ = lean_ctor_get(v_l_1299_, 3);
lean_dec(v_unused_1360_);
v_unused_1361_ = lean_ctor_get(v_l_1299_, 2);
lean_dec(v_unused_1361_);
v_unused_1362_ = lean_ctor_get(v_l_1299_, 1);
lean_dec(v_unused_1362_);
v_unused_1363_ = lean_ctor_get(v_l_1299_, 0);
lean_dec(v_unused_1363_);
v___x_1332_ = v_l_1299_;
v_isShared_1333_ = v_isSharedCheck_1358_;
goto v_resetjp_1331_;
}
else
{
lean_dec(v_l_1299_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1358_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___y_1337_; lean_object* v___y_1338_; lean_object* v___y_1339_; lean_object* v___y_1348_; 
v___x_1334_ = lean_nat_add(v___x_1301_, v_size_1310_);
v___x_1335_ = lean_nat_add(v___x_1334_, v_size_1296_);
lean_dec(v_size_1296_);
if (lean_obj_tag(v_l_1325_) == 0)
{
lean_object* v_size_1356_; 
v_size_1356_ = lean_ctor_get(v_l_1325_, 0);
lean_inc(v_size_1356_);
v___y_1348_ = v_size_1356_;
goto v___jp_1347_;
}
else
{
lean_object* v___x_1357_; 
v___x_1357_ = lean_unsigned_to_nat(0u);
v___y_1348_ = v___x_1357_;
goto v___jp_1347_;
}
v___jp_1336_:
{
lean_object* v___x_1340_; lean_object* v___x_1342_; 
v___x_1340_ = lean_nat_add(v___y_1337_, v___y_1339_);
lean_dec(v___y_1339_);
lean_dec(v___y_1337_);
if (v_isShared_1333_ == 0)
{
lean_ctor_set(v___x_1332_, 4, v_r_1300_);
lean_ctor_set(v___x_1332_, 3, v_r_1326_);
lean_ctor_set(v___x_1332_, 2, v_v_1298_);
lean_ctor_set(v___x_1332_, 1, v_k_1297_);
lean_ctor_set(v___x_1332_, 0, v___x_1340_);
v___x_1342_ = v___x_1332_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v___x_1340_);
lean_ctor_set(v_reuseFailAlloc_1346_, 1, v_k_1297_);
lean_ctor_set(v_reuseFailAlloc_1346_, 2, v_v_1298_);
lean_ctor_set(v_reuseFailAlloc_1346_, 3, v_r_1326_);
lean_ctor_set(v_reuseFailAlloc_1346_, 4, v_r_1300_);
v___x_1342_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
lean_object* v___x_1344_; 
if (v_isShared_1321_ == 0)
{
lean_ctor_set(v___x_1320_, 4, v___x_1342_);
lean_ctor_set(v___x_1320_, 3, v___y_1338_);
lean_ctor_set(v___x_1320_, 2, v_v_1324_);
lean_ctor_set(v___x_1320_, 1, v_k_1323_);
lean_ctor_set(v___x_1320_, 0, v___x_1335_);
v___x_1344_ = v___x_1320_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v___x_1335_);
lean_ctor_set(v_reuseFailAlloc_1345_, 1, v_k_1323_);
lean_ctor_set(v_reuseFailAlloc_1345_, 2, v_v_1324_);
lean_ctor_set(v_reuseFailAlloc_1345_, 3, v___y_1338_);
lean_ctor_set(v_reuseFailAlloc_1345_, 4, v___x_1342_);
v___x_1344_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
return v___x_1344_;
}
}
}
v___jp_1347_:
{
lean_object* v___x_1349_; lean_object* v___x_1351_; 
v___x_1349_ = lean_nat_add(v___x_1334_, v___y_1348_);
lean_dec(v___y_1348_);
lean_dec(v___x_1334_);
if (v_isShared_1305_ == 0)
{
lean_ctor_set(v___x_1304_, 4, v_l_1325_);
lean_ctor_set(v___x_1304_, 3, v_tree_1307_);
lean_ctor_set(v___x_1304_, 2, v_v_1309_);
lean_ctor_set(v___x_1304_, 1, v_k_1308_);
lean_ctor_set(v___x_1304_, 0, v___x_1349_);
v___x_1351_ = v___x_1304_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v___x_1349_);
lean_ctor_set(v_reuseFailAlloc_1355_, 1, v_k_1308_);
lean_ctor_set(v_reuseFailAlloc_1355_, 2, v_v_1309_);
lean_ctor_set(v_reuseFailAlloc_1355_, 3, v_tree_1307_);
lean_ctor_set(v_reuseFailAlloc_1355_, 4, v_l_1325_);
v___x_1351_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
lean_object* v___x_1352_; 
v___x_1352_ = lean_nat_add(v___x_1301_, v_size_1327_);
if (lean_obj_tag(v_r_1326_) == 0)
{
lean_object* v_size_1353_; 
v_size_1353_ = lean_ctor_get(v_r_1326_, 0);
lean_inc(v_size_1353_);
v___y_1337_ = v___x_1352_;
v___y_1338_ = v___x_1351_;
v___y_1339_ = v_size_1353_;
goto v___jp_1336_;
}
else
{
lean_object* v___x_1354_; 
v___x_1354_ = lean_unsigned_to_nat(0u);
v___y_1337_ = v___x_1352_;
v___y_1338_ = v___x_1351_;
v___y_1339_ = v___x_1354_;
goto v___jp_1336_;
}
}
}
}
}
else
{
lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1368_; 
v___x_1364_ = lean_nat_add(v___x_1301_, v_size_1310_);
v___x_1365_ = lean_nat_add(v___x_1364_, v_size_1296_);
lean_dec(v_size_1296_);
v___x_1366_ = lean_nat_add(v___x_1364_, v_size_1322_);
lean_dec(v___x_1364_);
if (v_isShared_1321_ == 0)
{
lean_ctor_set(v___x_1320_, 4, v_l_1299_);
lean_ctor_set(v___x_1320_, 3, v_tree_1307_);
lean_ctor_set(v___x_1320_, 2, v_v_1309_);
lean_ctor_set(v___x_1320_, 1, v_k_1308_);
lean_ctor_set(v___x_1320_, 0, v___x_1366_);
v___x_1368_ = v___x_1320_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v___x_1366_);
lean_ctor_set(v_reuseFailAlloc_1372_, 1, v_k_1308_);
lean_ctor_set(v_reuseFailAlloc_1372_, 2, v_v_1309_);
lean_ctor_set(v_reuseFailAlloc_1372_, 3, v_tree_1307_);
lean_ctor_set(v_reuseFailAlloc_1372_, 4, v_l_1299_);
v___x_1368_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
lean_object* v___x_1370_; 
if (v_isShared_1305_ == 0)
{
lean_ctor_set(v___x_1304_, 4, v_r_1300_);
lean_ctor_set(v___x_1304_, 3, v___x_1368_);
lean_ctor_set(v___x_1304_, 2, v_v_1298_);
lean_ctor_set(v___x_1304_, 1, v_k_1297_);
lean_ctor_set(v___x_1304_, 0, v___x_1365_);
v___x_1370_ = v___x_1304_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v___x_1365_);
lean_ctor_set(v_reuseFailAlloc_1371_, 1, v_k_1297_);
lean_ctor_set(v_reuseFailAlloc_1371_, 2, v_v_1298_);
lean_ctor_set(v_reuseFailAlloc_1371_, 3, v___x_1368_);
lean_ctor_set(v_reuseFailAlloc_1371_, 4, v_r_1300_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
}
}
}
}
else
{
lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1432_; 
lean_inc(v_r_1300_);
lean_inc(v_v_1298_);
lean_inc(v_k_1297_);
lean_inc(v_size_1296_);
v_isSharedCheck_1432_ = !lean_is_exclusive(v_r_1112_);
if (v_isSharedCheck_1432_ == 0)
{
lean_object* v_unused_1433_; lean_object* v_unused_1434_; lean_object* v_unused_1435_; lean_object* v_unused_1436_; lean_object* v_unused_1437_; 
v_unused_1433_ = lean_ctor_get(v_r_1112_, 4);
lean_dec(v_unused_1433_);
v_unused_1434_ = lean_ctor_get(v_r_1112_, 3);
lean_dec(v_unused_1434_);
v_unused_1435_ = lean_ctor_get(v_r_1112_, 2);
lean_dec(v_unused_1435_);
v_unused_1436_ = lean_ctor_get(v_r_1112_, 1);
lean_dec(v_unused_1436_);
v_unused_1437_ = lean_ctor_get(v_r_1112_, 0);
lean_dec(v_unused_1437_);
v___x_1380_ = v_r_1112_;
v_isShared_1381_ = v_isSharedCheck_1432_;
goto v_resetjp_1379_;
}
else
{
lean_dec(v_r_1112_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1432_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
if (lean_obj_tag(v_l_1299_) == 0)
{
if (lean_obj_tag(v_r_1300_) == 0)
{
lean_object* v_k_1382_; lean_object* v_v_1383_; lean_object* v_size_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1388_; 
v_k_1382_ = lean_ctor_get(v___x_1306_, 0);
lean_inc(v_k_1382_);
v_v_1383_ = lean_ctor_get(v___x_1306_, 1);
lean_inc(v_v_1383_);
lean_dec_ref(v___x_1306_);
v_size_1384_ = lean_ctor_get(v_l_1299_, 0);
v___x_1385_ = lean_nat_add(v___x_1301_, v_size_1296_);
lean_dec(v_size_1296_);
v___x_1386_ = lean_nat_add(v___x_1301_, v_size_1384_);
if (v_isShared_1381_ == 0)
{
lean_ctor_set(v___x_1380_, 4, v_l_1299_);
lean_ctor_set(v___x_1380_, 3, v_tree_1307_);
lean_ctor_set(v___x_1380_, 2, v_v_1383_);
lean_ctor_set(v___x_1380_, 1, v_k_1382_);
lean_ctor_set(v___x_1380_, 0, v___x_1386_);
v___x_1388_ = v___x_1380_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v___x_1386_);
lean_ctor_set(v_reuseFailAlloc_1392_, 1, v_k_1382_);
lean_ctor_set(v_reuseFailAlloc_1392_, 2, v_v_1383_);
lean_ctor_set(v_reuseFailAlloc_1392_, 3, v_tree_1307_);
lean_ctor_set(v_reuseFailAlloc_1392_, 4, v_l_1299_);
v___x_1388_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
lean_object* v___x_1390_; 
if (v_isShared_1305_ == 0)
{
lean_ctor_set(v___x_1304_, 4, v_r_1300_);
lean_ctor_set(v___x_1304_, 3, v___x_1388_);
lean_ctor_set(v___x_1304_, 2, v_v_1298_);
lean_ctor_set(v___x_1304_, 1, v_k_1297_);
lean_ctor_set(v___x_1304_, 0, v___x_1385_);
v___x_1390_ = v___x_1304_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v___x_1385_);
lean_ctor_set(v_reuseFailAlloc_1391_, 1, v_k_1297_);
lean_ctor_set(v_reuseFailAlloc_1391_, 2, v_v_1298_);
lean_ctor_set(v_reuseFailAlloc_1391_, 3, v___x_1388_);
lean_ctor_set(v_reuseFailAlloc_1391_, 4, v_r_1300_);
v___x_1390_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
return v___x_1390_;
}
}
}
else
{
lean_object* v_k_1393_; lean_object* v_v_1394_; lean_object* v_k_1395_; lean_object* v_v_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1410_; 
lean_dec(v_size_1296_);
v_k_1393_ = lean_ctor_get(v___x_1306_, 0);
lean_inc(v_k_1393_);
v_v_1394_ = lean_ctor_get(v___x_1306_, 1);
lean_inc(v_v_1394_);
lean_dec_ref(v___x_1306_);
v_k_1395_ = lean_ctor_get(v_l_1299_, 1);
v_v_1396_ = lean_ctor_get(v_l_1299_, 2);
v_isSharedCheck_1410_ = !lean_is_exclusive(v_l_1299_);
if (v_isSharedCheck_1410_ == 0)
{
lean_object* v_unused_1411_; lean_object* v_unused_1412_; lean_object* v_unused_1413_; 
v_unused_1411_ = lean_ctor_get(v_l_1299_, 4);
lean_dec(v_unused_1411_);
v_unused_1412_ = lean_ctor_get(v_l_1299_, 3);
lean_dec(v_unused_1412_);
v_unused_1413_ = lean_ctor_get(v_l_1299_, 0);
lean_dec(v_unused_1413_);
v___x_1398_ = v_l_1299_;
v_isShared_1399_ = v_isSharedCheck_1410_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_v_1396_);
lean_inc(v_k_1395_);
lean_dec(v_l_1299_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1410_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___x_1400_; lean_object* v___x_1402_; 
v___x_1400_ = lean_unsigned_to_nat(3u);
if (v_isShared_1399_ == 0)
{
lean_ctor_set(v___x_1398_, 4, v_r_1300_);
lean_ctor_set(v___x_1398_, 3, v_r_1300_);
lean_ctor_set(v___x_1398_, 2, v_v_1394_);
lean_ctor_set(v___x_1398_, 1, v_k_1393_);
lean_ctor_set(v___x_1398_, 0, v___x_1301_);
v___x_1402_ = v___x_1398_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v___x_1301_);
lean_ctor_set(v_reuseFailAlloc_1409_, 1, v_k_1393_);
lean_ctor_set(v_reuseFailAlloc_1409_, 2, v_v_1394_);
lean_ctor_set(v_reuseFailAlloc_1409_, 3, v_r_1300_);
lean_ctor_set(v_reuseFailAlloc_1409_, 4, v_r_1300_);
v___x_1402_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
lean_object* v___x_1404_; 
if (v_isShared_1381_ == 0)
{
lean_ctor_set(v___x_1380_, 3, v_r_1300_);
lean_ctor_set(v___x_1380_, 0, v___x_1301_);
v___x_1404_ = v___x_1380_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v___x_1301_);
lean_ctor_set(v_reuseFailAlloc_1408_, 1, v_k_1297_);
lean_ctor_set(v_reuseFailAlloc_1408_, 2, v_v_1298_);
lean_ctor_set(v_reuseFailAlloc_1408_, 3, v_r_1300_);
lean_ctor_set(v_reuseFailAlloc_1408_, 4, v_r_1300_);
v___x_1404_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
lean_object* v___x_1406_; 
if (v_isShared_1305_ == 0)
{
lean_ctor_set(v___x_1304_, 4, v___x_1404_);
lean_ctor_set(v___x_1304_, 3, v___x_1402_);
lean_ctor_set(v___x_1304_, 2, v_v_1396_);
lean_ctor_set(v___x_1304_, 1, v_k_1395_);
lean_ctor_set(v___x_1304_, 0, v___x_1400_);
v___x_1406_ = v___x_1304_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v___x_1400_);
lean_ctor_set(v_reuseFailAlloc_1407_, 1, v_k_1395_);
lean_ctor_set(v_reuseFailAlloc_1407_, 2, v_v_1396_);
lean_ctor_set(v_reuseFailAlloc_1407_, 3, v___x_1402_);
lean_ctor_set(v_reuseFailAlloc_1407_, 4, v___x_1404_);
v___x_1406_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
return v___x_1406_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1300_) == 0)
{
lean_object* v_k_1414_; lean_object* v_v_1415_; lean_object* v___x_1416_; lean_object* v___x_1418_; 
lean_dec(v_size_1296_);
v_k_1414_ = lean_ctor_get(v___x_1306_, 0);
lean_inc(v_k_1414_);
v_v_1415_ = lean_ctor_get(v___x_1306_, 1);
lean_inc(v_v_1415_);
lean_dec_ref(v___x_1306_);
v___x_1416_ = lean_unsigned_to_nat(3u);
if (v_isShared_1381_ == 0)
{
lean_ctor_set(v___x_1380_, 4, v_l_1299_);
lean_ctor_set(v___x_1380_, 2, v_v_1415_);
lean_ctor_set(v___x_1380_, 1, v_k_1414_);
lean_ctor_set(v___x_1380_, 0, v___x_1301_);
v___x_1418_ = v___x_1380_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v___x_1301_);
lean_ctor_set(v_reuseFailAlloc_1422_, 1, v_k_1414_);
lean_ctor_set(v_reuseFailAlloc_1422_, 2, v_v_1415_);
lean_ctor_set(v_reuseFailAlloc_1422_, 3, v_l_1299_);
lean_ctor_set(v_reuseFailAlloc_1422_, 4, v_l_1299_);
v___x_1418_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
lean_object* v___x_1420_; 
if (v_isShared_1305_ == 0)
{
lean_ctor_set(v___x_1304_, 4, v_r_1300_);
lean_ctor_set(v___x_1304_, 3, v___x_1418_);
lean_ctor_set(v___x_1304_, 2, v_v_1298_);
lean_ctor_set(v___x_1304_, 1, v_k_1297_);
lean_ctor_set(v___x_1304_, 0, v___x_1416_);
v___x_1420_ = v___x_1304_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v___x_1416_);
lean_ctor_set(v_reuseFailAlloc_1421_, 1, v_k_1297_);
lean_ctor_set(v_reuseFailAlloc_1421_, 2, v_v_1298_);
lean_ctor_set(v_reuseFailAlloc_1421_, 3, v___x_1418_);
lean_ctor_set(v_reuseFailAlloc_1421_, 4, v_r_1300_);
v___x_1420_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
return v___x_1420_;
}
}
}
else
{
lean_object* v_k_1423_; lean_object* v_v_1424_; lean_object* v___x_1426_; 
v_k_1423_ = lean_ctor_get(v___x_1306_, 0);
lean_inc(v_k_1423_);
v_v_1424_ = lean_ctor_get(v___x_1306_, 1);
lean_inc(v_v_1424_);
lean_dec_ref(v___x_1306_);
if (v_isShared_1381_ == 0)
{
lean_ctor_set(v___x_1380_, 3, v_r_1300_);
v___x_1426_ = v___x_1380_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v_size_1296_);
lean_ctor_set(v_reuseFailAlloc_1431_, 1, v_k_1297_);
lean_ctor_set(v_reuseFailAlloc_1431_, 2, v_v_1298_);
lean_ctor_set(v_reuseFailAlloc_1431_, 3, v_r_1300_);
lean_ctor_set(v_reuseFailAlloc_1431_, 4, v_r_1300_);
v___x_1426_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
lean_object* v___x_1427_; lean_object* v___x_1429_; 
v___x_1427_ = lean_unsigned_to_nat(2u);
if (v_isShared_1305_ == 0)
{
lean_ctor_set(v___x_1304_, 4, v___x_1426_);
lean_ctor_set(v___x_1304_, 3, v_r_1300_);
lean_ctor_set(v___x_1304_, 2, v_v_1424_);
lean_ctor_set(v___x_1304_, 1, v_k_1423_);
lean_ctor_set(v___x_1304_, 0, v___x_1427_);
v___x_1429_ = v___x_1304_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v___x_1427_);
lean_ctor_set(v_reuseFailAlloc_1430_, 1, v_k_1423_);
lean_ctor_set(v_reuseFailAlloc_1430_, 2, v_v_1424_);
lean_ctor_set(v_reuseFailAlloc_1430_, 3, v_r_1300_);
lean_ctor_set(v_reuseFailAlloc_1430_, 4, v___x_1426_);
v___x_1429_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
return v___x_1429_;
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
lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1596_; 
lean_inc(v_r_1300_);
lean_inc(v_v_1298_);
lean_inc(v_k_1297_);
v_isSharedCheck_1596_ = !lean_is_exclusive(v_r_1112_);
if (v_isSharedCheck_1596_ == 0)
{
lean_object* v_unused_1597_; lean_object* v_unused_1598_; lean_object* v_unused_1599_; lean_object* v_unused_1600_; lean_object* v_unused_1601_; 
v_unused_1597_ = lean_ctor_get(v_r_1112_, 4);
lean_dec(v_unused_1597_);
v_unused_1598_ = lean_ctor_get(v_r_1112_, 3);
lean_dec(v_unused_1598_);
v_unused_1599_ = lean_ctor_get(v_r_1112_, 2);
lean_dec(v_unused_1599_);
v_unused_1600_ = lean_ctor_get(v_r_1112_, 1);
lean_dec(v_unused_1600_);
v_unused_1601_ = lean_ctor_get(v_r_1112_, 0);
lean_dec(v_unused_1601_);
v___x_1445_ = v_r_1112_;
v_isShared_1446_ = v_isSharedCheck_1596_;
goto v_resetjp_1444_;
}
else
{
lean_dec(v_r_1112_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1596_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v___x_1447_; lean_object* v_tree_1448_; 
v___x_1447_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_1297_, v_v_1298_, v_l_1299_, v_r_1300_);
v_tree_1448_ = lean_ctor_get(v___x_1447_, 2);
lean_inc(v_tree_1448_);
if (lean_obj_tag(v_tree_1448_) == 0)
{
lean_object* v_k_1449_; lean_object* v_v_1450_; lean_object* v_size_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; uint8_t v___x_1454_; 
v_k_1449_ = lean_ctor_get(v___x_1447_, 0);
lean_inc(v_k_1449_);
v_v_1450_ = lean_ctor_get(v___x_1447_, 1);
lean_inc(v_v_1450_);
lean_dec_ref(v___x_1447_);
v_size_1451_ = lean_ctor_get(v_tree_1448_, 0);
v___x_1452_ = lean_unsigned_to_nat(3u);
v___x_1453_ = lean_nat_mul(v___x_1452_, v_size_1451_);
v___x_1454_ = lean_nat_dec_lt(v___x_1453_, v_size_1291_);
lean_dec(v___x_1453_);
if (v___x_1454_ == 0)
{
lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1458_; 
lean_dec(v_r_1295_);
v___x_1455_ = lean_nat_add(v___x_1301_, v_size_1291_);
v___x_1456_ = lean_nat_add(v___x_1455_, v_size_1451_);
lean_dec(v___x_1455_);
if (v_isShared_1446_ == 0)
{
lean_ctor_set(v___x_1445_, 4, v_tree_1448_);
lean_ctor_set(v___x_1445_, 3, v_l_1111_);
lean_ctor_set(v___x_1445_, 2, v_v_1450_);
lean_ctor_set(v___x_1445_, 1, v_k_1449_);
lean_ctor_set(v___x_1445_, 0, v___x_1456_);
v___x_1458_ = v___x_1445_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v___x_1456_);
lean_ctor_set(v_reuseFailAlloc_1459_, 1, v_k_1449_);
lean_ctor_set(v_reuseFailAlloc_1459_, 2, v_v_1450_);
lean_ctor_set(v_reuseFailAlloc_1459_, 3, v_l_1111_);
lean_ctor_set(v_reuseFailAlloc_1459_, 4, v_tree_1448_);
v___x_1458_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
return v___x_1458_;
}
}
else
{
lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1525_; 
lean_inc(v_l_1294_);
lean_inc(v_v_1293_);
lean_inc(v_k_1292_);
lean_inc(v_size_1291_);
v_isSharedCheck_1525_ = !lean_is_exclusive(v_l_1111_);
if (v_isSharedCheck_1525_ == 0)
{
lean_object* v_unused_1526_; lean_object* v_unused_1527_; lean_object* v_unused_1528_; lean_object* v_unused_1529_; lean_object* v_unused_1530_; 
v_unused_1526_ = lean_ctor_get(v_l_1111_, 4);
lean_dec(v_unused_1526_);
v_unused_1527_ = lean_ctor_get(v_l_1111_, 3);
lean_dec(v_unused_1527_);
v_unused_1528_ = lean_ctor_get(v_l_1111_, 2);
lean_dec(v_unused_1528_);
v_unused_1529_ = lean_ctor_get(v_l_1111_, 1);
lean_dec(v_unused_1529_);
v_unused_1530_ = lean_ctor_get(v_l_1111_, 0);
lean_dec(v_unused_1530_);
v___x_1461_ = v_l_1111_;
v_isShared_1462_ = v_isSharedCheck_1525_;
goto v_resetjp_1460_;
}
else
{
lean_dec(v_l_1111_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1525_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v_size_1463_; lean_object* v_size_1464_; lean_object* v_k_1465_; lean_object* v_v_1466_; lean_object* v_l_1467_; lean_object* v_r_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; uint8_t v___x_1471_; 
v_size_1463_ = lean_ctor_get(v_l_1294_, 0);
v_size_1464_ = lean_ctor_get(v_r_1295_, 0);
v_k_1465_ = lean_ctor_get(v_r_1295_, 1);
v_v_1466_ = lean_ctor_get(v_r_1295_, 2);
v_l_1467_ = lean_ctor_get(v_r_1295_, 3);
v_r_1468_ = lean_ctor_get(v_r_1295_, 4);
v___x_1469_ = lean_unsigned_to_nat(2u);
v___x_1470_ = lean_nat_mul(v___x_1469_, v_size_1463_);
v___x_1471_ = lean_nat_dec_lt(v_size_1464_, v___x_1470_);
lean_dec(v___x_1470_);
if (v___x_1471_ == 0)
{
lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1509_; 
lean_inc(v_r_1468_);
lean_inc(v_l_1467_);
lean_inc(v_v_1466_);
lean_inc(v_k_1465_);
lean_del_object(v___x_1461_);
v_isSharedCheck_1509_ = !lean_is_exclusive(v_r_1295_);
if (v_isSharedCheck_1509_ == 0)
{
lean_object* v_unused_1510_; lean_object* v_unused_1511_; lean_object* v_unused_1512_; lean_object* v_unused_1513_; lean_object* v_unused_1514_; 
v_unused_1510_ = lean_ctor_get(v_r_1295_, 4);
lean_dec(v_unused_1510_);
v_unused_1511_ = lean_ctor_get(v_r_1295_, 3);
lean_dec(v_unused_1511_);
v_unused_1512_ = lean_ctor_get(v_r_1295_, 2);
lean_dec(v_unused_1512_);
v_unused_1513_ = lean_ctor_get(v_r_1295_, 1);
lean_dec(v_unused_1513_);
v_unused_1514_ = lean_ctor_get(v_r_1295_, 0);
lean_dec(v_unused_1514_);
v___x_1473_ = v_r_1295_;
v_isShared_1474_ = v_isSharedCheck_1509_;
goto v_resetjp_1472_;
}
else
{
lean_dec(v_r_1295_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1509_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___y_1478_; lean_object* v___y_1479_; lean_object* v___y_1480_; lean_object* v___x_1497_; lean_object* v___y_1499_; 
v___x_1475_ = lean_nat_add(v___x_1301_, v_size_1291_);
lean_dec(v_size_1291_);
v___x_1476_ = lean_nat_add(v___x_1475_, v_size_1451_);
lean_dec(v___x_1475_);
v___x_1497_ = lean_nat_add(v___x_1301_, v_size_1463_);
if (lean_obj_tag(v_l_1467_) == 0)
{
lean_object* v_size_1507_; 
v_size_1507_ = lean_ctor_get(v_l_1467_, 0);
lean_inc(v_size_1507_);
v___y_1499_ = v_size_1507_;
goto v___jp_1498_;
}
else
{
lean_object* v___x_1508_; 
v___x_1508_ = lean_unsigned_to_nat(0u);
v___y_1499_ = v___x_1508_;
goto v___jp_1498_;
}
v___jp_1477_:
{
lean_object* v___x_1481_; lean_object* v___x_1483_; 
v___x_1481_ = lean_nat_add(v___y_1478_, v___y_1480_);
lean_dec(v___y_1480_);
lean_dec(v___y_1478_);
lean_inc_ref(v_tree_1448_);
if (v_isShared_1474_ == 0)
{
lean_ctor_set(v___x_1473_, 4, v_tree_1448_);
lean_ctor_set(v___x_1473_, 3, v_r_1468_);
lean_ctor_set(v___x_1473_, 2, v_v_1450_);
lean_ctor_set(v___x_1473_, 1, v_k_1449_);
lean_ctor_set(v___x_1473_, 0, v___x_1481_);
v___x_1483_ = v___x_1473_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v___x_1481_);
lean_ctor_set(v_reuseFailAlloc_1496_, 1, v_k_1449_);
lean_ctor_set(v_reuseFailAlloc_1496_, 2, v_v_1450_);
lean_ctor_set(v_reuseFailAlloc_1496_, 3, v_r_1468_);
lean_ctor_set(v_reuseFailAlloc_1496_, 4, v_tree_1448_);
v___x_1483_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1490_; 
v_isSharedCheck_1490_ = !lean_is_exclusive(v_tree_1448_);
if (v_isSharedCheck_1490_ == 0)
{
lean_object* v_unused_1491_; lean_object* v_unused_1492_; lean_object* v_unused_1493_; lean_object* v_unused_1494_; lean_object* v_unused_1495_; 
v_unused_1491_ = lean_ctor_get(v_tree_1448_, 4);
lean_dec(v_unused_1491_);
v_unused_1492_ = lean_ctor_get(v_tree_1448_, 3);
lean_dec(v_unused_1492_);
v_unused_1493_ = lean_ctor_get(v_tree_1448_, 2);
lean_dec(v_unused_1493_);
v_unused_1494_ = lean_ctor_get(v_tree_1448_, 1);
lean_dec(v_unused_1494_);
v_unused_1495_ = lean_ctor_get(v_tree_1448_, 0);
lean_dec(v_unused_1495_);
v___x_1485_ = v_tree_1448_;
v_isShared_1486_ = v_isSharedCheck_1490_;
goto v_resetjp_1484_;
}
else
{
lean_dec(v_tree_1448_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1490_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
lean_object* v___x_1488_; 
if (v_isShared_1486_ == 0)
{
lean_ctor_set(v___x_1485_, 4, v___x_1483_);
lean_ctor_set(v___x_1485_, 3, v___y_1479_);
lean_ctor_set(v___x_1485_, 2, v_v_1466_);
lean_ctor_set(v___x_1485_, 1, v_k_1465_);
lean_ctor_set(v___x_1485_, 0, v___x_1476_);
v___x_1488_ = v___x_1485_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v___x_1476_);
lean_ctor_set(v_reuseFailAlloc_1489_, 1, v_k_1465_);
lean_ctor_set(v_reuseFailAlloc_1489_, 2, v_v_1466_);
lean_ctor_set(v_reuseFailAlloc_1489_, 3, v___y_1479_);
lean_ctor_set(v_reuseFailAlloc_1489_, 4, v___x_1483_);
v___x_1488_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
return v___x_1488_;
}
}
}
}
v___jp_1498_:
{
lean_object* v___x_1500_; lean_object* v___x_1502_; 
v___x_1500_ = lean_nat_add(v___x_1497_, v___y_1499_);
lean_dec(v___y_1499_);
lean_dec(v___x_1497_);
if (v_isShared_1446_ == 0)
{
lean_ctor_set(v___x_1445_, 4, v_l_1467_);
lean_ctor_set(v___x_1445_, 3, v_l_1294_);
lean_ctor_set(v___x_1445_, 2, v_v_1293_);
lean_ctor_set(v___x_1445_, 1, v_k_1292_);
lean_ctor_set(v___x_1445_, 0, v___x_1500_);
v___x_1502_ = v___x_1445_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v___x_1500_);
lean_ctor_set(v_reuseFailAlloc_1506_, 1, v_k_1292_);
lean_ctor_set(v_reuseFailAlloc_1506_, 2, v_v_1293_);
lean_ctor_set(v_reuseFailAlloc_1506_, 3, v_l_1294_);
lean_ctor_set(v_reuseFailAlloc_1506_, 4, v_l_1467_);
v___x_1502_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
lean_object* v___x_1503_; 
v___x_1503_ = lean_nat_add(v___x_1301_, v_size_1451_);
if (lean_obj_tag(v_r_1468_) == 0)
{
lean_object* v_size_1504_; 
v_size_1504_ = lean_ctor_get(v_r_1468_, 0);
lean_inc(v_size_1504_);
v___y_1478_ = v___x_1503_;
v___y_1479_ = v___x_1502_;
v___y_1480_ = v_size_1504_;
goto v___jp_1477_;
}
else
{
lean_object* v___x_1505_; 
v___x_1505_ = lean_unsigned_to_nat(0u);
v___y_1478_ = v___x_1503_;
v___y_1479_ = v___x_1502_;
v___y_1480_ = v___x_1505_;
goto v___jp_1477_;
}
}
}
}
}
else
{
lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1520_; 
v___x_1515_ = lean_nat_add(v___x_1301_, v_size_1291_);
lean_dec(v_size_1291_);
v___x_1516_ = lean_nat_add(v___x_1515_, v_size_1451_);
lean_dec(v___x_1515_);
v___x_1517_ = lean_nat_add(v___x_1301_, v_size_1451_);
v___x_1518_ = lean_nat_add(v___x_1517_, v_size_1464_);
lean_dec(v___x_1517_);
if (v_isShared_1446_ == 0)
{
lean_ctor_set(v___x_1445_, 4, v_tree_1448_);
lean_ctor_set(v___x_1445_, 3, v_r_1295_);
lean_ctor_set(v___x_1445_, 2, v_v_1450_);
lean_ctor_set(v___x_1445_, 1, v_k_1449_);
lean_ctor_set(v___x_1445_, 0, v___x_1518_);
v___x_1520_ = v___x_1445_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v___x_1518_);
lean_ctor_set(v_reuseFailAlloc_1524_, 1, v_k_1449_);
lean_ctor_set(v_reuseFailAlloc_1524_, 2, v_v_1450_);
lean_ctor_set(v_reuseFailAlloc_1524_, 3, v_r_1295_);
lean_ctor_set(v_reuseFailAlloc_1524_, 4, v_tree_1448_);
v___x_1520_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
lean_object* v___x_1522_; 
if (v_isShared_1462_ == 0)
{
lean_ctor_set(v___x_1461_, 4, v___x_1520_);
lean_ctor_set(v___x_1461_, 0, v___x_1516_);
v___x_1522_ = v___x_1461_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v___x_1516_);
lean_ctor_set(v_reuseFailAlloc_1523_, 1, v_k_1292_);
lean_ctor_set(v_reuseFailAlloc_1523_, 2, v_v_1293_);
lean_ctor_set(v_reuseFailAlloc_1523_, 3, v_l_1294_);
lean_ctor_set(v_reuseFailAlloc_1523_, 4, v___x_1520_);
v___x_1522_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
return v___x_1522_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_1294_) == 0)
{
lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1554_; 
lean_inc_ref(v_l_1294_);
lean_inc(v_v_1293_);
lean_inc(v_k_1292_);
lean_inc(v_size_1291_);
v_isSharedCheck_1554_ = !lean_is_exclusive(v_l_1111_);
if (v_isSharedCheck_1554_ == 0)
{
lean_object* v_unused_1555_; lean_object* v_unused_1556_; lean_object* v_unused_1557_; lean_object* v_unused_1558_; lean_object* v_unused_1559_; 
v_unused_1555_ = lean_ctor_get(v_l_1111_, 4);
lean_dec(v_unused_1555_);
v_unused_1556_ = lean_ctor_get(v_l_1111_, 3);
lean_dec(v_unused_1556_);
v_unused_1557_ = lean_ctor_get(v_l_1111_, 2);
lean_dec(v_unused_1557_);
v_unused_1558_ = lean_ctor_get(v_l_1111_, 1);
lean_dec(v_unused_1558_);
v_unused_1559_ = lean_ctor_get(v_l_1111_, 0);
lean_dec(v_unused_1559_);
v___x_1532_ = v_l_1111_;
v_isShared_1533_ = v_isSharedCheck_1554_;
goto v_resetjp_1531_;
}
else
{
lean_dec(v_l_1111_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1554_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
if (lean_obj_tag(v_r_1295_) == 0)
{
lean_object* v_k_1534_; lean_object* v_v_1535_; lean_object* v_size_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1540_; 
v_k_1534_ = lean_ctor_get(v___x_1447_, 0);
lean_inc(v_k_1534_);
v_v_1535_ = lean_ctor_get(v___x_1447_, 1);
lean_inc(v_v_1535_);
lean_dec_ref(v___x_1447_);
v_size_1536_ = lean_ctor_get(v_r_1295_, 0);
v___x_1537_ = lean_nat_add(v___x_1301_, v_size_1291_);
lean_dec(v_size_1291_);
v___x_1538_ = lean_nat_add(v___x_1301_, v_size_1536_);
if (v_isShared_1446_ == 0)
{
lean_ctor_set(v___x_1445_, 4, v_tree_1448_);
lean_ctor_set(v___x_1445_, 3, v_r_1295_);
lean_ctor_set(v___x_1445_, 2, v_v_1535_);
lean_ctor_set(v___x_1445_, 1, v_k_1534_);
lean_ctor_set(v___x_1445_, 0, v___x_1538_);
v___x_1540_ = v___x_1445_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v___x_1538_);
lean_ctor_set(v_reuseFailAlloc_1544_, 1, v_k_1534_);
lean_ctor_set(v_reuseFailAlloc_1544_, 2, v_v_1535_);
lean_ctor_set(v_reuseFailAlloc_1544_, 3, v_r_1295_);
lean_ctor_set(v_reuseFailAlloc_1544_, 4, v_tree_1448_);
v___x_1540_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
lean_object* v___x_1542_; 
if (v_isShared_1533_ == 0)
{
lean_ctor_set(v___x_1532_, 4, v___x_1540_);
lean_ctor_set(v___x_1532_, 0, v___x_1537_);
v___x_1542_ = v___x_1532_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v___x_1537_);
lean_ctor_set(v_reuseFailAlloc_1543_, 1, v_k_1292_);
lean_ctor_set(v_reuseFailAlloc_1543_, 2, v_v_1293_);
lean_ctor_set(v_reuseFailAlloc_1543_, 3, v_l_1294_);
lean_ctor_set(v_reuseFailAlloc_1543_, 4, v___x_1540_);
v___x_1542_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
return v___x_1542_;
}
}
}
else
{
lean_object* v_k_1545_; lean_object* v_v_1546_; lean_object* v___x_1547_; lean_object* v___x_1549_; 
lean_dec(v_size_1291_);
v_k_1545_ = lean_ctor_get(v___x_1447_, 0);
lean_inc(v_k_1545_);
v_v_1546_ = lean_ctor_get(v___x_1447_, 1);
lean_inc(v_v_1546_);
lean_dec_ref(v___x_1447_);
v___x_1547_ = lean_unsigned_to_nat(3u);
if (v_isShared_1446_ == 0)
{
lean_ctor_set(v___x_1445_, 4, v_r_1295_);
lean_ctor_set(v___x_1445_, 3, v_r_1295_);
lean_ctor_set(v___x_1445_, 2, v_v_1546_);
lean_ctor_set(v___x_1445_, 1, v_k_1545_);
lean_ctor_set(v___x_1445_, 0, v___x_1301_);
v___x_1549_ = v___x_1445_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v___x_1301_);
lean_ctor_set(v_reuseFailAlloc_1553_, 1, v_k_1545_);
lean_ctor_set(v_reuseFailAlloc_1553_, 2, v_v_1546_);
lean_ctor_set(v_reuseFailAlloc_1553_, 3, v_r_1295_);
lean_ctor_set(v_reuseFailAlloc_1553_, 4, v_r_1295_);
v___x_1549_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
lean_object* v___x_1551_; 
if (v_isShared_1533_ == 0)
{
lean_ctor_set(v___x_1532_, 4, v___x_1549_);
lean_ctor_set(v___x_1532_, 0, v___x_1547_);
v___x_1551_ = v___x_1532_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v___x_1547_);
lean_ctor_set(v_reuseFailAlloc_1552_, 1, v_k_1292_);
lean_ctor_set(v_reuseFailAlloc_1552_, 2, v_v_1293_);
lean_ctor_set(v_reuseFailAlloc_1552_, 3, v_l_1294_);
lean_ctor_set(v_reuseFailAlloc_1552_, 4, v___x_1549_);
v___x_1551_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
return v___x_1551_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1295_) == 0)
{
lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1584_; 
lean_inc(v_l_1294_);
lean_inc(v_v_1293_);
lean_inc(v_k_1292_);
v_isSharedCheck_1584_ = !lean_is_exclusive(v_l_1111_);
if (v_isSharedCheck_1584_ == 0)
{
lean_object* v_unused_1585_; lean_object* v_unused_1586_; lean_object* v_unused_1587_; lean_object* v_unused_1588_; lean_object* v_unused_1589_; 
v_unused_1585_ = lean_ctor_get(v_l_1111_, 4);
lean_dec(v_unused_1585_);
v_unused_1586_ = lean_ctor_get(v_l_1111_, 3);
lean_dec(v_unused_1586_);
v_unused_1587_ = lean_ctor_get(v_l_1111_, 2);
lean_dec(v_unused_1587_);
v_unused_1588_ = lean_ctor_get(v_l_1111_, 1);
lean_dec(v_unused_1588_);
v_unused_1589_ = lean_ctor_get(v_l_1111_, 0);
lean_dec(v_unused_1589_);
v___x_1561_ = v_l_1111_;
v_isShared_1562_ = v_isSharedCheck_1584_;
goto v_resetjp_1560_;
}
else
{
lean_dec(v_l_1111_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1584_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v_k_1563_; lean_object* v_v_1564_; lean_object* v_k_1565_; lean_object* v_v_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1580_; 
v_k_1563_ = lean_ctor_get(v___x_1447_, 0);
lean_inc(v_k_1563_);
v_v_1564_ = lean_ctor_get(v___x_1447_, 1);
lean_inc(v_v_1564_);
lean_dec_ref(v___x_1447_);
v_k_1565_ = lean_ctor_get(v_r_1295_, 1);
v_v_1566_ = lean_ctor_get(v_r_1295_, 2);
v_isSharedCheck_1580_ = !lean_is_exclusive(v_r_1295_);
if (v_isSharedCheck_1580_ == 0)
{
lean_object* v_unused_1581_; lean_object* v_unused_1582_; lean_object* v_unused_1583_; 
v_unused_1581_ = lean_ctor_get(v_r_1295_, 4);
lean_dec(v_unused_1581_);
v_unused_1582_ = lean_ctor_get(v_r_1295_, 3);
lean_dec(v_unused_1582_);
v_unused_1583_ = lean_ctor_get(v_r_1295_, 0);
lean_dec(v_unused_1583_);
v___x_1568_ = v_r_1295_;
v_isShared_1569_ = v_isSharedCheck_1580_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_v_1566_);
lean_inc(v_k_1565_);
lean_dec(v_r_1295_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1580_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v___x_1570_; lean_object* v___x_1572_; 
v___x_1570_ = lean_unsigned_to_nat(3u);
if (v_isShared_1569_ == 0)
{
lean_ctor_set(v___x_1568_, 4, v_l_1294_);
lean_ctor_set(v___x_1568_, 3, v_l_1294_);
lean_ctor_set(v___x_1568_, 2, v_v_1293_);
lean_ctor_set(v___x_1568_, 1, v_k_1292_);
lean_ctor_set(v___x_1568_, 0, v___x_1301_);
v___x_1572_ = v___x_1568_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v___x_1301_);
lean_ctor_set(v_reuseFailAlloc_1579_, 1, v_k_1292_);
lean_ctor_set(v_reuseFailAlloc_1579_, 2, v_v_1293_);
lean_ctor_set(v_reuseFailAlloc_1579_, 3, v_l_1294_);
lean_ctor_set(v_reuseFailAlloc_1579_, 4, v_l_1294_);
v___x_1572_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
lean_object* v___x_1574_; 
if (v_isShared_1446_ == 0)
{
lean_ctor_set(v___x_1445_, 4, v_l_1294_);
lean_ctor_set(v___x_1445_, 3, v_l_1294_);
lean_ctor_set(v___x_1445_, 2, v_v_1564_);
lean_ctor_set(v___x_1445_, 1, v_k_1563_);
lean_ctor_set(v___x_1445_, 0, v___x_1301_);
v___x_1574_ = v___x_1445_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v___x_1301_);
lean_ctor_set(v_reuseFailAlloc_1578_, 1, v_k_1563_);
lean_ctor_set(v_reuseFailAlloc_1578_, 2, v_v_1564_);
lean_ctor_set(v_reuseFailAlloc_1578_, 3, v_l_1294_);
lean_ctor_set(v_reuseFailAlloc_1578_, 4, v_l_1294_);
v___x_1574_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
lean_object* v___x_1576_; 
if (v_isShared_1562_ == 0)
{
lean_ctor_set(v___x_1561_, 4, v___x_1574_);
lean_ctor_set(v___x_1561_, 3, v___x_1572_);
lean_ctor_set(v___x_1561_, 2, v_v_1566_);
lean_ctor_set(v___x_1561_, 1, v_k_1565_);
lean_ctor_set(v___x_1561_, 0, v___x_1570_);
v___x_1576_ = v___x_1561_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v___x_1570_);
lean_ctor_set(v_reuseFailAlloc_1577_, 1, v_k_1565_);
lean_ctor_set(v_reuseFailAlloc_1577_, 2, v_v_1566_);
lean_ctor_set(v_reuseFailAlloc_1577_, 3, v___x_1572_);
lean_ctor_set(v_reuseFailAlloc_1577_, 4, v___x_1574_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
return v___x_1576_;
}
}
}
}
}
}
else
{
lean_object* v_k_1590_; lean_object* v_v_1591_; lean_object* v___x_1592_; lean_object* v___x_1594_; 
v_k_1590_ = lean_ctor_get(v___x_1447_, 0);
lean_inc(v_k_1590_);
v_v_1591_ = lean_ctor_get(v___x_1447_, 1);
lean_inc(v_v_1591_);
lean_dec_ref(v___x_1447_);
v___x_1592_ = lean_unsigned_to_nat(2u);
if (v_isShared_1446_ == 0)
{
lean_ctor_set(v___x_1445_, 4, v_r_1295_);
lean_ctor_set(v___x_1445_, 3, v_l_1111_);
lean_ctor_set(v___x_1445_, 2, v_v_1591_);
lean_ctor_set(v___x_1445_, 1, v_k_1590_);
lean_ctor_set(v___x_1445_, 0, v___x_1592_);
v___x_1594_ = v___x_1445_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v___x_1592_);
lean_ctor_set(v_reuseFailAlloc_1595_, 1, v_k_1590_);
lean_ctor_set(v_reuseFailAlloc_1595_, 2, v_v_1591_);
lean_ctor_set(v_reuseFailAlloc_1595_, 3, v_l_1111_);
lean_ctor_set(v_reuseFailAlloc_1595_, 4, v_r_1295_);
v___x_1594_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
return v___x_1594_;
}
}
}
}
}
}
}
else
{
return v_l_1111_;
}
}
else
{
return v_r_1112_;
}
}
default: 
{
lean_object* v_impl_1602_; lean_object* v___x_1603_; 
v_impl_1602_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_k_1107_, v_r_1112_);
v___x_1603_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1602_) == 0)
{
if (lean_obj_tag(v_l_1111_) == 0)
{
lean_object* v_size_1604_; lean_object* v_size_1605_; lean_object* v_k_1606_; lean_object* v_v_1607_; lean_object* v_l_1608_; lean_object* v_r_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; uint8_t v___x_1612_; 
v_size_1604_ = lean_ctor_get(v_impl_1602_, 0);
lean_inc(v_size_1604_);
v_size_1605_ = lean_ctor_get(v_l_1111_, 0);
v_k_1606_ = lean_ctor_get(v_l_1111_, 1);
v_v_1607_ = lean_ctor_get(v_l_1111_, 2);
v_l_1608_ = lean_ctor_get(v_l_1111_, 3);
v_r_1609_ = lean_ctor_get(v_l_1111_, 4);
lean_inc(v_r_1609_);
v___x_1610_ = lean_unsigned_to_nat(3u);
v___x_1611_ = lean_nat_mul(v___x_1610_, v_size_1604_);
v___x_1612_ = lean_nat_dec_lt(v___x_1611_, v_size_1605_);
lean_dec(v___x_1611_);
if (v___x_1612_ == 0)
{
lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1616_; 
lean_dec(v_r_1609_);
v___x_1613_ = lean_nat_add(v___x_1603_, v_size_1605_);
v___x_1614_ = lean_nat_add(v___x_1613_, v_size_1604_);
lean_dec(v_size_1604_);
lean_dec(v___x_1613_);
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 4, v_impl_1602_);
lean_ctor_set(v___x_1114_, 0, v___x_1614_);
v___x_1616_ = v___x_1114_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v___x_1614_);
lean_ctor_set(v_reuseFailAlloc_1617_, 1, v_k_1109_);
lean_ctor_set(v_reuseFailAlloc_1617_, 2, v_v_1110_);
lean_ctor_set(v_reuseFailAlloc_1617_, 3, v_l_1111_);
lean_ctor_set(v_reuseFailAlloc_1617_, 4, v_impl_1602_);
v___x_1616_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
return v___x_1616_;
}
}
else
{
lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1683_; 
lean_inc(v_l_1608_);
lean_inc(v_v_1607_);
lean_inc(v_k_1606_);
lean_inc(v_size_1605_);
v_isSharedCheck_1683_ = !lean_is_exclusive(v_l_1111_);
if (v_isSharedCheck_1683_ == 0)
{
lean_object* v_unused_1684_; lean_object* v_unused_1685_; lean_object* v_unused_1686_; lean_object* v_unused_1687_; lean_object* v_unused_1688_; 
v_unused_1684_ = lean_ctor_get(v_l_1111_, 4);
lean_dec(v_unused_1684_);
v_unused_1685_ = lean_ctor_get(v_l_1111_, 3);
lean_dec(v_unused_1685_);
v_unused_1686_ = lean_ctor_get(v_l_1111_, 2);
lean_dec(v_unused_1686_);
v_unused_1687_ = lean_ctor_get(v_l_1111_, 1);
lean_dec(v_unused_1687_);
v_unused_1688_ = lean_ctor_get(v_l_1111_, 0);
lean_dec(v_unused_1688_);
v___x_1619_ = v_l_1111_;
v_isShared_1620_ = v_isSharedCheck_1683_;
goto v_resetjp_1618_;
}
else
{
lean_dec(v_l_1111_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1683_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v_size_1621_; lean_object* v_size_1622_; lean_object* v_k_1623_; lean_object* v_v_1624_; lean_object* v_l_1625_; lean_object* v_r_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; uint8_t v___x_1629_; 
v_size_1621_ = lean_ctor_get(v_l_1608_, 0);
v_size_1622_ = lean_ctor_get(v_r_1609_, 0);
v_k_1623_ = lean_ctor_get(v_r_1609_, 1);
v_v_1624_ = lean_ctor_get(v_r_1609_, 2);
v_l_1625_ = lean_ctor_get(v_r_1609_, 3);
v_r_1626_ = lean_ctor_get(v_r_1609_, 4);
v___x_1627_ = lean_unsigned_to_nat(2u);
v___x_1628_ = lean_nat_mul(v___x_1627_, v_size_1621_);
v___x_1629_ = lean_nat_dec_lt(v_size_1622_, v___x_1628_);
lean_dec(v___x_1628_);
if (v___x_1629_ == 0)
{
lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1658_; 
lean_inc(v_r_1626_);
lean_inc(v_l_1625_);
lean_inc(v_v_1624_);
lean_inc(v_k_1623_);
v_isSharedCheck_1658_ = !lean_is_exclusive(v_r_1609_);
if (v_isSharedCheck_1658_ == 0)
{
lean_object* v_unused_1659_; lean_object* v_unused_1660_; lean_object* v_unused_1661_; lean_object* v_unused_1662_; lean_object* v_unused_1663_; 
v_unused_1659_ = lean_ctor_get(v_r_1609_, 4);
lean_dec(v_unused_1659_);
v_unused_1660_ = lean_ctor_get(v_r_1609_, 3);
lean_dec(v_unused_1660_);
v_unused_1661_ = lean_ctor_get(v_r_1609_, 2);
lean_dec(v_unused_1661_);
v_unused_1662_ = lean_ctor_get(v_r_1609_, 1);
lean_dec(v_unused_1662_);
v_unused_1663_ = lean_ctor_get(v_r_1609_, 0);
lean_dec(v_unused_1663_);
v___x_1631_ = v_r_1609_;
v_isShared_1632_ = v_isSharedCheck_1658_;
goto v_resetjp_1630_;
}
else
{
lean_dec(v_r_1609_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1658_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___y_1636_; lean_object* v___y_1637_; lean_object* v___y_1638_; lean_object* v___x_1646_; lean_object* v___y_1648_; 
v___x_1633_ = lean_nat_add(v___x_1603_, v_size_1605_);
lean_dec(v_size_1605_);
v___x_1634_ = lean_nat_add(v___x_1633_, v_size_1604_);
lean_dec(v___x_1633_);
v___x_1646_ = lean_nat_add(v___x_1603_, v_size_1621_);
if (lean_obj_tag(v_l_1625_) == 0)
{
lean_object* v_size_1656_; 
v_size_1656_ = lean_ctor_get(v_l_1625_, 0);
lean_inc(v_size_1656_);
v___y_1648_ = v_size_1656_;
goto v___jp_1647_;
}
else
{
lean_object* v___x_1657_; 
v___x_1657_ = lean_unsigned_to_nat(0u);
v___y_1648_ = v___x_1657_;
goto v___jp_1647_;
}
v___jp_1635_:
{
lean_object* v___x_1639_; lean_object* v___x_1641_; 
v___x_1639_ = lean_nat_add(v___y_1637_, v___y_1638_);
lean_dec(v___y_1638_);
lean_dec(v___y_1637_);
if (v_isShared_1632_ == 0)
{
lean_ctor_set(v___x_1631_, 4, v_impl_1602_);
lean_ctor_set(v___x_1631_, 3, v_r_1626_);
lean_ctor_set(v___x_1631_, 2, v_v_1110_);
lean_ctor_set(v___x_1631_, 1, v_k_1109_);
lean_ctor_set(v___x_1631_, 0, v___x_1639_);
v___x_1641_ = v___x_1631_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v___x_1639_);
lean_ctor_set(v_reuseFailAlloc_1645_, 1, v_k_1109_);
lean_ctor_set(v_reuseFailAlloc_1645_, 2, v_v_1110_);
lean_ctor_set(v_reuseFailAlloc_1645_, 3, v_r_1626_);
lean_ctor_set(v_reuseFailAlloc_1645_, 4, v_impl_1602_);
v___x_1641_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
lean_object* v___x_1643_; 
if (v_isShared_1620_ == 0)
{
lean_ctor_set(v___x_1619_, 4, v___x_1641_);
lean_ctor_set(v___x_1619_, 3, v___y_1636_);
lean_ctor_set(v___x_1619_, 2, v_v_1624_);
lean_ctor_set(v___x_1619_, 1, v_k_1623_);
lean_ctor_set(v___x_1619_, 0, v___x_1634_);
v___x_1643_ = v___x_1619_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v___x_1634_);
lean_ctor_set(v_reuseFailAlloc_1644_, 1, v_k_1623_);
lean_ctor_set(v_reuseFailAlloc_1644_, 2, v_v_1624_);
lean_ctor_set(v_reuseFailAlloc_1644_, 3, v___y_1636_);
lean_ctor_set(v_reuseFailAlloc_1644_, 4, v___x_1641_);
v___x_1643_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
return v___x_1643_;
}
}
}
v___jp_1647_:
{
lean_object* v___x_1649_; lean_object* v___x_1651_; 
v___x_1649_ = lean_nat_add(v___x_1646_, v___y_1648_);
lean_dec(v___y_1648_);
lean_dec(v___x_1646_);
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 4, v_l_1625_);
lean_ctor_set(v___x_1114_, 3, v_l_1608_);
lean_ctor_set(v___x_1114_, 2, v_v_1607_);
lean_ctor_set(v___x_1114_, 1, v_k_1606_);
lean_ctor_set(v___x_1114_, 0, v___x_1649_);
v___x_1651_ = v___x_1114_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v___x_1649_);
lean_ctor_set(v_reuseFailAlloc_1655_, 1, v_k_1606_);
lean_ctor_set(v_reuseFailAlloc_1655_, 2, v_v_1607_);
lean_ctor_set(v_reuseFailAlloc_1655_, 3, v_l_1608_);
lean_ctor_set(v_reuseFailAlloc_1655_, 4, v_l_1625_);
v___x_1651_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
lean_object* v___x_1652_; 
v___x_1652_ = lean_nat_add(v___x_1603_, v_size_1604_);
lean_dec(v_size_1604_);
if (lean_obj_tag(v_r_1626_) == 0)
{
lean_object* v_size_1653_; 
v_size_1653_ = lean_ctor_get(v_r_1626_, 0);
lean_inc(v_size_1653_);
v___y_1636_ = v___x_1651_;
v___y_1637_ = v___x_1652_;
v___y_1638_ = v_size_1653_;
goto v___jp_1635_;
}
else
{
lean_object* v___x_1654_; 
v___x_1654_ = lean_unsigned_to_nat(0u);
v___y_1636_ = v___x_1651_;
v___y_1637_ = v___x_1652_;
v___y_1638_ = v___x_1654_;
goto v___jp_1635_;
}
}
}
}
}
else
{
lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1669_; 
lean_del_object(v___x_1114_);
v___x_1664_ = lean_nat_add(v___x_1603_, v_size_1605_);
lean_dec(v_size_1605_);
v___x_1665_ = lean_nat_add(v___x_1664_, v_size_1604_);
lean_dec(v___x_1664_);
v___x_1666_ = lean_nat_add(v___x_1603_, v_size_1604_);
lean_dec(v_size_1604_);
v___x_1667_ = lean_nat_add(v___x_1666_, v_size_1622_);
lean_dec(v___x_1666_);
lean_inc_ref(v_impl_1602_);
if (v_isShared_1620_ == 0)
{
lean_ctor_set(v___x_1619_, 4, v_impl_1602_);
lean_ctor_set(v___x_1619_, 3, v_r_1609_);
lean_ctor_set(v___x_1619_, 2, v_v_1110_);
lean_ctor_set(v___x_1619_, 1, v_k_1109_);
lean_ctor_set(v___x_1619_, 0, v___x_1667_);
v___x_1669_ = v___x_1619_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v___x_1667_);
lean_ctor_set(v_reuseFailAlloc_1682_, 1, v_k_1109_);
lean_ctor_set(v_reuseFailAlloc_1682_, 2, v_v_1110_);
lean_ctor_set(v_reuseFailAlloc_1682_, 3, v_r_1609_);
lean_ctor_set(v_reuseFailAlloc_1682_, 4, v_impl_1602_);
v___x_1669_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1676_; 
v_isSharedCheck_1676_ = !lean_is_exclusive(v_impl_1602_);
if (v_isSharedCheck_1676_ == 0)
{
lean_object* v_unused_1677_; lean_object* v_unused_1678_; lean_object* v_unused_1679_; lean_object* v_unused_1680_; lean_object* v_unused_1681_; 
v_unused_1677_ = lean_ctor_get(v_impl_1602_, 4);
lean_dec(v_unused_1677_);
v_unused_1678_ = lean_ctor_get(v_impl_1602_, 3);
lean_dec(v_unused_1678_);
v_unused_1679_ = lean_ctor_get(v_impl_1602_, 2);
lean_dec(v_unused_1679_);
v_unused_1680_ = lean_ctor_get(v_impl_1602_, 1);
lean_dec(v_unused_1680_);
v_unused_1681_ = lean_ctor_get(v_impl_1602_, 0);
lean_dec(v_unused_1681_);
v___x_1671_ = v_impl_1602_;
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
else
{
lean_dec(v_impl_1602_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1676_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v___x_1674_; 
if (v_isShared_1672_ == 0)
{
lean_ctor_set(v___x_1671_, 4, v___x_1669_);
lean_ctor_set(v___x_1671_, 3, v_l_1608_);
lean_ctor_set(v___x_1671_, 2, v_v_1607_);
lean_ctor_set(v___x_1671_, 1, v_k_1606_);
lean_ctor_set(v___x_1671_, 0, v___x_1665_);
v___x_1674_ = v___x_1671_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v___x_1665_);
lean_ctor_set(v_reuseFailAlloc_1675_, 1, v_k_1606_);
lean_ctor_set(v_reuseFailAlloc_1675_, 2, v_v_1607_);
lean_ctor_set(v_reuseFailAlloc_1675_, 3, v_l_1608_);
lean_ctor_set(v_reuseFailAlloc_1675_, 4, v___x_1669_);
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
}
}
}
else
{
lean_object* v_size_1689_; lean_object* v___x_1690_; lean_object* v___x_1692_; 
v_size_1689_ = lean_ctor_get(v_impl_1602_, 0);
lean_inc(v_size_1689_);
v___x_1690_ = lean_nat_add(v___x_1603_, v_size_1689_);
lean_dec(v_size_1689_);
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 4, v_impl_1602_);
lean_ctor_set(v___x_1114_, 0, v___x_1690_);
v___x_1692_ = v___x_1114_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v___x_1690_);
lean_ctor_set(v_reuseFailAlloc_1693_, 1, v_k_1109_);
lean_ctor_set(v_reuseFailAlloc_1693_, 2, v_v_1110_);
lean_ctor_set(v_reuseFailAlloc_1693_, 3, v_l_1111_);
lean_ctor_set(v_reuseFailAlloc_1693_, 4, v_impl_1602_);
v___x_1692_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
return v___x_1692_;
}
}
}
else
{
if (lean_obj_tag(v_l_1111_) == 0)
{
lean_object* v_l_1694_; 
v_l_1694_ = lean_ctor_get(v_l_1111_, 3);
if (lean_obj_tag(v_l_1694_) == 0)
{
lean_object* v_r_1695_; 
lean_inc_ref(v_l_1694_);
v_r_1695_ = lean_ctor_get(v_l_1111_, 4);
lean_inc(v_r_1695_);
if (lean_obj_tag(v_r_1695_) == 0)
{
lean_object* v_size_1696_; lean_object* v_k_1697_; lean_object* v_v_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1711_; 
v_size_1696_ = lean_ctor_get(v_l_1111_, 0);
v_k_1697_ = lean_ctor_get(v_l_1111_, 1);
v_v_1698_ = lean_ctor_get(v_l_1111_, 2);
v_isSharedCheck_1711_ = !lean_is_exclusive(v_l_1111_);
if (v_isSharedCheck_1711_ == 0)
{
lean_object* v_unused_1712_; lean_object* v_unused_1713_; 
v_unused_1712_ = lean_ctor_get(v_l_1111_, 4);
lean_dec(v_unused_1712_);
v_unused_1713_ = lean_ctor_get(v_l_1111_, 3);
lean_dec(v_unused_1713_);
v___x_1700_ = v_l_1111_;
v_isShared_1701_ = v_isSharedCheck_1711_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_v_1698_);
lean_inc(v_k_1697_);
lean_inc(v_size_1696_);
lean_dec(v_l_1111_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1711_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v_size_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1706_; 
v_size_1702_ = lean_ctor_get(v_r_1695_, 0);
v___x_1703_ = lean_nat_add(v___x_1603_, v_size_1696_);
lean_dec(v_size_1696_);
v___x_1704_ = lean_nat_add(v___x_1603_, v_size_1702_);
if (v_isShared_1701_ == 0)
{
lean_ctor_set(v___x_1700_, 4, v_impl_1602_);
lean_ctor_set(v___x_1700_, 3, v_r_1695_);
lean_ctor_set(v___x_1700_, 2, v_v_1110_);
lean_ctor_set(v___x_1700_, 1, v_k_1109_);
lean_ctor_set(v___x_1700_, 0, v___x_1704_);
v___x_1706_ = v___x_1700_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v___x_1704_);
lean_ctor_set(v_reuseFailAlloc_1710_, 1, v_k_1109_);
lean_ctor_set(v_reuseFailAlloc_1710_, 2, v_v_1110_);
lean_ctor_set(v_reuseFailAlloc_1710_, 3, v_r_1695_);
lean_ctor_set(v_reuseFailAlloc_1710_, 4, v_impl_1602_);
v___x_1706_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
lean_object* v___x_1708_; 
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 4, v___x_1706_);
lean_ctor_set(v___x_1114_, 3, v_l_1694_);
lean_ctor_set(v___x_1114_, 2, v_v_1698_);
lean_ctor_set(v___x_1114_, 1, v_k_1697_);
lean_ctor_set(v___x_1114_, 0, v___x_1703_);
v___x_1708_ = v___x_1114_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v___x_1703_);
lean_ctor_set(v_reuseFailAlloc_1709_, 1, v_k_1697_);
lean_ctor_set(v_reuseFailAlloc_1709_, 2, v_v_1698_);
lean_ctor_set(v_reuseFailAlloc_1709_, 3, v_l_1694_);
lean_ctor_set(v_reuseFailAlloc_1709_, 4, v___x_1706_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
return v___x_1708_;
}
}
}
}
else
{
lean_object* v_k_1714_; lean_object* v_v_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1726_; 
v_k_1714_ = lean_ctor_get(v_l_1111_, 1);
v_v_1715_ = lean_ctor_get(v_l_1111_, 2);
v_isSharedCheck_1726_ = !lean_is_exclusive(v_l_1111_);
if (v_isSharedCheck_1726_ == 0)
{
lean_object* v_unused_1727_; lean_object* v_unused_1728_; lean_object* v_unused_1729_; 
v_unused_1727_ = lean_ctor_get(v_l_1111_, 4);
lean_dec(v_unused_1727_);
v_unused_1728_ = lean_ctor_get(v_l_1111_, 3);
lean_dec(v_unused_1728_);
v_unused_1729_ = lean_ctor_get(v_l_1111_, 0);
lean_dec(v_unused_1729_);
v___x_1717_ = v_l_1111_;
v_isShared_1718_ = v_isSharedCheck_1726_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_v_1715_);
lean_inc(v_k_1714_);
lean_dec(v_l_1111_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1726_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v___x_1719_; lean_object* v___x_1721_; 
v___x_1719_ = lean_unsigned_to_nat(3u);
if (v_isShared_1718_ == 0)
{
lean_ctor_set(v___x_1717_, 3, v_r_1695_);
lean_ctor_set(v___x_1717_, 2, v_v_1110_);
lean_ctor_set(v___x_1717_, 1, v_k_1109_);
lean_ctor_set(v___x_1717_, 0, v___x_1603_);
v___x_1721_ = v___x_1717_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v___x_1603_);
lean_ctor_set(v_reuseFailAlloc_1725_, 1, v_k_1109_);
lean_ctor_set(v_reuseFailAlloc_1725_, 2, v_v_1110_);
lean_ctor_set(v_reuseFailAlloc_1725_, 3, v_r_1695_);
lean_ctor_set(v_reuseFailAlloc_1725_, 4, v_r_1695_);
v___x_1721_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
lean_object* v___x_1723_; 
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 4, v___x_1721_);
lean_ctor_set(v___x_1114_, 3, v_l_1694_);
lean_ctor_set(v___x_1114_, 2, v_v_1715_);
lean_ctor_set(v___x_1114_, 1, v_k_1714_);
lean_ctor_set(v___x_1114_, 0, v___x_1719_);
v___x_1723_ = v___x_1114_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v___x_1719_);
lean_ctor_set(v_reuseFailAlloc_1724_, 1, v_k_1714_);
lean_ctor_set(v_reuseFailAlloc_1724_, 2, v_v_1715_);
lean_ctor_set(v_reuseFailAlloc_1724_, 3, v_l_1694_);
lean_ctor_set(v_reuseFailAlloc_1724_, 4, v___x_1721_);
v___x_1723_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
return v___x_1723_;
}
}
}
}
}
else
{
lean_object* v_r_1730_; 
v_r_1730_ = lean_ctor_get(v_l_1111_, 4);
lean_inc(v_r_1730_);
if (lean_obj_tag(v_r_1730_) == 0)
{
lean_object* v_k_1731_; lean_object* v_v_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1755_; 
lean_inc(v_l_1694_);
v_k_1731_ = lean_ctor_get(v_l_1111_, 1);
v_v_1732_ = lean_ctor_get(v_l_1111_, 2);
v_isSharedCheck_1755_ = !lean_is_exclusive(v_l_1111_);
if (v_isSharedCheck_1755_ == 0)
{
lean_object* v_unused_1756_; lean_object* v_unused_1757_; lean_object* v_unused_1758_; 
v_unused_1756_ = lean_ctor_get(v_l_1111_, 4);
lean_dec(v_unused_1756_);
v_unused_1757_ = lean_ctor_get(v_l_1111_, 3);
lean_dec(v_unused_1757_);
v_unused_1758_ = lean_ctor_get(v_l_1111_, 0);
lean_dec(v_unused_1758_);
v___x_1734_ = v_l_1111_;
v_isShared_1735_ = v_isSharedCheck_1755_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_v_1732_);
lean_inc(v_k_1731_);
lean_dec(v_l_1111_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1755_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v_k_1736_; lean_object* v_v_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1751_; 
v_k_1736_ = lean_ctor_get(v_r_1730_, 1);
v_v_1737_ = lean_ctor_get(v_r_1730_, 2);
v_isSharedCheck_1751_ = !lean_is_exclusive(v_r_1730_);
if (v_isSharedCheck_1751_ == 0)
{
lean_object* v_unused_1752_; lean_object* v_unused_1753_; lean_object* v_unused_1754_; 
v_unused_1752_ = lean_ctor_get(v_r_1730_, 4);
lean_dec(v_unused_1752_);
v_unused_1753_ = lean_ctor_get(v_r_1730_, 3);
lean_dec(v_unused_1753_);
v_unused_1754_ = lean_ctor_get(v_r_1730_, 0);
lean_dec(v_unused_1754_);
v___x_1739_ = v_r_1730_;
v_isShared_1740_ = v_isSharedCheck_1751_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_v_1737_);
lean_inc(v_k_1736_);
lean_dec(v_r_1730_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1751_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
lean_object* v___x_1741_; lean_object* v___x_1743_; 
v___x_1741_ = lean_unsigned_to_nat(3u);
if (v_isShared_1740_ == 0)
{
lean_ctor_set(v___x_1739_, 4, v_l_1694_);
lean_ctor_set(v___x_1739_, 3, v_l_1694_);
lean_ctor_set(v___x_1739_, 2, v_v_1732_);
lean_ctor_set(v___x_1739_, 1, v_k_1731_);
lean_ctor_set(v___x_1739_, 0, v___x_1603_);
v___x_1743_ = v___x_1739_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v___x_1603_);
lean_ctor_set(v_reuseFailAlloc_1750_, 1, v_k_1731_);
lean_ctor_set(v_reuseFailAlloc_1750_, 2, v_v_1732_);
lean_ctor_set(v_reuseFailAlloc_1750_, 3, v_l_1694_);
lean_ctor_set(v_reuseFailAlloc_1750_, 4, v_l_1694_);
v___x_1743_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
lean_object* v___x_1745_; 
if (v_isShared_1735_ == 0)
{
lean_ctor_set(v___x_1734_, 4, v_l_1694_);
lean_ctor_set(v___x_1734_, 2, v_v_1110_);
lean_ctor_set(v___x_1734_, 1, v_k_1109_);
lean_ctor_set(v___x_1734_, 0, v___x_1603_);
v___x_1745_ = v___x_1734_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1749_; 
v_reuseFailAlloc_1749_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1749_, 0, v___x_1603_);
lean_ctor_set(v_reuseFailAlloc_1749_, 1, v_k_1109_);
lean_ctor_set(v_reuseFailAlloc_1749_, 2, v_v_1110_);
lean_ctor_set(v_reuseFailAlloc_1749_, 3, v_l_1694_);
lean_ctor_set(v_reuseFailAlloc_1749_, 4, v_l_1694_);
v___x_1745_ = v_reuseFailAlloc_1749_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
lean_object* v___x_1747_; 
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 4, v___x_1745_);
lean_ctor_set(v___x_1114_, 3, v___x_1743_);
lean_ctor_set(v___x_1114_, 2, v_v_1737_);
lean_ctor_set(v___x_1114_, 1, v_k_1736_);
lean_ctor_set(v___x_1114_, 0, v___x_1741_);
v___x_1747_ = v___x_1114_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v___x_1741_);
lean_ctor_set(v_reuseFailAlloc_1748_, 1, v_k_1736_);
lean_ctor_set(v_reuseFailAlloc_1748_, 2, v_v_1737_);
lean_ctor_set(v_reuseFailAlloc_1748_, 3, v___x_1743_);
lean_ctor_set(v_reuseFailAlloc_1748_, 4, v___x_1745_);
v___x_1747_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
return v___x_1747_;
}
}
}
}
}
}
else
{
lean_object* v___x_1759_; lean_object* v___x_1761_; 
v___x_1759_ = lean_unsigned_to_nat(2u);
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 4, v_r_1730_);
lean_ctor_set(v___x_1114_, 0, v___x_1759_);
v___x_1761_ = v___x_1114_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v___x_1759_);
lean_ctor_set(v_reuseFailAlloc_1762_, 1, v_k_1109_);
lean_ctor_set(v_reuseFailAlloc_1762_, 2, v_v_1110_);
lean_ctor_set(v_reuseFailAlloc_1762_, 3, v_l_1111_);
lean_ctor_set(v_reuseFailAlloc_1762_, 4, v_r_1730_);
v___x_1761_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
return v___x_1761_;
}
}
}
}
else
{
lean_object* v___x_1764_; 
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 4, v_l_1111_);
lean_ctor_set(v___x_1114_, 0, v___x_1603_);
v___x_1764_ = v___x_1114_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v___x_1603_);
lean_ctor_set(v_reuseFailAlloc_1765_, 1, v_k_1109_);
lean_ctor_set(v_reuseFailAlloc_1765_, 2, v_v_1110_);
lean_ctor_set(v_reuseFailAlloc_1765_, 3, v_l_1111_);
lean_ctor_set(v_reuseFailAlloc_1765_, 4, v_l_1111_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
return v___x_1764_;
}
}
}
}
}
}
}
else
{
return v_t_1108_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg___boxed(lean_object* v_k_1768_, lean_object* v_t_1769_){
_start:
{
lean_object* v_res_1770_; 
v_res_1770_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_k_1768_, v_t_1769_);
lean_dec_ref(v_k_1768_);
return v_res_1770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___lam__0(lean_object* v_val_1771_, lean_object* v_s_1772_){
_start:
{
lean_object* v_toRing_1773_; lean_object* v_invFn_x3f_1774_; lean_object* v_semiringId_x3f_1775_; lean_object* v_commSemiringInst_1776_; lean_object* v_commRingInst_1777_; lean_object* v_noZeroDivInst_x3f_1778_; lean_object* v_fieldInst_x3f_1779_; lean_object* v_denoteEntries_1780_; lean_object* v_nextId_1781_; lean_object* v_steps_1782_; lean_object* v_queue_1783_; lean_object* v_basis_1784_; lean_object* v_diseqs_1785_; uint8_t v_recheck_1786_; lean_object* v_invSet_1787_; lean_object* v_numEq0_x3f_1788_; uint8_t v_numEq0Updated_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1797_; 
v_toRing_1773_ = lean_ctor_get(v_s_1772_, 0);
v_invFn_x3f_1774_ = lean_ctor_get(v_s_1772_, 1);
v_semiringId_x3f_1775_ = lean_ctor_get(v_s_1772_, 2);
v_commSemiringInst_1776_ = lean_ctor_get(v_s_1772_, 3);
v_commRingInst_1777_ = lean_ctor_get(v_s_1772_, 4);
v_noZeroDivInst_x3f_1778_ = lean_ctor_get(v_s_1772_, 5);
v_fieldInst_x3f_1779_ = lean_ctor_get(v_s_1772_, 6);
v_denoteEntries_1780_ = lean_ctor_get(v_s_1772_, 7);
v_nextId_1781_ = lean_ctor_get(v_s_1772_, 8);
v_steps_1782_ = lean_ctor_get(v_s_1772_, 9);
v_queue_1783_ = lean_ctor_get(v_s_1772_, 10);
v_basis_1784_ = lean_ctor_get(v_s_1772_, 11);
v_diseqs_1785_ = lean_ctor_get(v_s_1772_, 12);
v_recheck_1786_ = lean_ctor_get_uint8(v_s_1772_, sizeof(void*)*15);
v_invSet_1787_ = lean_ctor_get(v_s_1772_, 13);
v_numEq0_x3f_1788_ = lean_ctor_get(v_s_1772_, 14);
v_numEq0Updated_1789_ = lean_ctor_get_uint8(v_s_1772_, sizeof(void*)*15 + 1);
v_isSharedCheck_1797_ = !lean_is_exclusive(v_s_1772_);
if (v_isSharedCheck_1797_ == 0)
{
v___x_1791_ = v_s_1772_;
v_isShared_1792_ = v_isSharedCheck_1797_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_numEq0_x3f_1788_);
lean_inc(v_invSet_1787_);
lean_inc(v_diseqs_1785_);
lean_inc(v_basis_1784_);
lean_inc(v_queue_1783_);
lean_inc(v_steps_1782_);
lean_inc(v_nextId_1781_);
lean_inc(v_denoteEntries_1780_);
lean_inc(v_fieldInst_x3f_1779_);
lean_inc(v_noZeroDivInst_x3f_1778_);
lean_inc(v_commRingInst_1777_);
lean_inc(v_commSemiringInst_1776_);
lean_inc(v_semiringId_x3f_1775_);
lean_inc(v_invFn_x3f_1774_);
lean_inc(v_toRing_1773_);
lean_dec(v_s_1772_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1797_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
lean_object* v___x_1793_; lean_object* v___x_1795_; 
v___x_1793_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_val_1771_, v_queue_1783_);
if (v_isShared_1792_ == 0)
{
lean_ctor_set(v___x_1791_, 10, v___x_1793_);
v___x_1795_ = v___x_1791_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(0, 15, 2);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v_toRing_1773_);
lean_ctor_set(v_reuseFailAlloc_1796_, 1, v_invFn_x3f_1774_);
lean_ctor_set(v_reuseFailAlloc_1796_, 2, v_semiringId_x3f_1775_);
lean_ctor_set(v_reuseFailAlloc_1796_, 3, v_commSemiringInst_1776_);
lean_ctor_set(v_reuseFailAlloc_1796_, 4, v_commRingInst_1777_);
lean_ctor_set(v_reuseFailAlloc_1796_, 5, v_noZeroDivInst_x3f_1778_);
lean_ctor_set(v_reuseFailAlloc_1796_, 6, v_fieldInst_x3f_1779_);
lean_ctor_set(v_reuseFailAlloc_1796_, 7, v_denoteEntries_1780_);
lean_ctor_set(v_reuseFailAlloc_1796_, 8, v_nextId_1781_);
lean_ctor_set(v_reuseFailAlloc_1796_, 9, v_steps_1782_);
lean_ctor_set(v_reuseFailAlloc_1796_, 10, v___x_1793_);
lean_ctor_set(v_reuseFailAlloc_1796_, 11, v_basis_1784_);
lean_ctor_set(v_reuseFailAlloc_1796_, 12, v_diseqs_1785_);
lean_ctor_set(v_reuseFailAlloc_1796_, 13, v_invSet_1787_);
lean_ctor_set(v_reuseFailAlloc_1796_, 14, v_numEq0_x3f_1788_);
lean_ctor_set_uint8(v_reuseFailAlloc_1796_, sizeof(void*)*15, v_recheck_1786_);
lean_ctor_set_uint8(v_reuseFailAlloc_1796_, sizeof(void*)*15 + 1, v_numEq0Updated_1789_);
v___x_1795_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
return v___x_1795_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___lam__0___boxed(lean_object* v_val_1798_, lean_object* v_s_1799_){
_start:
{
lean_object* v_res_1800_; 
v_res_1800_ = l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___lam__0(v_val_1798_, v_s_1799_);
lean_dec_ref(v_val_1798_);
return v_res_1800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f(lean_object* v_a_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_){
_start:
{
lean_object* v___x_1813_; 
v___x_1813_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_, v_a_1805_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_);
if (lean_obj_tag(v___x_1813_) == 0)
{
lean_object* v_a_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1853_; 
v_a_1814_ = lean_ctor_get(v___x_1813_, 0);
v_isSharedCheck_1853_ = !lean_is_exclusive(v___x_1813_);
if (v_isSharedCheck_1853_ == 0)
{
v___x_1816_ = v___x_1813_;
v_isShared_1817_ = v_isSharedCheck_1853_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_a_1814_);
lean_dec(v___x_1813_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1853_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v_queue_1818_; lean_object* v___x_1819_; 
v_queue_1818_ = lean_ctor_get(v_a_1814_, 10);
lean_inc(v_queue_1818_);
lean_dec(v_a_1814_);
v___x_1819_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_queue_1818_);
lean_dec(v_queue_1818_);
if (lean_obj_tag(v___x_1819_) == 1)
{
lean_object* v_val_1820_; lean_object* v___f_1821_; lean_object* v___x_1822_; 
lean_del_object(v___x_1816_);
v_val_1820_ = lean_ctor_get(v___x_1819_, 0);
lean_inc(v_val_1820_);
v___f_1821_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1821_, 0, v_val_1820_);
lean_inc_ref(v_a_1801_);
v___x_1822_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_1821_, v_a_1801_, v_a_1802_);
if (lean_obj_tag(v___x_1822_) == 0)
{
lean_object* v___x_1823_; lean_object* v___x_1824_; 
lean_dec_ref(v___x_1822_);
v___x_1823_ = lean_unsigned_to_nat(1u);
v___x_1824_ = l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg(v___x_1823_, v_a_1802_);
if (lean_obj_tag(v___x_1824_) == 0)
{
lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1831_; 
v_isSharedCheck_1831_ = !lean_is_exclusive(v___x_1824_);
if (v_isSharedCheck_1831_ == 0)
{
lean_object* v_unused_1832_; 
v_unused_1832_ = lean_ctor_get(v___x_1824_, 0);
lean_dec(v_unused_1832_);
v___x_1826_ = v___x_1824_;
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
else
{
lean_dec(v___x_1824_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v___x_1829_; 
if (v_isShared_1827_ == 0)
{
lean_ctor_set(v___x_1826_, 0, v___x_1819_);
v___x_1829_ = v___x_1826_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v___x_1819_);
v___x_1829_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
return v___x_1829_;
}
}
}
else
{
lean_object* v_a_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1840_; 
lean_dec_ref(v___x_1819_);
v_a_1833_ = lean_ctor_get(v___x_1824_, 0);
v_isSharedCheck_1840_ = !lean_is_exclusive(v___x_1824_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1835_ = v___x_1824_;
v_isShared_1836_ = v_isSharedCheck_1840_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_a_1833_);
lean_dec(v___x_1824_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1840_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v___x_1838_; 
if (v_isShared_1836_ == 0)
{
v___x_1838_ = v___x_1835_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v_a_1833_);
v___x_1838_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
return v___x_1838_;
}
}
}
}
else
{
lean_object* v_a_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1848_; 
lean_dec_ref(v___x_1819_);
v_a_1841_ = lean_ctor_get(v___x_1822_, 0);
v_isSharedCheck_1848_ = !lean_is_exclusive(v___x_1822_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1843_ = v___x_1822_;
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_a_1841_);
lean_dec(v___x_1822_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___x_1846_; 
if (v_isShared_1844_ == 0)
{
v___x_1846_ = v___x_1843_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v_a_1841_);
v___x_1846_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
return v___x_1846_;
}
}
}
}
else
{
lean_object* v___x_1849_; lean_object* v___x_1851_; 
lean_dec(v___x_1819_);
v___x_1849_ = lean_box(0);
if (v_isShared_1817_ == 0)
{
lean_ctor_set(v___x_1816_, 0, v___x_1849_);
v___x_1851_ = v___x_1816_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v___x_1849_);
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
lean_object* v_a_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1861_; 
v_a_1854_ = lean_ctor_get(v___x_1813_, 0);
v_isSharedCheck_1861_ = !lean_is_exclusive(v___x_1813_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1856_ = v___x_1813_;
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_a_1854_);
lean_dec(v___x_1813_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v___x_1859_; 
if (v_isShared_1857_ == 0)
{
v___x_1859_ = v___x_1856_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v_a_1854_);
v___x_1859_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
return v___x_1859_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___boxed(lean_object* v_a_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_){
_start:
{
lean_object* v_res_1874_; 
v_res_1874_ = l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f(v_a_1862_, v_a_1863_, v_a_1864_, v_a_1865_, v_a_1866_, v_a_1867_, v_a_1868_, v_a_1869_, v_a_1870_, v_a_1871_, v_a_1872_);
lean_dec(v_a_1872_);
lean_dec_ref(v_a_1871_);
lean_dec(v_a_1870_);
lean_dec_ref(v_a_1869_);
lean_dec(v_a_1868_);
lean_dec_ref(v_a_1867_);
lean_dec(v_a_1866_);
lean_dec_ref(v_a_1865_);
lean_dec(v_a_1864_);
lean_dec(v_a_1863_);
lean_dec_ref(v_a_1862_);
return v_res_1874_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0(lean_object* v_00_u03b2_1875_, lean_object* v_k_1876_, lean_object* v_t_1877_, lean_object* v_h_1878_){
_start:
{
lean_object* v___x_1879_; 
v___x_1879_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_k_1876_, v_t_1877_);
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___boxed(lean_object* v_00_u03b2_1880_, lean_object* v_k_1881_, lean_object* v_t_1882_, lean_object* v_h_1883_){
_start:
{
lean_object* v_res_1884_; 
v_res_1884_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0(v_00_u03b2_1880_, v_k_1881_, v_t_1882_, v_h_1883_);
lean_dec_ref(v_k_1881_);
return v_res_1884_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_1885_, lean_object* v_x_1886_, lean_object* v_x_1887_, lean_object* v_x_1888_){
_start:
{
lean_object* v_ks_1889_; lean_object* v_vs_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1914_; 
v_ks_1889_ = lean_ctor_get(v_x_1885_, 0);
v_vs_1890_ = lean_ctor_get(v_x_1885_, 1);
v_isSharedCheck_1914_ = !lean_is_exclusive(v_x_1885_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1892_ = v_x_1885_;
v_isShared_1893_ = v_isSharedCheck_1914_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_vs_1890_);
lean_inc(v_ks_1889_);
lean_dec(v_x_1885_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1914_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v___x_1894_; uint8_t v___x_1895_; 
v___x_1894_ = lean_array_get_size(v_ks_1889_);
v___x_1895_ = lean_nat_dec_lt(v_x_1886_, v___x_1894_);
if (v___x_1895_ == 0)
{
lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1899_; 
lean_dec(v_x_1886_);
v___x_1896_ = lean_array_push(v_ks_1889_, v_x_1887_);
v___x_1897_ = lean_array_push(v_vs_1890_, v_x_1888_);
if (v_isShared_1893_ == 0)
{
lean_ctor_set(v___x_1892_, 1, v___x_1897_);
lean_ctor_set(v___x_1892_, 0, v___x_1896_);
v___x_1899_ = v___x_1892_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v___x_1896_);
lean_ctor_set(v_reuseFailAlloc_1900_, 1, v___x_1897_);
v___x_1899_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
return v___x_1899_;
}
}
else
{
lean_object* v_k_x27_1901_; uint8_t v___x_1902_; 
v_k_x27_1901_ = lean_array_fget_borrowed(v_ks_1889_, v_x_1886_);
v___x_1902_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_1887_, v_k_x27_1901_);
if (v___x_1902_ == 0)
{
lean_object* v___x_1904_; 
if (v_isShared_1893_ == 0)
{
v___x_1904_ = v___x_1892_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v_ks_1889_);
lean_ctor_set(v_reuseFailAlloc_1908_, 1, v_vs_1890_);
v___x_1904_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
lean_object* v___x_1905_; lean_object* v___x_1906_; 
v___x_1905_ = lean_unsigned_to_nat(1u);
v___x_1906_ = lean_nat_add(v_x_1886_, v___x_1905_);
lean_dec(v_x_1886_);
v_x_1885_ = v___x_1904_;
v_x_1886_ = v___x_1906_;
goto _start;
}
}
else
{
lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1912_; 
v___x_1909_ = lean_array_fset(v_ks_1889_, v_x_1886_, v_x_1887_);
v___x_1910_ = lean_array_fset(v_vs_1890_, v_x_1886_, v_x_1888_);
lean_dec(v_x_1886_);
if (v_isShared_1893_ == 0)
{
lean_ctor_set(v___x_1892_, 1, v___x_1910_);
lean_ctor_set(v___x_1892_, 0, v___x_1909_);
v___x_1912_ = v___x_1892_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v___x_1909_);
lean_ctor_set(v_reuseFailAlloc_1913_, 1, v___x_1910_);
v___x_1912_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
return v___x_1912_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1___redArg(lean_object* v_n_1915_, lean_object* v_k_1916_, lean_object* v_v_1917_){
_start:
{
lean_object* v___x_1918_; lean_object* v___x_1919_; 
v___x_1918_ = lean_unsigned_to_nat(0u);
v___x_1919_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1915_, v___x_1918_, v_k_1916_, v_v_1917_);
return v___x_1919_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1920_; 
v___x_1920_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1920_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(lean_object* v_x_1921_, size_t v_x_1922_, size_t v_x_1923_, lean_object* v_x_1924_, lean_object* v_x_1925_){
_start:
{
if (lean_obj_tag(v_x_1921_) == 0)
{
lean_object* v_es_1926_; size_t v___x_1927_; size_t v___x_1928_; size_t v___x_1929_; size_t v___x_1930_; lean_object* v_j_1931_; lean_object* v___x_1932_; uint8_t v___x_1933_; 
v_es_1926_ = lean_ctor_get(v_x_1921_, 0);
v___x_1927_ = ((size_t)5ULL);
v___x_1928_ = ((size_t)1ULL);
v___x_1929_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__1);
v___x_1930_ = lean_usize_land(v_x_1922_, v___x_1929_);
v_j_1931_ = lean_usize_to_nat(v___x_1930_);
v___x_1932_ = lean_array_get_size(v_es_1926_);
v___x_1933_ = lean_nat_dec_lt(v_j_1931_, v___x_1932_);
if (v___x_1933_ == 0)
{
lean_dec(v_j_1931_);
lean_dec(v_x_1925_);
lean_dec_ref(v_x_1924_);
return v_x_1921_;
}
else
{
lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1970_; 
lean_inc_ref(v_es_1926_);
v_isSharedCheck_1970_ = !lean_is_exclusive(v_x_1921_);
if (v_isSharedCheck_1970_ == 0)
{
lean_object* v_unused_1971_; 
v_unused_1971_ = lean_ctor_get(v_x_1921_, 0);
lean_dec(v_unused_1971_);
v___x_1935_ = v_x_1921_;
v_isShared_1936_ = v_isSharedCheck_1970_;
goto v_resetjp_1934_;
}
else
{
lean_dec(v_x_1921_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1970_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v_v_1937_; lean_object* v___x_1938_; lean_object* v_xs_x27_1939_; lean_object* v___y_1941_; 
v_v_1937_ = lean_array_fget(v_es_1926_, v_j_1931_);
v___x_1938_ = lean_box(0);
v_xs_x27_1939_ = lean_array_fset(v_es_1926_, v_j_1931_, v___x_1938_);
switch(lean_obj_tag(v_v_1937_))
{
case 0:
{
lean_object* v_key_1946_; lean_object* v_val_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1957_; 
v_key_1946_ = lean_ctor_get(v_v_1937_, 0);
v_val_1947_ = lean_ctor_get(v_v_1937_, 1);
v_isSharedCheck_1957_ = !lean_is_exclusive(v_v_1937_);
if (v_isSharedCheck_1957_ == 0)
{
v___x_1949_ = v_v_1937_;
v_isShared_1950_ = v_isSharedCheck_1957_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_val_1947_);
lean_inc(v_key_1946_);
lean_dec(v_v_1937_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1957_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
uint8_t v___x_1951_; 
v___x_1951_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_1924_, v_key_1946_);
if (v___x_1951_ == 0)
{
lean_object* v___x_1952_; lean_object* v___x_1953_; 
lean_del_object(v___x_1949_);
v___x_1952_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1946_, v_val_1947_, v_x_1924_, v_x_1925_);
v___x_1953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1953_, 0, v___x_1952_);
v___y_1941_ = v___x_1953_;
goto v___jp_1940_;
}
else
{
lean_object* v___x_1955_; 
lean_dec(v_val_1947_);
lean_dec(v_key_1946_);
if (v_isShared_1950_ == 0)
{
lean_ctor_set(v___x_1949_, 1, v_x_1925_);
lean_ctor_set(v___x_1949_, 0, v_x_1924_);
v___x_1955_ = v___x_1949_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v_x_1924_);
lean_ctor_set(v_reuseFailAlloc_1956_, 1, v_x_1925_);
v___x_1955_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
v___y_1941_ = v___x_1955_;
goto v___jp_1940_;
}
}
}
}
case 1:
{
lean_object* v_node_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1968_; 
v_node_1958_ = lean_ctor_get(v_v_1937_, 0);
v_isSharedCheck_1968_ = !lean_is_exclusive(v_v_1937_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1960_ = v_v_1937_;
v_isShared_1961_ = v_isSharedCheck_1968_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_node_1958_);
lean_dec(v_v_1937_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1968_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
size_t v___x_1962_; size_t v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1966_; 
v___x_1962_ = lean_usize_shift_right(v_x_1922_, v___x_1927_);
v___x_1963_ = lean_usize_add(v_x_1923_, v___x_1928_);
v___x_1964_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_node_1958_, v___x_1962_, v___x_1963_, v_x_1924_, v_x_1925_);
if (v_isShared_1961_ == 0)
{
lean_ctor_set(v___x_1960_, 0, v___x_1964_);
v___x_1966_ = v___x_1960_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v___x_1964_);
v___x_1966_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
v___y_1941_ = v___x_1966_;
goto v___jp_1940_;
}
}
}
default: 
{
lean_object* v___x_1969_; 
v___x_1969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1969_, 0, v_x_1924_);
lean_ctor_set(v___x_1969_, 1, v_x_1925_);
v___y_1941_ = v___x_1969_;
goto v___jp_1940_;
}
}
v___jp_1940_:
{
lean_object* v___x_1942_; lean_object* v___x_1944_; 
v___x_1942_ = lean_array_fset(v_xs_x27_1939_, v_j_1931_, v___y_1941_);
lean_dec(v_j_1931_);
if (v_isShared_1936_ == 0)
{
lean_ctor_set(v___x_1935_, 0, v___x_1942_);
v___x_1944_ = v___x_1935_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v___x_1942_);
v___x_1944_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
return v___x_1944_;
}
}
}
}
}
else
{
lean_object* v_ks_1972_; lean_object* v_vs_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1993_; 
v_ks_1972_ = lean_ctor_get(v_x_1921_, 0);
v_vs_1973_ = lean_ctor_get(v_x_1921_, 1);
v_isSharedCheck_1993_ = !lean_is_exclusive(v_x_1921_);
if (v_isSharedCheck_1993_ == 0)
{
v___x_1975_ = v_x_1921_;
v_isShared_1976_ = v_isSharedCheck_1993_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_vs_1973_);
lean_inc(v_ks_1972_);
lean_dec(v_x_1921_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_1993_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v___x_1978_; 
if (v_isShared_1976_ == 0)
{
v___x_1978_ = v___x_1975_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v_ks_1972_);
lean_ctor_set(v_reuseFailAlloc_1992_, 1, v_vs_1973_);
v___x_1978_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
lean_object* v_newNode_1979_; uint8_t v___y_1981_; size_t v___x_1987_; uint8_t v___x_1988_; 
v_newNode_1979_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1___redArg(v___x_1978_, v_x_1924_, v_x_1925_);
v___x_1987_ = ((size_t)7ULL);
v___x_1988_ = lean_usize_dec_le(v___x_1987_, v_x_1923_);
if (v___x_1988_ == 0)
{
lean_object* v___x_1989_; lean_object* v___x_1990_; uint8_t v___x_1991_; 
v___x_1989_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1979_);
v___x_1990_ = lean_unsigned_to_nat(4u);
v___x_1991_ = lean_nat_dec_lt(v___x_1989_, v___x_1990_);
lean_dec(v___x_1989_);
v___y_1981_ = v___x_1991_;
goto v___jp_1980_;
}
else
{
v___y_1981_ = v___x_1988_;
goto v___jp_1980_;
}
v___jp_1980_:
{
if (v___y_1981_ == 0)
{
lean_object* v_ks_1982_; lean_object* v_vs_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; 
v_ks_1982_ = lean_ctor_get(v_newNode_1979_, 0);
lean_inc_ref(v_ks_1982_);
v_vs_1983_ = lean_ctor_get(v_newNode_1979_, 1);
lean_inc_ref(v_vs_1983_);
lean_dec_ref(v_newNode_1979_);
v___x_1984_ = lean_unsigned_to_nat(0u);
v___x_1985_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0);
v___x_1986_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg(v_x_1923_, v_ks_1982_, v_vs_1983_, v___x_1984_, v___x_1985_);
lean_dec_ref(v_vs_1983_);
lean_dec_ref(v_ks_1982_);
return v___x_1986_;
}
else
{
return v_newNode_1979_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg(size_t v_depth_1994_, lean_object* v_keys_1995_, lean_object* v_vals_1996_, lean_object* v_i_1997_, lean_object* v_entries_1998_){
_start:
{
lean_object* v___x_1999_; uint8_t v___x_2000_; 
v___x_1999_ = lean_array_get_size(v_keys_1995_);
v___x_2000_ = lean_nat_dec_lt(v_i_1997_, v___x_1999_);
if (v___x_2000_ == 0)
{
lean_dec(v_i_1997_);
return v_entries_1998_;
}
else
{
lean_object* v_k_2001_; lean_object* v_v_2002_; uint64_t v___x_2003_; size_t v_h_2004_; size_t v___x_2005_; lean_object* v___x_2006_; size_t v___x_2007_; size_t v___x_2008_; size_t v___x_2009_; size_t v_h_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; 
v_k_2001_ = lean_array_fget_borrowed(v_keys_1995_, v_i_1997_);
v_v_2002_ = lean_array_fget_borrowed(v_vals_1996_, v_i_1997_);
v___x_2003_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_2001_);
v_h_2004_ = lean_uint64_to_usize(v___x_2003_);
v___x_2005_ = ((size_t)5ULL);
v___x_2006_ = lean_unsigned_to_nat(1u);
v___x_2007_ = ((size_t)1ULL);
v___x_2008_ = lean_usize_sub(v_depth_1994_, v___x_2007_);
v___x_2009_ = lean_usize_mul(v___x_2005_, v___x_2008_);
v_h_2010_ = lean_usize_shift_right(v_h_2004_, v___x_2009_);
v___x_2011_ = lean_nat_add(v_i_1997_, v___x_2006_);
lean_dec(v_i_1997_);
lean_inc(v_v_2002_);
lean_inc(v_k_2001_);
v___x_2012_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_entries_1998_, v_h_2010_, v_depth_1994_, v_k_2001_, v_v_2002_);
v_i_1997_ = v___x_2011_;
v_entries_1998_ = v___x_2012_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_2014_, lean_object* v_keys_2015_, lean_object* v_vals_2016_, lean_object* v_i_2017_, lean_object* v_entries_2018_){
_start:
{
size_t v_depth_boxed_2019_; lean_object* v_res_2020_; 
v_depth_boxed_2019_ = lean_unbox_usize(v_depth_2014_);
lean_dec(v_depth_2014_);
v_res_2020_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg(v_depth_boxed_2019_, v_keys_2015_, v_vals_2016_, v_i_2017_, v_entries_2018_);
lean_dec_ref(v_vals_2016_);
lean_dec_ref(v_keys_2015_);
return v_res_2020_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___boxed(lean_object* v_x_2021_, lean_object* v_x_2022_, lean_object* v_x_2023_, lean_object* v_x_2024_, lean_object* v_x_2025_){
_start:
{
size_t v_x_8495__boxed_2026_; size_t v_x_8496__boxed_2027_; lean_object* v_res_2028_; 
v_x_8495__boxed_2026_ = lean_unbox_usize(v_x_2022_);
lean_dec(v_x_2022_);
v_x_8496__boxed_2027_ = lean_unbox_usize(v_x_2023_);
lean_dec(v_x_2023_);
v_res_2028_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_x_2021_, v_x_8495__boxed_2026_, v_x_8496__boxed_2027_, v_x_2024_, v_x_2025_);
return v_res_2028_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0___redArg(lean_object* v_x_2029_, lean_object* v_x_2030_, lean_object* v_x_2031_){
_start:
{
uint64_t v___x_2032_; size_t v___x_2033_; size_t v___x_2034_; lean_object* v___x_2035_; 
v___x_2032_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_2030_);
v___x_2033_ = lean_uint64_to_usize(v___x_2032_);
v___x_2034_ = ((size_t)1ULL);
v___x_2035_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_x_2029_, v___x_2033_, v___x_2034_, v_x_2030_, v_x_2031_);
return v___x_2035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___lam__0(lean_object* v_e_2036_, lean_object* v_ringId_2037_, lean_object* v_s_2038_){
_start:
{
lean_object* v_rings_2039_; lean_object* v_typeIdOf_2040_; lean_object* v_exprToRingId_2041_; lean_object* v_semirings_2042_; lean_object* v_stypeIdOf_2043_; lean_object* v_exprToSemiringId_2044_; lean_object* v_ncRings_2045_; lean_object* v_exprToNCRingId_2046_; lean_object* v_nctypeIdOf_2047_; lean_object* v_ncSemirings_2048_; lean_object* v_exprToNCSemiringId_2049_; lean_object* v_ncstypeIdOf_2050_; lean_object* v_steps_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2059_; 
v_rings_2039_ = lean_ctor_get(v_s_2038_, 0);
v_typeIdOf_2040_ = lean_ctor_get(v_s_2038_, 1);
v_exprToRingId_2041_ = lean_ctor_get(v_s_2038_, 2);
v_semirings_2042_ = lean_ctor_get(v_s_2038_, 3);
v_stypeIdOf_2043_ = lean_ctor_get(v_s_2038_, 4);
v_exprToSemiringId_2044_ = lean_ctor_get(v_s_2038_, 5);
v_ncRings_2045_ = lean_ctor_get(v_s_2038_, 6);
v_exprToNCRingId_2046_ = lean_ctor_get(v_s_2038_, 7);
v_nctypeIdOf_2047_ = lean_ctor_get(v_s_2038_, 8);
v_ncSemirings_2048_ = lean_ctor_get(v_s_2038_, 9);
v_exprToNCSemiringId_2049_ = lean_ctor_get(v_s_2038_, 10);
v_ncstypeIdOf_2050_ = lean_ctor_get(v_s_2038_, 11);
v_steps_2051_ = lean_ctor_get(v_s_2038_, 12);
v_isSharedCheck_2059_ = !lean_is_exclusive(v_s_2038_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_2053_ = v_s_2038_;
v_isShared_2054_ = v_isSharedCheck_2059_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_steps_2051_);
lean_inc(v_ncstypeIdOf_2050_);
lean_inc(v_exprToNCSemiringId_2049_);
lean_inc(v_ncSemirings_2048_);
lean_inc(v_nctypeIdOf_2047_);
lean_inc(v_exprToNCRingId_2046_);
lean_inc(v_ncRings_2045_);
lean_inc(v_exprToSemiringId_2044_);
lean_inc(v_stypeIdOf_2043_);
lean_inc(v_semirings_2042_);
lean_inc(v_exprToRingId_2041_);
lean_inc(v_typeIdOf_2040_);
lean_inc(v_rings_2039_);
lean_dec(v_s_2038_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2059_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2055_; lean_object* v___x_2057_; 
v___x_2055_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0___redArg(v_exprToRingId_2041_, v_e_2036_, v_ringId_2037_);
if (v_isShared_2054_ == 0)
{
lean_ctor_set(v___x_2053_, 2, v___x_2055_);
v___x_2057_ = v___x_2053_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_2058_, 0, v_rings_2039_);
lean_ctor_set(v_reuseFailAlloc_2058_, 1, v_typeIdOf_2040_);
lean_ctor_set(v_reuseFailAlloc_2058_, 2, v___x_2055_);
lean_ctor_set(v_reuseFailAlloc_2058_, 3, v_semirings_2042_);
lean_ctor_set(v_reuseFailAlloc_2058_, 4, v_stypeIdOf_2043_);
lean_ctor_set(v_reuseFailAlloc_2058_, 5, v_exprToSemiringId_2044_);
lean_ctor_set(v_reuseFailAlloc_2058_, 6, v_ncRings_2045_);
lean_ctor_set(v_reuseFailAlloc_2058_, 7, v_exprToNCRingId_2046_);
lean_ctor_set(v_reuseFailAlloc_2058_, 8, v_nctypeIdOf_2047_);
lean_ctor_set(v_reuseFailAlloc_2058_, 9, v_ncSemirings_2048_);
lean_ctor_set(v_reuseFailAlloc_2058_, 10, v_exprToNCSemiringId_2049_);
lean_ctor_set(v_reuseFailAlloc_2058_, 11, v_ncstypeIdOf_2050_);
lean_ctor_set(v_reuseFailAlloc_2058_, 12, v_steps_2051_);
v___x_2057_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
return v___x_2057_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___closed__1(void){
_start:
{
lean_object* v___x_2061_; lean_object* v___x_2062_; 
v___x_2061_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___closed__0));
v___x_2062_ = l_Lean_stringToMessageData(v___x_2061_);
return v___x_2062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId(lean_object* v_e_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_, lean_object* v_a_2073_, lean_object* v_a_2074_){
_start:
{
lean_object* v___x_2079_; 
v___x_2079_ = l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg(v_e_2063_, v_a_2065_, v_a_2073_);
if (lean_obj_tag(v___x_2079_) == 0)
{
lean_object* v_a_2080_; 
v_a_2080_ = lean_ctor_get(v___x_2079_, 0);
lean_inc(v_a_2080_);
lean_dec_ref(v___x_2079_);
if (lean_obj_tag(v_a_2080_) == 1)
{
lean_object* v_ringId_2081_; lean_object* v_val_2082_; uint8_t v___x_2083_; 
v_ringId_2081_ = lean_ctor_get(v_a_2064_, 0);
lean_inc(v_ringId_2081_);
lean_dec_ref(v_a_2064_);
v_val_2082_ = lean_ctor_get(v_a_2080_, 0);
lean_inc(v_val_2082_);
lean_dec_ref(v_a_2080_);
v___x_2083_ = lean_nat_dec_eq(v_val_2082_, v_ringId_2081_);
lean_dec(v_ringId_2081_);
lean_dec(v_val_2082_);
if (v___x_2083_ == 0)
{
lean_object* v___x_2084_; 
v___x_2084_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_2067_);
if (lean_obj_tag(v___x_2084_) == 0)
{
lean_object* v_a_2085_; uint8_t v_verbose_2086_; 
v_a_2085_ = lean_ctor_get(v___x_2084_, 0);
lean_inc(v_a_2085_);
lean_dec_ref(v___x_2084_);
v_verbose_2086_ = lean_ctor_get_uint8(v_a_2085_, sizeof(void*)*11 + 15);
lean_dec(v_a_2085_);
if (v_verbose_2086_ == 0)
{
lean_dec_ref(v_e_2063_);
goto v___jp_2076_;
}
else
{
lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; 
v___x_2087_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___closed__1);
v___x_2088_ = l_Lean_indentExpr(v_e_2063_);
v___x_2089_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2089_, 0, v___x_2087_);
lean_ctor_set(v___x_2089_, 1, v___x_2088_);
v___x_2090_ = l_Lean_Meta_Grind_reportIssue(v___x_2089_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_, v_a_2073_, v_a_2074_);
if (lean_obj_tag(v___x_2090_) == 0)
{
lean_dec_ref(v___x_2090_);
goto v___jp_2076_;
}
else
{
return v___x_2090_;
}
}
}
else
{
lean_object* v_a_2091_; lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2098_; 
lean_dec_ref(v_e_2063_);
v_a_2091_ = lean_ctor_get(v___x_2084_, 0);
v_isSharedCheck_2098_ = !lean_is_exclusive(v___x_2084_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2093_ = v___x_2084_;
v_isShared_2094_ = v_isSharedCheck_2098_;
goto v_resetjp_2092_;
}
else
{
lean_inc(v_a_2091_);
lean_dec(v___x_2084_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2098_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
lean_object* v___x_2096_; 
if (v_isShared_2094_ == 0)
{
v___x_2096_ = v___x_2093_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_a_2091_);
v___x_2096_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
return v___x_2096_;
}
}
}
}
else
{
lean_dec_ref(v_e_2063_);
goto v___jp_2076_;
}
}
else
{
lean_object* v_ringId_2099_; lean_object* v___f_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; 
lean_dec(v_a_2080_);
v_ringId_2099_ = lean_ctor_get(v_a_2064_, 0);
lean_inc(v_ringId_2099_);
lean_dec_ref(v_a_2064_);
v___f_2100_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___lam__0), 3, 2);
lean_closure_set(v___f_2100_, 0, v_e_2063_);
lean_closure_set(v___f_2100_, 1, v_ringId_2099_);
v___x_2101_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_2102_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2101_, v___f_2100_, v_a_2065_);
return v___x_2102_;
}
}
else
{
lean_object* v_a_2103_; lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2110_; 
lean_dec_ref(v_a_2064_);
lean_dec_ref(v_e_2063_);
v_a_2103_ = lean_ctor_get(v___x_2079_, 0);
v_isSharedCheck_2110_ = !lean_is_exclusive(v___x_2079_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2105_ = v___x_2079_;
v_isShared_2106_ = v_isSharedCheck_2110_;
goto v_resetjp_2104_;
}
else
{
lean_inc(v_a_2103_);
lean_dec(v___x_2079_);
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
v___jp_2076_:
{
lean_object* v___x_2077_; lean_object* v___x_2078_; 
v___x_2077_ = lean_box(0);
v___x_2078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2078_, 0, v___x_2077_);
return v___x_2078_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___boxed(lean_object* v_e_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_){
_start:
{
lean_object* v_res_2124_; 
v_res_2124_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId(v_e_2111_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_, v_a_2121_, v_a_2122_);
lean_dec(v_a_2122_);
lean_dec_ref(v_a_2121_);
lean_dec(v_a_2120_);
lean_dec_ref(v_a_2119_);
lean_dec(v_a_2118_);
lean_dec_ref(v_a_2117_);
lean_dec(v_a_2116_);
lean_dec_ref(v_a_2115_);
lean_dec(v_a_2114_);
lean_dec(v_a_2113_);
return v_res_2124_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0(lean_object* v_00_u03b2_2125_, lean_object* v_x_2126_, lean_object* v_x_2127_, lean_object* v_x_2128_){
_start:
{
lean_object* v___x_2129_; 
v___x_2129_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0___redArg(v_x_2126_, v_x_2127_, v_x_2128_);
return v___x_2129_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0(lean_object* v_00_u03b2_2130_, lean_object* v_x_2131_, size_t v_x_2132_, size_t v_x_2133_, lean_object* v_x_2134_, lean_object* v_x_2135_){
_start:
{
lean_object* v___x_2136_; 
v___x_2136_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_x_2131_, v_x_2132_, v_x_2133_, v_x_2134_, v_x_2135_);
return v___x_2136_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2137_, lean_object* v_x_2138_, lean_object* v_x_2139_, lean_object* v_x_2140_, lean_object* v_x_2141_, lean_object* v_x_2142_){
_start:
{
size_t v_x_8767__boxed_2143_; size_t v_x_8768__boxed_2144_; lean_object* v_res_2145_; 
v_x_8767__boxed_2143_ = lean_unbox_usize(v_x_2139_);
lean_dec(v_x_2139_);
v_x_8768__boxed_2144_ = lean_unbox_usize(v_x_2140_);
lean_dec(v_x_2140_);
v_res_2145_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0(v_00_u03b2_2137_, v_x_2138_, v_x_8767__boxed_2143_, v_x_8768__boxed_2144_, v_x_2141_, v_x_2142_);
return v_res_2145_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2146_, lean_object* v_n_2147_, lean_object* v_k_2148_, lean_object* v_v_2149_){
_start:
{
lean_object* v___x_2150_; 
v___x_2150_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1___redArg(v_n_2147_, v_k_2148_, v_v_2149_);
return v___x_2150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_2151_, size_t v_depth_2152_, lean_object* v_keys_2153_, lean_object* v_vals_2154_, lean_object* v_heq_2155_, lean_object* v_i_2156_, lean_object* v_entries_2157_){
_start:
{
lean_object* v___x_2158_; 
v___x_2158_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg(v_depth_2152_, v_keys_2153_, v_vals_2154_, v_i_2156_, v_entries_2157_);
return v___x_2158_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2159_, lean_object* v_depth_2160_, lean_object* v_keys_2161_, lean_object* v_vals_2162_, lean_object* v_heq_2163_, lean_object* v_i_2164_, lean_object* v_entries_2165_){
_start:
{
size_t v_depth_boxed_2166_; lean_object* v_res_2167_; 
v_depth_boxed_2166_ = lean_unbox_usize(v_depth_2160_);
lean_dec(v_depth_2160_);
v_res_2167_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2(v_00_u03b2_2159_, v_depth_boxed_2166_, v_keys_2161_, v_vals_2162_, v_heq_2163_, v_i_2164_, v_entries_2165_);
lean_dec_ref(v_vals_2162_);
lean_dec_ref(v_keys_2161_);
return v_res_2167_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2168_, lean_object* v_x_2169_, lean_object* v_x_2170_, lean_object* v_x_2171_, lean_object* v_x_2172_){
_start:
{
lean_object* v___x_2173_; 
v___x_2173_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1_spec__2___redArg(v_x_2169_, v_x_2170_, v_x_2171_, v_x_2172_);
return v___x_2173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__0(lean_object* v_e_2174_, lean_object* v___f_2175_, lean_object* v___f_2176_, lean_object* v_size_2177_, lean_object* v_s_2178_){
_start:
{
lean_object* v_id_2179_; lean_object* v_type_2180_; lean_object* v_u_2181_; lean_object* v_ringInst_2182_; lean_object* v_semiringInst_2183_; lean_object* v_charInst_x3f_2184_; lean_object* v_addFn_x3f_2185_; lean_object* v_mulFn_x3f_2186_; lean_object* v_subFn_x3f_2187_; lean_object* v_negFn_x3f_2188_; lean_object* v_powFn_x3f_2189_; lean_object* v_intCastFn_x3f_2190_; lean_object* v_natCastFn_x3f_2191_; lean_object* v_one_x3f_2192_; lean_object* v_vars_2193_; lean_object* v_varMap_2194_; lean_object* v_denote_2195_; lean_object* v___x_2197_; uint8_t v_isShared_2198_; uint8_t v_isSharedCheck_2204_; 
v_id_2179_ = lean_ctor_get(v_s_2178_, 0);
v_type_2180_ = lean_ctor_get(v_s_2178_, 1);
v_u_2181_ = lean_ctor_get(v_s_2178_, 2);
v_ringInst_2182_ = lean_ctor_get(v_s_2178_, 3);
v_semiringInst_2183_ = lean_ctor_get(v_s_2178_, 4);
v_charInst_x3f_2184_ = lean_ctor_get(v_s_2178_, 5);
v_addFn_x3f_2185_ = lean_ctor_get(v_s_2178_, 6);
v_mulFn_x3f_2186_ = lean_ctor_get(v_s_2178_, 7);
v_subFn_x3f_2187_ = lean_ctor_get(v_s_2178_, 8);
v_negFn_x3f_2188_ = lean_ctor_get(v_s_2178_, 9);
v_powFn_x3f_2189_ = lean_ctor_get(v_s_2178_, 10);
v_intCastFn_x3f_2190_ = lean_ctor_get(v_s_2178_, 11);
v_natCastFn_x3f_2191_ = lean_ctor_get(v_s_2178_, 12);
v_one_x3f_2192_ = lean_ctor_get(v_s_2178_, 13);
v_vars_2193_ = lean_ctor_get(v_s_2178_, 14);
v_varMap_2194_ = lean_ctor_get(v_s_2178_, 15);
v_denote_2195_ = lean_ctor_get(v_s_2178_, 16);
v_isSharedCheck_2204_ = !lean_is_exclusive(v_s_2178_);
if (v_isSharedCheck_2204_ == 0)
{
v___x_2197_ = v_s_2178_;
v_isShared_2198_ = v_isSharedCheck_2204_;
goto v_resetjp_2196_;
}
else
{
lean_inc(v_denote_2195_);
lean_inc(v_varMap_2194_);
lean_inc(v_vars_2193_);
lean_inc(v_one_x3f_2192_);
lean_inc(v_natCastFn_x3f_2191_);
lean_inc(v_intCastFn_x3f_2190_);
lean_inc(v_powFn_x3f_2189_);
lean_inc(v_negFn_x3f_2188_);
lean_inc(v_subFn_x3f_2187_);
lean_inc(v_mulFn_x3f_2186_);
lean_inc(v_addFn_x3f_2185_);
lean_inc(v_charInst_x3f_2184_);
lean_inc(v_semiringInst_2183_);
lean_inc(v_ringInst_2182_);
lean_inc(v_u_2181_);
lean_inc(v_type_2180_);
lean_inc(v_id_2179_);
lean_dec(v_s_2178_);
v___x_2197_ = lean_box(0);
v_isShared_2198_ = v_isSharedCheck_2204_;
goto v_resetjp_2196_;
}
v_resetjp_2196_:
{
lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2202_; 
lean_inc_ref(v_e_2174_);
v___x_2199_ = l_Lean_PersistentArray_push___redArg(v_vars_2193_, v_e_2174_);
v___x_2200_ = l_Lean_PersistentHashMap_insert___redArg(v___f_2175_, v___f_2176_, v_varMap_2194_, v_e_2174_, v_size_2177_);
if (v_isShared_2198_ == 0)
{
lean_ctor_set(v___x_2197_, 15, v___x_2200_);
lean_ctor_set(v___x_2197_, 14, v___x_2199_);
v___x_2202_ = v___x_2197_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v_id_2179_);
lean_ctor_set(v_reuseFailAlloc_2203_, 1, v_type_2180_);
lean_ctor_set(v_reuseFailAlloc_2203_, 2, v_u_2181_);
lean_ctor_set(v_reuseFailAlloc_2203_, 3, v_ringInst_2182_);
lean_ctor_set(v_reuseFailAlloc_2203_, 4, v_semiringInst_2183_);
lean_ctor_set(v_reuseFailAlloc_2203_, 5, v_charInst_x3f_2184_);
lean_ctor_set(v_reuseFailAlloc_2203_, 6, v_addFn_x3f_2185_);
lean_ctor_set(v_reuseFailAlloc_2203_, 7, v_mulFn_x3f_2186_);
lean_ctor_set(v_reuseFailAlloc_2203_, 8, v_subFn_x3f_2187_);
lean_ctor_set(v_reuseFailAlloc_2203_, 9, v_negFn_x3f_2188_);
lean_ctor_set(v_reuseFailAlloc_2203_, 10, v_powFn_x3f_2189_);
lean_ctor_set(v_reuseFailAlloc_2203_, 11, v_intCastFn_x3f_2190_);
lean_ctor_set(v_reuseFailAlloc_2203_, 12, v_natCastFn_x3f_2191_);
lean_ctor_set(v_reuseFailAlloc_2203_, 13, v_one_x3f_2192_);
lean_ctor_set(v_reuseFailAlloc_2203_, 14, v___x_2199_);
lean_ctor_set(v_reuseFailAlloc_2203_, 15, v___x_2200_);
lean_ctor_set(v_reuseFailAlloc_2203_, 16, v_denote_2195_);
v___x_2202_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
return v___x_2202_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__1(lean_object* v_toPure_2205_, lean_object* v_size_2206_, lean_object* v_____r_2207_){
_start:
{
lean_object* v___x_2208_; 
v___x_2208_ = lean_apply_2(v_toPure_2205_, lean_box(0), v_size_2206_);
return v___x_2208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__2(lean_object* v_e_2209_, lean_object* v_inst_2210_, lean_object* v_toBind_2211_, lean_object* v___f_2212_, lean_object* v_____r_2213_){
_start:
{
lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; 
v___x_2214_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_2215_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_SolverExtension_markTerm___boxed), 14, 3);
lean_closure_set(v___x_2215_, 0, lean_box(0));
lean_closure_set(v___x_2215_, 1, v___x_2214_);
lean_closure_set(v___x_2215_, 2, v_e_2209_);
v___x_2216_ = lean_apply_2(v_inst_2210_, lean_box(0), v___x_2215_);
v___x_2217_ = lean_apply_4(v_toBind_2211_, lean_box(0), lean_box(0), v___x_2216_, v___f_2212_);
return v___x_2217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__3(lean_object* v_inst_2218_, lean_object* v_e_2219_, lean_object* v_toBind_2220_, lean_object* v___f_2221_, lean_object* v_____r_2222_){
_start:
{
lean_object* v___x_2223_; lean_object* v___x_2224_; 
v___x_2223_ = lean_apply_1(v_inst_2218_, v_e_2219_);
v___x_2224_ = lean_apply_4(v_toBind_2220_, lean_box(0), lean_box(0), v___x_2223_, v___f_2221_);
return v___x_2224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__4(lean_object* v___f_2225_, lean_object* v___f_2226_, lean_object* v_e_2227_, lean_object* v_toPure_2228_, lean_object* v_inst_2229_, lean_object* v_toBind_2230_, lean_object* v_inst_2231_, lean_object* v_modifyRing_2232_, lean_object* v_s_2233_){
_start:
{
lean_object* v_vars_2234_; lean_object* v_varMap_2235_; lean_object* v___x_2236_; 
v_vars_2234_ = lean_ctor_get(v_s_2233_, 14);
lean_inc_ref(v_vars_2234_);
v_varMap_2235_ = lean_ctor_get(v_s_2233_, 15);
lean_inc_ref(v_varMap_2235_);
lean_dec_ref(v_s_2233_);
lean_inc_ref(v_e_2227_);
lean_inc_ref(v___f_2226_);
lean_inc_ref(v___f_2225_);
v___x_2236_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_2225_, v___f_2226_, v_varMap_2235_, v_e_2227_);
if (lean_obj_tag(v___x_2236_) == 1)
{
lean_object* v_val_2237_; lean_object* v___x_2238_; 
lean_dec_ref(v_vars_2234_);
lean_dec(v_modifyRing_2232_);
lean_dec(v_inst_2231_);
lean_dec(v_toBind_2230_);
lean_dec(v_inst_2229_);
lean_dec_ref(v_e_2227_);
lean_dec_ref(v___f_2226_);
lean_dec_ref(v___f_2225_);
v_val_2237_ = lean_ctor_get(v___x_2236_, 0);
lean_inc(v_val_2237_);
lean_dec_ref(v___x_2236_);
v___x_2238_ = lean_apply_2(v_toPure_2228_, lean_box(0), v_val_2237_);
return v___x_2238_;
}
else
{
lean_object* v_size_2239_; lean_object* v___f_2240_; lean_object* v___f_2241_; lean_object* v___f_2242_; lean_object* v___f_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; 
lean_dec(v___x_2236_);
v_size_2239_ = lean_ctor_get(v_vars_2234_, 2);
lean_inc(v_size_2239_);
lean_dec_ref(v_vars_2234_);
lean_inc(v_size_2239_);
lean_inc_ref(v_e_2227_);
v___f_2240_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2240_, 0, v_e_2227_);
lean_closure_set(v___f_2240_, 1, v___f_2225_);
lean_closure_set(v___f_2240_, 2, v___f_2226_);
lean_closure_set(v___f_2240_, 3, v_size_2239_);
v___f_2241_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2241_, 0, v_toPure_2228_);
lean_closure_set(v___f_2241_, 1, v_size_2239_);
lean_inc(v_toBind_2230_);
lean_inc_ref(v_e_2227_);
v___f_2242_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2242_, 0, v_e_2227_);
lean_closure_set(v___f_2242_, 1, v_inst_2229_);
lean_closure_set(v___f_2242_, 2, v_toBind_2230_);
lean_closure_set(v___f_2242_, 3, v___f_2241_);
lean_inc(v_toBind_2230_);
v___f_2243_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__3), 5, 4);
lean_closure_set(v___f_2243_, 0, v_inst_2231_);
lean_closure_set(v___f_2243_, 1, v_e_2227_);
lean_closure_set(v___f_2243_, 2, v_toBind_2230_);
lean_closure_set(v___f_2243_, 3, v___f_2242_);
v___x_2244_ = lean_apply_1(v_modifyRing_2232_, v___f_2240_);
v___x_2245_ = lean_apply_4(v_toBind_2230_, lean_box(0), lean_box(0), v___x_2244_, v___f_2243_);
return v___x_2245_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg(lean_object* v_inst_2248_, lean_object* v_inst_2249_, lean_object* v_inst_2250_, lean_object* v_inst_2251_, lean_object* v_e_2252_){
_start:
{
lean_object* v_toApplicative_2253_; lean_object* v_toBind_2254_; lean_object* v_getRing_2255_; lean_object* v_modifyRing_2256_; lean_object* v_toPure_2257_; lean_object* v___f_2258_; lean_object* v___f_2259_; lean_object* v___f_2260_; lean_object* v___x_2261_; 
v_toApplicative_2253_ = lean_ctor_get(v_inst_2249_, 0);
lean_inc_ref(v_toApplicative_2253_);
v_toBind_2254_ = lean_ctor_get(v_inst_2249_, 1);
lean_inc(v_toBind_2254_);
lean_dec_ref(v_inst_2249_);
v_getRing_2255_ = lean_ctor_get(v_inst_2250_, 0);
lean_inc(v_getRing_2255_);
v_modifyRing_2256_ = lean_ctor_get(v_inst_2250_, 1);
lean_inc(v_modifyRing_2256_);
lean_dec_ref(v_inst_2250_);
v_toPure_2257_ = lean_ctor_get(v_toApplicative_2253_, 1);
lean_inc(v_toPure_2257_);
lean_dec_ref(v_toApplicative_2253_);
v___f_2258_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___closed__0));
v___f_2259_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___closed__1));
lean_inc(v_toBind_2254_);
v___f_2260_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__4), 9, 8);
lean_closure_set(v___f_2260_, 0, v___f_2258_);
lean_closure_set(v___f_2260_, 1, v___f_2259_);
lean_closure_set(v___f_2260_, 2, v_e_2252_);
lean_closure_set(v___f_2260_, 3, v_toPure_2257_);
lean_closure_set(v___f_2260_, 4, v_inst_2248_);
lean_closure_set(v___f_2260_, 5, v_toBind_2254_);
lean_closure_set(v___f_2260_, 6, v_inst_2251_);
lean_closure_set(v___f_2260_, 7, v_modifyRing_2256_);
v___x_2261_ = lean_apply_4(v_toBind_2254_, lean_box(0), lean_box(0), v_getRing_2255_, v___f_2260_);
return v___x_2261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore(lean_object* v_m_2262_, lean_object* v_inst_2263_, lean_object* v_inst_2264_, lean_object* v_inst_2265_, lean_object* v_inst_2266_, lean_object* v_e_2267_){
_start:
{
lean_object* v___x_2268_; 
v___x_2268_ = l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg(v_inst_2263_, v_inst_2264_, v_inst_2265_, v_inst_2266_, v_e_2267_);
return v___x_2268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkVar_spec__0___lam__0(lean_object* v_e_2271_, lean_object* v_size_2272_, lean_object* v_s_2273_){
_start:
{
lean_object* v_toRing_2274_; lean_object* v_invFn_x3f_2275_; lean_object* v_semiringId_x3f_2276_; lean_object* v_commSemiringInst_2277_; lean_object* v_commRingInst_2278_; lean_object* v_noZeroDivInst_x3f_2279_; lean_object* v_fieldInst_x3f_2280_; lean_object* v_denoteEntries_2281_; lean_object* v_nextId_2282_; lean_object* v_steps_2283_; lean_object* v_queue_2284_; lean_object* v_basis_2285_; lean_object* v_diseqs_2286_; uint8_t v_recheck_2287_; lean_object* v_invSet_2288_; lean_object* v_numEq0_x3f_2289_; uint8_t v_numEq0Updated_2290_; lean_object* v___x_2292_; uint8_t v_isShared_2293_; uint8_t v_isSharedCheck_2323_; 
v_toRing_2274_ = lean_ctor_get(v_s_2273_, 0);
v_invFn_x3f_2275_ = lean_ctor_get(v_s_2273_, 1);
v_semiringId_x3f_2276_ = lean_ctor_get(v_s_2273_, 2);
v_commSemiringInst_2277_ = lean_ctor_get(v_s_2273_, 3);
v_commRingInst_2278_ = lean_ctor_get(v_s_2273_, 4);
v_noZeroDivInst_x3f_2279_ = lean_ctor_get(v_s_2273_, 5);
v_fieldInst_x3f_2280_ = lean_ctor_get(v_s_2273_, 6);
v_denoteEntries_2281_ = lean_ctor_get(v_s_2273_, 7);
v_nextId_2282_ = lean_ctor_get(v_s_2273_, 8);
v_steps_2283_ = lean_ctor_get(v_s_2273_, 9);
v_queue_2284_ = lean_ctor_get(v_s_2273_, 10);
v_basis_2285_ = lean_ctor_get(v_s_2273_, 11);
v_diseqs_2286_ = lean_ctor_get(v_s_2273_, 12);
v_recheck_2287_ = lean_ctor_get_uint8(v_s_2273_, sizeof(void*)*15);
v_invSet_2288_ = lean_ctor_get(v_s_2273_, 13);
v_numEq0_x3f_2289_ = lean_ctor_get(v_s_2273_, 14);
v_numEq0Updated_2290_ = lean_ctor_get_uint8(v_s_2273_, sizeof(void*)*15 + 1);
v_isSharedCheck_2323_ = !lean_is_exclusive(v_s_2273_);
if (v_isSharedCheck_2323_ == 0)
{
v___x_2292_ = v_s_2273_;
v_isShared_2293_ = v_isSharedCheck_2323_;
goto v_resetjp_2291_;
}
else
{
lean_inc(v_numEq0_x3f_2289_);
lean_inc(v_invSet_2288_);
lean_inc(v_diseqs_2286_);
lean_inc(v_basis_2285_);
lean_inc(v_queue_2284_);
lean_inc(v_steps_2283_);
lean_inc(v_nextId_2282_);
lean_inc(v_denoteEntries_2281_);
lean_inc(v_fieldInst_x3f_2280_);
lean_inc(v_noZeroDivInst_x3f_2279_);
lean_inc(v_commRingInst_2278_);
lean_inc(v_commSemiringInst_2277_);
lean_inc(v_semiringId_x3f_2276_);
lean_inc(v_invFn_x3f_2275_);
lean_inc(v_toRing_2274_);
lean_dec(v_s_2273_);
v___x_2292_ = lean_box(0);
v_isShared_2293_ = v_isSharedCheck_2323_;
goto v_resetjp_2291_;
}
v_resetjp_2291_:
{
lean_object* v_id_2294_; lean_object* v_type_2295_; lean_object* v_u_2296_; lean_object* v_ringInst_2297_; lean_object* v_semiringInst_2298_; lean_object* v_charInst_x3f_2299_; lean_object* v_addFn_x3f_2300_; lean_object* v_mulFn_x3f_2301_; lean_object* v_subFn_x3f_2302_; lean_object* v_negFn_x3f_2303_; lean_object* v_powFn_x3f_2304_; lean_object* v_intCastFn_x3f_2305_; lean_object* v_natCastFn_x3f_2306_; lean_object* v_one_x3f_2307_; lean_object* v_vars_2308_; lean_object* v_varMap_2309_; lean_object* v_denote_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2322_; 
v_id_2294_ = lean_ctor_get(v_toRing_2274_, 0);
v_type_2295_ = lean_ctor_get(v_toRing_2274_, 1);
v_u_2296_ = lean_ctor_get(v_toRing_2274_, 2);
v_ringInst_2297_ = lean_ctor_get(v_toRing_2274_, 3);
v_semiringInst_2298_ = lean_ctor_get(v_toRing_2274_, 4);
v_charInst_x3f_2299_ = lean_ctor_get(v_toRing_2274_, 5);
v_addFn_x3f_2300_ = lean_ctor_get(v_toRing_2274_, 6);
v_mulFn_x3f_2301_ = lean_ctor_get(v_toRing_2274_, 7);
v_subFn_x3f_2302_ = lean_ctor_get(v_toRing_2274_, 8);
v_negFn_x3f_2303_ = lean_ctor_get(v_toRing_2274_, 9);
v_powFn_x3f_2304_ = lean_ctor_get(v_toRing_2274_, 10);
v_intCastFn_x3f_2305_ = lean_ctor_get(v_toRing_2274_, 11);
v_natCastFn_x3f_2306_ = lean_ctor_get(v_toRing_2274_, 12);
v_one_x3f_2307_ = lean_ctor_get(v_toRing_2274_, 13);
v_vars_2308_ = lean_ctor_get(v_toRing_2274_, 14);
v_varMap_2309_ = lean_ctor_get(v_toRing_2274_, 15);
v_denote_2310_ = lean_ctor_get(v_toRing_2274_, 16);
v_isSharedCheck_2322_ = !lean_is_exclusive(v_toRing_2274_);
if (v_isSharedCheck_2322_ == 0)
{
v___x_2312_ = v_toRing_2274_;
v_isShared_2313_ = v_isSharedCheck_2322_;
goto v_resetjp_2311_;
}
else
{
lean_inc(v_denote_2310_);
lean_inc(v_varMap_2309_);
lean_inc(v_vars_2308_);
lean_inc(v_one_x3f_2307_);
lean_inc(v_natCastFn_x3f_2306_);
lean_inc(v_intCastFn_x3f_2305_);
lean_inc(v_powFn_x3f_2304_);
lean_inc(v_negFn_x3f_2303_);
lean_inc(v_subFn_x3f_2302_);
lean_inc(v_mulFn_x3f_2301_);
lean_inc(v_addFn_x3f_2300_);
lean_inc(v_charInst_x3f_2299_);
lean_inc(v_semiringInst_2298_);
lean_inc(v_ringInst_2297_);
lean_inc(v_u_2296_);
lean_inc(v_type_2295_);
lean_inc(v_id_2294_);
lean_dec(v_toRing_2274_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2322_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2317_; 
lean_inc_ref(v_e_2271_);
v___x_2314_ = l_Lean_PersistentArray_push___redArg(v_vars_2308_, v_e_2271_);
v___x_2315_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0___redArg(v_varMap_2309_, v_e_2271_, v_size_2272_);
if (v_isShared_2313_ == 0)
{
lean_ctor_set(v___x_2312_, 15, v___x_2315_);
lean_ctor_set(v___x_2312_, 14, v___x_2314_);
v___x_2317_ = v___x_2312_;
goto v_reusejp_2316_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v_id_2294_);
lean_ctor_set(v_reuseFailAlloc_2321_, 1, v_type_2295_);
lean_ctor_set(v_reuseFailAlloc_2321_, 2, v_u_2296_);
lean_ctor_set(v_reuseFailAlloc_2321_, 3, v_ringInst_2297_);
lean_ctor_set(v_reuseFailAlloc_2321_, 4, v_semiringInst_2298_);
lean_ctor_set(v_reuseFailAlloc_2321_, 5, v_charInst_x3f_2299_);
lean_ctor_set(v_reuseFailAlloc_2321_, 6, v_addFn_x3f_2300_);
lean_ctor_set(v_reuseFailAlloc_2321_, 7, v_mulFn_x3f_2301_);
lean_ctor_set(v_reuseFailAlloc_2321_, 8, v_subFn_x3f_2302_);
lean_ctor_set(v_reuseFailAlloc_2321_, 9, v_negFn_x3f_2303_);
lean_ctor_set(v_reuseFailAlloc_2321_, 10, v_powFn_x3f_2304_);
lean_ctor_set(v_reuseFailAlloc_2321_, 11, v_intCastFn_x3f_2305_);
lean_ctor_set(v_reuseFailAlloc_2321_, 12, v_natCastFn_x3f_2306_);
lean_ctor_set(v_reuseFailAlloc_2321_, 13, v_one_x3f_2307_);
lean_ctor_set(v_reuseFailAlloc_2321_, 14, v___x_2314_);
lean_ctor_set(v_reuseFailAlloc_2321_, 15, v___x_2315_);
lean_ctor_set(v_reuseFailAlloc_2321_, 16, v_denote_2310_);
v___x_2317_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2316_;
}
v_reusejp_2316_:
{
lean_object* v___x_2319_; 
if (v_isShared_2293_ == 0)
{
lean_ctor_set(v___x_2292_, 0, v___x_2317_);
v___x_2319_ = v___x_2292_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(0, 15, 2);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v___x_2317_);
lean_ctor_set(v_reuseFailAlloc_2320_, 1, v_invFn_x3f_2275_);
lean_ctor_set(v_reuseFailAlloc_2320_, 2, v_semiringId_x3f_2276_);
lean_ctor_set(v_reuseFailAlloc_2320_, 3, v_commSemiringInst_2277_);
lean_ctor_set(v_reuseFailAlloc_2320_, 4, v_commRingInst_2278_);
lean_ctor_set(v_reuseFailAlloc_2320_, 5, v_noZeroDivInst_x3f_2279_);
lean_ctor_set(v_reuseFailAlloc_2320_, 6, v_fieldInst_x3f_2280_);
lean_ctor_set(v_reuseFailAlloc_2320_, 7, v_denoteEntries_2281_);
lean_ctor_set(v_reuseFailAlloc_2320_, 8, v_nextId_2282_);
lean_ctor_set(v_reuseFailAlloc_2320_, 9, v_steps_2283_);
lean_ctor_set(v_reuseFailAlloc_2320_, 10, v_queue_2284_);
lean_ctor_set(v_reuseFailAlloc_2320_, 11, v_basis_2285_);
lean_ctor_set(v_reuseFailAlloc_2320_, 12, v_diseqs_2286_);
lean_ctor_set(v_reuseFailAlloc_2320_, 13, v_invSet_2288_);
lean_ctor_set(v_reuseFailAlloc_2320_, 14, v_numEq0_x3f_2289_);
lean_ctor_set_uint8(v_reuseFailAlloc_2320_, sizeof(void*)*15, v_recheck_2287_);
lean_ctor_set_uint8(v_reuseFailAlloc_2320_, sizeof(void*)*15 + 1, v_numEq0Updated_2290_);
v___x_2319_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
return v___x_2319_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkVar_spec__0(lean_object* v_e_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_){
_start:
{
lean_object* v___x_2337_; 
v___x_2337_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_);
if (lean_obj_tag(v___x_2337_) == 0)
{
lean_object* v_a_2338_; lean_object* v___x_2340_; uint8_t v_isShared_2341_; uint8_t v_isSharedCheck_2388_; 
v_a_2338_ = lean_ctor_get(v___x_2337_, 0);
v_isSharedCheck_2388_ = !lean_is_exclusive(v___x_2337_);
if (v_isSharedCheck_2388_ == 0)
{
v___x_2340_ = v___x_2337_;
v_isShared_2341_ = v_isSharedCheck_2388_;
goto v_resetjp_2339_;
}
else
{
lean_inc(v_a_2338_);
lean_dec(v___x_2337_);
v___x_2340_ = lean_box(0);
v_isShared_2341_ = v_isSharedCheck_2388_;
goto v_resetjp_2339_;
}
v_resetjp_2339_:
{
lean_object* v_toRing_2342_; lean_object* v_vars_2343_; lean_object* v_varMap_2344_; lean_object* v___x_2345_; 
v_toRing_2342_ = lean_ctor_get(v_a_2338_, 0);
lean_inc_ref(v_toRing_2342_);
lean_dec(v_a_2338_);
v_vars_2343_ = lean_ctor_get(v_toRing_2342_, 14);
lean_inc_ref(v_vars_2343_);
v_varMap_2344_ = lean_ctor_get(v_toRing_2342_, 15);
lean_inc_ref(v_varMap_2344_);
lean_dec_ref(v_toRing_2342_);
v___x_2345_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(v_varMap_2344_, v_e_2324_);
if (lean_obj_tag(v___x_2345_) == 1)
{
lean_object* v_val_2346_; lean_object* v___x_2348_; 
lean_dec_ref(v_vars_2343_);
lean_dec_ref(v_e_2324_);
v_val_2346_ = lean_ctor_get(v___x_2345_, 0);
lean_inc(v_val_2346_);
lean_dec_ref(v___x_2345_);
if (v_isShared_2341_ == 0)
{
lean_ctor_set(v___x_2340_, 0, v_val_2346_);
v___x_2348_ = v___x_2340_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v_val_2346_);
v___x_2348_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
return v___x_2348_;
}
}
else
{
lean_object* v_size_2350_; lean_object* v___f_2351_; lean_object* v___x_2352_; 
lean_dec(v___x_2345_);
lean_del_object(v___x_2340_);
v_size_2350_ = lean_ctor_get(v_vars_2343_, 2);
lean_inc(v_size_2350_);
lean_dec_ref(v_vars_2343_);
lean_inc(v_size_2350_);
lean_inc_ref(v_e_2324_);
v___f_2351_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkVar_spec__0___lam__0), 3, 2);
lean_closure_set(v___f_2351_, 0, v_e_2324_);
lean_closure_set(v___f_2351_, 1, v_size_2350_);
lean_inc_ref(v___y_2325_);
v___x_2352_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_2351_, v___y_2325_, v___y_2326_);
if (lean_obj_tag(v___x_2352_) == 0)
{
lean_object* v___x_2353_; 
lean_dec_ref(v___x_2352_);
lean_inc_ref(v___y_2325_);
lean_inc_ref(v_e_2324_);
v___x_2353_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId(v_e_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_);
if (lean_obj_tag(v___x_2353_) == 0)
{
lean_object* v___x_2354_; lean_object* v___x_2355_; 
lean_dec_ref(v___x_2353_);
v___x_2354_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_2355_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_2354_, v_e_2324_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_);
if (lean_obj_tag(v___x_2355_) == 0)
{
lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2362_; 
v_isSharedCheck_2362_ = !lean_is_exclusive(v___x_2355_);
if (v_isSharedCheck_2362_ == 0)
{
lean_object* v_unused_2363_; 
v_unused_2363_ = lean_ctor_get(v___x_2355_, 0);
lean_dec(v_unused_2363_);
v___x_2357_ = v___x_2355_;
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
else
{
lean_dec(v___x_2355_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
v_resetjp_2356_:
{
lean_object* v___x_2360_; 
if (v_isShared_2358_ == 0)
{
lean_ctor_set(v___x_2357_, 0, v_size_2350_);
v___x_2360_ = v___x_2357_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v_size_2350_);
v___x_2360_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
return v___x_2360_;
}
}
}
else
{
lean_object* v_a_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2371_; 
lean_dec(v_size_2350_);
v_a_2364_ = lean_ctor_get(v___x_2355_, 0);
v_isSharedCheck_2371_ = !lean_is_exclusive(v___x_2355_);
if (v_isSharedCheck_2371_ == 0)
{
v___x_2366_ = v___x_2355_;
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_a_2364_);
lean_dec(v___x_2355_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v___x_2369_; 
if (v_isShared_2367_ == 0)
{
v___x_2369_ = v___x_2366_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v_a_2364_);
v___x_2369_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
return v___x_2369_;
}
}
}
}
else
{
lean_object* v_a_2372_; lean_object* v___x_2374_; uint8_t v_isShared_2375_; uint8_t v_isSharedCheck_2379_; 
lean_dec(v_size_2350_);
lean_dec_ref(v_e_2324_);
v_a_2372_ = lean_ctor_get(v___x_2353_, 0);
v_isSharedCheck_2379_ = !lean_is_exclusive(v___x_2353_);
if (v_isSharedCheck_2379_ == 0)
{
v___x_2374_ = v___x_2353_;
v_isShared_2375_ = v_isSharedCheck_2379_;
goto v_resetjp_2373_;
}
else
{
lean_inc(v_a_2372_);
lean_dec(v___x_2353_);
v___x_2374_ = lean_box(0);
v_isShared_2375_ = v_isSharedCheck_2379_;
goto v_resetjp_2373_;
}
v_resetjp_2373_:
{
lean_object* v___x_2377_; 
if (v_isShared_2375_ == 0)
{
v___x_2377_ = v___x_2374_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2378_; 
v_reuseFailAlloc_2378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2378_, 0, v_a_2372_);
v___x_2377_ = v_reuseFailAlloc_2378_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
return v___x_2377_;
}
}
}
}
else
{
lean_object* v_a_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2387_; 
lean_dec(v_size_2350_);
lean_dec_ref(v_e_2324_);
v_a_2380_ = lean_ctor_get(v___x_2352_, 0);
v_isSharedCheck_2387_ = !lean_is_exclusive(v___x_2352_);
if (v_isSharedCheck_2387_ == 0)
{
v___x_2382_ = v___x_2352_;
v_isShared_2383_ = v_isSharedCheck_2387_;
goto v_resetjp_2381_;
}
else
{
lean_inc(v_a_2380_);
lean_dec(v___x_2352_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2387_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
lean_object* v___x_2385_; 
if (v_isShared_2383_ == 0)
{
v___x_2385_ = v___x_2382_;
goto v_reusejp_2384_;
}
else
{
lean_object* v_reuseFailAlloc_2386_; 
v_reuseFailAlloc_2386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2386_, 0, v_a_2380_);
v___x_2385_ = v_reuseFailAlloc_2386_;
goto v_reusejp_2384_;
}
v_reusejp_2384_:
{
return v___x_2385_;
}
}
}
}
}
}
else
{
lean_object* v_a_2389_; lean_object* v___x_2391_; uint8_t v_isShared_2392_; uint8_t v_isSharedCheck_2396_; 
lean_dec_ref(v_e_2324_);
v_a_2389_ = lean_ctor_get(v___x_2337_, 0);
v_isSharedCheck_2396_ = !lean_is_exclusive(v___x_2337_);
if (v_isSharedCheck_2396_ == 0)
{
v___x_2391_ = v___x_2337_;
v_isShared_2392_ = v_isSharedCheck_2396_;
goto v_resetjp_2390_;
}
else
{
lean_inc(v_a_2389_);
lean_dec(v___x_2337_);
v___x_2391_ = lean_box(0);
v_isShared_2392_ = v_isSharedCheck_2396_;
goto v_resetjp_2390_;
}
v_resetjp_2390_:
{
lean_object* v___x_2394_; 
if (v_isShared_2392_ == 0)
{
v___x_2394_ = v___x_2391_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v_a_2389_);
v___x_2394_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2393_;
}
v_reusejp_2393_:
{
return v___x_2394_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkVar_spec__0___boxed(lean_object* v_e_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_){
_start:
{
lean_object* v_res_2410_; 
v_res_2410_ = l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkVar_spec__0(v_e_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_);
lean_dec(v___y_2408_);
lean_dec_ref(v___y_2407_);
lean_dec(v___y_2406_);
lean_dec_ref(v___y_2405_);
lean_dec(v___y_2404_);
lean_dec_ref(v___y_2403_);
lean_dec(v___y_2402_);
lean_dec_ref(v___y_2401_);
lean_dec(v___y_2400_);
lean_dec(v___y_2399_);
lean_dec_ref(v___y_2398_);
return v_res_2410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVar(lean_object* v_e_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_){
_start:
{
lean_object* v___x_2424_; 
v___x_2424_ = l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkVar_spec__0(v_e_2411_, v_a_2412_, v_a_2413_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_, v_a_2418_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_);
return v___x_2424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVar___boxed(lean_object* v_e_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_){
_start:
{
lean_object* v_res_2438_; 
v_res_2438_ = l_Lean_Meta_Grind_Arith_CommRing_mkVar(v_e_2425_, v_a_2426_, v_a_2427_, v_a_2428_, v_a_2429_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_);
lean_dec(v_a_2436_);
lean_dec_ref(v_a_2435_);
lean_dec(v_a_2434_);
lean_dec_ref(v_a_2433_);
lean_dec(v_a_2432_);
lean_dec_ref(v_a_2431_);
lean_dec(v_a_2430_);
lean_dec_ref(v_a_2429_);
lean_dec(v_a_2428_);
lean_dec(v_a_2427_);
lean_dec_ref(v_a_2426_);
return v_res_2438_;
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
