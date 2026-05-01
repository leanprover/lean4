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
lean_object* l_Lean_Meta_Sym_canon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_CommRing_ringExt;
lean_object* l_Lean_Meta_Grind_SolverExtension_markTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Sym_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_hashPtrExpr_unsafe__1___boxed(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_compare(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_synthInstanceMeta_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "expression in two different rings"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___lam__0___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
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
v___x_236_ = l_Lean_Meta_Sym_canon(v_e_223_, v___y_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_);
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
v___x_266_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v_e_253_, v___y_261_, v___y_262_, v___y_263_, v___y_264_);
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
lean_dec_ref(v_a_471_);
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
lean_object* v_es_634_; lean_object* v___x_635_; size_t v___x_636_; size_t v___x_637_; size_t v___x_638_; lean_object* v_j_639_; lean_object* v___x_640_; 
v_es_634_ = lean_ctor_get(v_x_631_, 0);
v___x_635_ = lean_box(2);
v___x_636_ = ((size_t)5ULL);
v___x_637_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__1);
v___x_638_ = lean_usize_land(v_x_632_, v___x_637_);
v_j_639_ = lean_usize_to_nat(v___x_638_);
v___x_640_ = lean_array_get_borrowed(v___x_635_, v_es_634_, v_j_639_);
lean_dec(v_j_639_);
switch(lean_obj_tag(v___x_640_))
{
case 0:
{
lean_object* v_key_641_; lean_object* v_val_642_; uint8_t v___x_643_; 
v_key_641_ = lean_ctor_get(v___x_640_, 0);
v_val_642_ = lean_ctor_get(v___x_640_, 1);
v___x_643_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_633_, v_key_641_);
if (v___x_643_ == 0)
{
lean_object* v___x_644_; 
v___x_644_ = lean_box(0);
return v___x_644_;
}
else
{
lean_object* v___x_645_; 
lean_inc(v_val_642_);
v___x_645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_645_, 0, v_val_642_);
return v___x_645_;
}
}
case 1:
{
lean_object* v_node_646_; size_t v___x_647_; 
v_node_646_ = lean_ctor_get(v___x_640_, 0);
v___x_647_ = lean_usize_shift_right(v_x_632_, v___x_636_);
v_x_631_ = v_node_646_;
v_x_632_ = v___x_647_;
goto _start;
}
default: 
{
lean_object* v___x_649_; 
v___x_649_ = lean_box(0);
return v___x_649_;
}
}
}
else
{
lean_object* v_ks_650_; lean_object* v_vs_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
v_ks_650_ = lean_ctor_get(v_x_631_, 0);
v_vs_651_ = lean_ctor_get(v_x_631_, 1);
v___x_652_ = lean_unsigned_to_nat(0u);
v___x_653_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_650_, v_vs_651_, v___x_652_, v_x_633_);
return v___x_653_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_654_, lean_object* v_x_655_, lean_object* v_x_656_){
_start:
{
size_t v_x_867__boxed_657_; lean_object* v_res_658_; 
v_x_867__boxed_657_ = lean_unbox_usize(v_x_655_);
lean_dec(v_x_655_);
v_res_658_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg(v_x_654_, v_x_867__boxed_657_, v_x_656_);
lean_dec_ref(v_x_656_);
lean_dec_ref(v_x_654_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(lean_object* v_x_659_, lean_object* v_x_660_){
_start:
{
uint64_t v___x_661_; size_t v___x_662_; lean_object* v___x_663_; 
v___x_661_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_660_);
v___x_662_ = lean_uint64_to_usize(v___x_661_);
v___x_663_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg(v_x_659_, v___x_662_, v_x_660_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg___boxed(lean_object* v_x_664_, lean_object* v_x_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(v_x_664_, v_x_665_);
lean_dec_ref(v_x_665_);
lean_dec_ref(v_x_664_);
return v_res_666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg(lean_object* v_e_667_, lean_object* v_a_668_, lean_object* v_a_669_){
_start:
{
lean_object* v___x_671_; 
v___x_671_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_668_, v_a_669_);
if (lean_obj_tag(v___x_671_) == 0)
{
lean_object* v_a_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_681_; 
v_a_672_ = lean_ctor_get(v___x_671_, 0);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_671_);
if (v_isSharedCheck_681_ == 0)
{
v___x_674_ = v___x_671_;
v_isShared_675_ = v_isSharedCheck_681_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_a_672_);
lean_dec(v___x_671_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_681_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v_exprToRingId_676_; lean_object* v___x_677_; lean_object* v___x_679_; 
v_exprToRingId_676_ = lean_ctor_get(v_a_672_, 2);
lean_inc_ref(v_exprToRingId_676_);
lean_dec(v_a_672_);
v___x_677_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(v_exprToRingId_676_, v_e_667_);
lean_dec_ref(v_exprToRingId_676_);
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 0, v___x_677_);
v___x_679_ = v___x_674_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v___x_677_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
}
else
{
lean_object* v_a_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_689_; 
v_a_682_ = lean_ctor_get(v___x_671_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_671_);
if (v_isSharedCheck_689_ == 0)
{
v___x_684_ = v___x_671_;
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_a_682_);
lean_dec(v___x_671_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_687_; 
if (v_isShared_685_ == 0)
{
v___x_687_ = v___x_684_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_a_682_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg___boxed(lean_object* v_e_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_){
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg(v_e_690_, v_a_691_, v_a_692_);
lean_dec_ref(v_a_692_);
lean_dec(v_a_691_);
lean_dec_ref(v_e_690_);
return v_res_694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f(lean_object* v_e_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_){
_start:
{
lean_object* v___x_707_; 
v___x_707_ = l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg(v_e_695_, v_a_696_, v_a_704_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___boxed(lean_object* v_e_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f(v_e_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
lean_dec(v_a_718_);
lean_dec_ref(v_a_717_);
lean_dec(v_a_716_);
lean_dec_ref(v_a_715_);
lean_dec(v_a_714_);
lean_dec_ref(v_a_713_);
lean_dec(v_a_712_);
lean_dec_ref(v_a_711_);
lean_dec(v_a_710_);
lean_dec(v_a_709_);
lean_dec_ref(v_e_708_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0(lean_object* v_00_u03b2_721_, lean_object* v_x_722_, lean_object* v_x_723_){
_start:
{
lean_object* v___x_724_; 
v___x_724_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(v_x_722_, v_x_723_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___boxed(lean_object* v_00_u03b2_725_, lean_object* v_x_726_, lean_object* v_x_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0(v_00_u03b2_725_, v_x_726_, v_x_727_);
lean_dec_ref(v_x_727_);
lean_dec_ref(v_x_726_);
return v_res_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_729_, lean_object* v_x_730_, size_t v_x_731_, lean_object* v_x_732_){
_start:
{
lean_object* v___x_733_; 
v___x_733_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg(v_x_730_, v_x_731_, v_x_732_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_734_, lean_object* v_x_735_, lean_object* v_x_736_, lean_object* v_x_737_){
_start:
{
size_t v_x_984__boxed_738_; lean_object* v_res_739_; 
v_x_984__boxed_738_ = lean_unbox_usize(v_x_736_);
lean_dec(v_x_736_);
v_res_739_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0(v_00_u03b2_734_, v_x_735_, v_x_984__boxed_738_, v_x_737_);
lean_dec_ref(v_x_737_);
lean_dec_ref(v_x_735_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_740_, lean_object* v_keys_741_, lean_object* v_vals_742_, lean_object* v_heq_743_, lean_object* v_i_744_, lean_object* v_k_745_){
_start:
{
lean_object* v___x_746_; 
v___x_746_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_741_, v_vals_742_, v_i_744_, v_k_745_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_747_, lean_object* v_keys_748_, lean_object* v_vals_749_, lean_object* v_heq_750_, lean_object* v_i_751_, lean_object* v_k_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_747_, v_keys_748_, v_vals_749_, v_heq_750_, v_i_751_, v_k_752_);
lean_dec_ref(v_k_752_);
lean_dec_ref(v_vals_749_);
lean_dec_ref(v_keys_748_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg___lam__0(lean_object* v_toPure_754_, lean_object* v_____do__lift_755_){
_start:
{
lean_object* v_charInst_x3f_759_; 
v_charInst_x3f_759_ = lean_ctor_get(v_____do__lift_755_, 5);
lean_inc(v_charInst_x3f_759_);
lean_dec_ref(v_____do__lift_755_);
if (lean_obj_tag(v_charInst_x3f_759_) == 1)
{
lean_object* v_val_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_771_; 
v_val_760_ = lean_ctor_get(v_charInst_x3f_759_, 0);
v_isSharedCheck_771_ = !lean_is_exclusive(v_charInst_x3f_759_);
if (v_isSharedCheck_771_ == 0)
{
v___x_762_ = v_charInst_x3f_759_;
v_isShared_763_ = v_isSharedCheck_771_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_val_760_);
lean_dec(v_charInst_x3f_759_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_771_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v_snd_764_; lean_object* v___x_765_; uint8_t v___x_766_; 
v_snd_764_ = lean_ctor_get(v_val_760_, 1);
lean_inc(v_snd_764_);
lean_dec(v_val_760_);
v___x_765_ = lean_unsigned_to_nat(0u);
v___x_766_ = lean_nat_dec_eq(v_snd_764_, v___x_765_);
if (v___x_766_ == 0)
{
lean_object* v___x_768_; 
if (v_isShared_763_ == 0)
{
lean_ctor_set(v___x_762_, 0, v_snd_764_);
v___x_768_ = v___x_762_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v_snd_764_);
v___x_768_ = v_reuseFailAlloc_770_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
lean_object* v___x_769_; 
v___x_769_ = lean_apply_2(v_toPure_754_, lean_box(0), v___x_768_);
return v___x_769_;
}
}
else
{
lean_dec(v_snd_764_);
lean_del_object(v___x_762_);
goto v___jp_756_;
}
}
}
else
{
lean_dec(v_charInst_x3f_759_);
goto v___jp_756_;
}
v___jp_756_:
{
lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_757_ = lean_box(0);
v___x_758_ = lean_apply_2(v_toPure_754_, lean_box(0), v___x_757_);
return v___x_758_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg(lean_object* v_inst_772_, lean_object* v_inst_773_){
_start:
{
lean_object* v_toApplicative_774_; lean_object* v_toBind_775_; lean_object* v_getRing_776_; lean_object* v_toPure_777_; lean_object* v___f_778_; lean_object* v___x_779_; 
v_toApplicative_774_ = lean_ctor_get(v_inst_772_, 0);
lean_inc_ref(v_toApplicative_774_);
v_toBind_775_ = lean_ctor_get(v_inst_772_, 1);
lean_inc(v_toBind_775_);
lean_dec_ref(v_inst_772_);
v_getRing_776_ = lean_ctor_get(v_inst_773_, 0);
lean_inc(v_getRing_776_);
lean_dec_ref(v_inst_773_);
v_toPure_777_ = lean_ctor_get(v_toApplicative_774_, 1);
lean_inc(v_toPure_777_);
lean_dec_ref(v_toApplicative_774_);
v___f_778_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_778_, 0, v_toPure_777_);
v___x_779_ = lean_apply_4(v_toBind_775_, lean_box(0), lean_box(0), v_getRing_776_, v___f_778_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f(lean_object* v_m_780_, lean_object* v_inst_781_, lean_object* v_inst_782_){
_start:
{
lean_object* v___x_783_; 
v___x_783_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg(v_inst_781_, v_inst_782_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f___redArg___lam__0(lean_object* v_toPure_784_, lean_object* v_____do__lift_785_){
_start:
{
lean_object* v_charInst_x3f_789_; 
v_charInst_x3f_789_ = lean_ctor_get(v_____do__lift_785_, 5);
lean_inc(v_charInst_x3f_789_);
lean_dec_ref(v_____do__lift_785_);
if (lean_obj_tag(v_charInst_x3f_789_) == 1)
{
lean_object* v_val_790_; lean_object* v_snd_791_; lean_object* v___x_792_; uint8_t v___x_793_; 
v_val_790_ = lean_ctor_get(v_charInst_x3f_789_, 0);
v_snd_791_ = lean_ctor_get(v_val_790_, 1);
v___x_792_ = lean_unsigned_to_nat(0u);
v___x_793_ = lean_nat_dec_eq(v_snd_791_, v___x_792_);
if (v___x_793_ == 0)
{
lean_object* v___x_794_; 
v___x_794_ = lean_apply_2(v_toPure_784_, lean_box(0), v_charInst_x3f_789_);
return v___x_794_;
}
else
{
lean_dec_ref(v_charInst_x3f_789_);
goto v___jp_786_;
}
}
else
{
lean_dec(v_charInst_x3f_789_);
goto v___jp_786_;
}
v___jp_786_:
{
lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_787_ = lean_box(0);
v___x_788_ = lean_apply_2(v_toPure_784_, lean_box(0), v___x_787_);
return v___x_788_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f___redArg(lean_object* v_inst_795_, lean_object* v_inst_796_){
_start:
{
lean_object* v_toApplicative_797_; lean_object* v_toBind_798_; lean_object* v_getRing_799_; lean_object* v_toPure_800_; lean_object* v___f_801_; lean_object* v___x_802_; 
v_toApplicative_797_ = lean_ctor_get(v_inst_795_, 0);
lean_inc_ref(v_toApplicative_797_);
v_toBind_798_ = lean_ctor_get(v_inst_795_, 1);
lean_inc(v_toBind_798_);
lean_dec_ref(v_inst_795_);
v_getRing_799_ = lean_ctor_get(v_inst_796_, 0);
lean_inc(v_getRing_799_);
lean_dec_ref(v_inst_796_);
v_toPure_800_ = lean_ctor_get(v_toApplicative_797_, 1);
lean_inc(v_toPure_800_);
lean_dec_ref(v_toApplicative_797_);
v___f_801_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_801_, 0, v_toPure_800_);
v___x_802_ = lean_apply_4(v_toBind_798_, lean_box(0), lean_box(0), v_getRing_799_, v___f_801_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f(lean_object* v_m_803_, lean_object* v_inst_804_, lean_object* v_inst_805_){
_start:
{
lean_object* v___x_806_; 
v___x_806_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f___redArg(v_inst_804_, v_inst_805_);
return v___x_806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisorsInst_x3f(lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_){
_start:
{
lean_object* v___x_819_; 
v___x_819_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_807_, v_a_808_, v_a_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_);
if (lean_obj_tag(v___x_819_) == 0)
{
lean_object* v_a_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_828_; 
v_a_820_ = lean_ctor_get(v___x_819_, 0);
v_isSharedCheck_828_ = !lean_is_exclusive(v___x_819_);
if (v_isSharedCheck_828_ == 0)
{
v___x_822_ = v___x_819_;
v_isShared_823_ = v_isSharedCheck_828_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_a_820_);
lean_dec(v___x_819_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_828_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v_noZeroDivInst_x3f_824_; lean_object* v___x_826_; 
v_noZeroDivInst_x3f_824_ = lean_ctor_get(v_a_820_, 5);
lean_inc(v_noZeroDivInst_x3f_824_);
lean_dec(v_a_820_);
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 0, v_noZeroDivInst_x3f_824_);
v___x_826_ = v___x_822_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v_noZeroDivInst_x3f_824_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
}
else
{
lean_object* v_a_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_836_; 
v_a_829_ = lean_ctor_get(v___x_819_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_819_);
if (v_isSharedCheck_836_ == 0)
{
v___x_831_ = v___x_819_;
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_a_829_);
lean_dec(v___x_819_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisorsInst_x3f___boxed(lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisorsInst_x3f(v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_);
lean_dec(v_a_847_);
lean_dec_ref(v_a_846_);
lean_dec(v_a_845_);
lean_dec_ref(v_a_844_);
lean_dec(v_a_843_);
lean_dec_ref(v_a_842_);
lean_dec(v_a_841_);
lean_dec_ref(v_a_840_);
lean_dec(v_a_839_);
lean_dec(v_a_838_);
lean_dec_ref(v_a_837_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisors(lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_){
_start:
{
lean_object* v___x_862_; 
v___x_862_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_, v_a_858_, v_a_859_, v_a_860_);
if (lean_obj_tag(v___x_862_) == 0)
{
lean_object* v_a_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_878_; 
v_a_863_ = lean_ctor_get(v___x_862_, 0);
v_isSharedCheck_878_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_878_ == 0)
{
v___x_865_ = v___x_862_;
v_isShared_866_ = v_isSharedCheck_878_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_a_863_);
lean_dec(v___x_862_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_878_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v_noZeroDivInst_x3f_867_; 
v_noZeroDivInst_x3f_867_ = lean_ctor_get(v_a_863_, 5);
lean_inc(v_noZeroDivInst_x3f_867_);
lean_dec(v_a_863_);
if (lean_obj_tag(v_noZeroDivInst_x3f_867_) == 0)
{
uint8_t v___x_868_; lean_object* v___x_869_; lean_object* v___x_871_; 
v___x_868_ = 0;
v___x_869_ = lean_box(v___x_868_);
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 0, v___x_869_);
v___x_871_ = v___x_865_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v___x_869_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
else
{
uint8_t v___x_873_; lean_object* v___x_874_; lean_object* v___x_876_; 
lean_dec_ref(v_noZeroDivInst_x3f_867_);
v___x_873_ = 1;
v___x_874_ = lean_box(v___x_873_);
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 0, v___x_874_);
v___x_876_ = v___x_865_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v___x_874_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
}
}
else
{
lean_object* v_a_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_886_; 
v_a_879_ = lean_ctor_get(v___x_862_, 0);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_886_ == 0)
{
v___x_881_ = v___x_862_;
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_a_879_);
lean_dec(v___x_862_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_884_; 
if (v_isShared_882_ == 0)
{
v___x_884_ = v___x_881_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_a_879_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisors___boxed(lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisors(v_a_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_);
lean_dec(v_a_897_);
lean_dec_ref(v_a_896_);
lean_dec(v_a_895_);
lean_dec_ref(v_a_894_);
lean_dec(v_a_893_);
lean_dec_ref(v_a_892_);
lean_dec(v_a_891_);
lean_dec_ref(v_a_890_);
lean_dec(v_a_889_);
lean_dec(v_a_888_);
lean_dec_ref(v_a_887_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_hasChar(lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_){
_start:
{
lean_object* v___x_912_; 
v___x_912_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_);
if (lean_obj_tag(v___x_912_) == 0)
{
lean_object* v_a_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_929_; 
v_a_913_ = lean_ctor_get(v___x_912_, 0);
v_isSharedCheck_929_ = !lean_is_exclusive(v___x_912_);
if (v_isSharedCheck_929_ == 0)
{
v___x_915_ = v___x_912_;
v_isShared_916_ = v_isSharedCheck_929_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_a_913_);
lean_dec(v___x_912_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_929_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v_toRing_917_; lean_object* v_charInst_x3f_918_; 
v_toRing_917_ = lean_ctor_get(v_a_913_, 0);
lean_inc_ref(v_toRing_917_);
lean_dec(v_a_913_);
v_charInst_x3f_918_ = lean_ctor_get(v_toRing_917_, 5);
lean_inc(v_charInst_x3f_918_);
lean_dec_ref(v_toRing_917_);
if (lean_obj_tag(v_charInst_x3f_918_) == 0)
{
uint8_t v___x_919_; lean_object* v___x_920_; lean_object* v___x_922_; 
v___x_919_ = 0;
v___x_920_ = lean_box(v___x_919_);
if (v_isShared_916_ == 0)
{
lean_ctor_set(v___x_915_, 0, v___x_920_);
v___x_922_ = v___x_915_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v___x_920_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
else
{
uint8_t v___x_924_; lean_object* v___x_925_; lean_object* v___x_927_; 
lean_dec_ref(v_charInst_x3f_918_);
v___x_924_ = 1;
v___x_925_ = lean_box(v___x_924_);
if (v_isShared_916_ == 0)
{
lean_ctor_set(v___x_915_, 0, v___x_925_);
v___x_927_ = v___x_915_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v___x_925_);
v___x_927_ = v_reuseFailAlloc_928_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
return v___x_927_;
}
}
}
}
else
{
lean_object* v_a_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_937_; 
v_a_930_ = lean_ctor_get(v___x_912_, 0);
v_isSharedCheck_937_ = !lean_is_exclusive(v___x_912_);
if (v_isSharedCheck_937_ == 0)
{
v___x_932_ = v___x_912_;
v_isShared_933_ = v_isSharedCheck_937_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_a_930_);
lean_dec(v___x_912_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_937_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v___x_935_; 
if (v_isShared_933_ == 0)
{
v___x_935_ = v___x_932_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v_a_930_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_hasChar___boxed(lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_){
_start:
{
lean_object* v_res_950_; 
v_res_950_ = l_Lean_Meta_Grind_Arith_CommRing_hasChar(v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_, v_a_948_);
lean_dec(v_a_948_);
lean_dec_ref(v_a_947_);
lean_dec(v_a_946_);
lean_dec_ref(v_a_945_);
lean_dec(v_a_944_);
lean_dec_ref(v_a_943_);
lean_dec(v_a_942_);
lean_dec_ref(v_a_941_);
lean_dec(v_a_940_);
lean_dec(v_a_939_);
lean_dec_ref(v_a_938_);
return v_res_950_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__1(void){
_start:
{
lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_952_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__0));
v___x_953_ = l_Lean_stringToMessageData(v___x_952_);
return v___x_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCharInst(lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_){
_start:
{
lean_object* v___x_966_; 
v___x_966_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_954_, v_a_955_, v_a_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_);
if (lean_obj_tag(v___x_966_) == 0)
{
lean_object* v_a_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_979_; 
v_a_967_ = lean_ctor_get(v___x_966_, 0);
v_isSharedCheck_979_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_979_ == 0)
{
v___x_969_ = v___x_966_;
v_isShared_970_ = v_isSharedCheck_979_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_a_967_);
lean_dec(v___x_966_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_979_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v_toRing_971_; lean_object* v_charInst_x3f_972_; 
v_toRing_971_ = lean_ctor_get(v_a_967_, 0);
lean_inc_ref(v_toRing_971_);
lean_dec(v_a_967_);
v_charInst_x3f_972_ = lean_ctor_get(v_toRing_971_, 5);
lean_inc(v_charInst_x3f_972_);
lean_dec_ref(v_toRing_971_);
if (lean_obj_tag(v_charInst_x3f_972_) == 1)
{
lean_object* v_val_973_; lean_object* v___x_975_; 
v_val_973_ = lean_ctor_get(v_charInst_x3f_972_, 0);
lean_inc(v_val_973_);
lean_dec_ref(v_charInst_x3f_972_);
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 0, v_val_973_);
v___x_975_ = v___x_969_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v_val_973_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
else
{
lean_object* v___x_977_; lean_object* v___x_978_; 
lean_dec(v_charInst_x3f_972_);
lean_del_object(v___x_969_);
v___x_977_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__1);
v___x_978_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg(v___x_977_, v_a_961_, v_a_962_, v_a_963_, v_a_964_);
return v___x_978_;
}
}
}
else
{
lean_object* v_a_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_987_; 
v_a_980_ = lean_ctor_get(v___x_966_, 0);
v_isSharedCheck_987_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_987_ == 0)
{
v___x_982_ = v___x_966_;
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_a_980_);
lean_dec(v___x_966_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_985_; 
if (v_isShared_983_ == 0)
{
v___x_985_ = v___x_982_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_a_980_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCharInst___boxed(lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l_Lean_Meta_Grind_Arith_CommRing_getCharInst(v_a_988_, v_a_989_, v_a_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_, v_a_995_, v_a_996_, v_a_997_, v_a_998_);
lean_dec(v_a_998_);
lean_dec_ref(v_a_997_);
lean_dec(v_a_996_);
lean_dec_ref(v_a_995_);
lean_dec(v_a_994_);
lean_dec_ref(v_a_993_);
lean_dec(v_a_992_);
lean_dec_ref(v_a_991_);
lean_dec(v_a_990_);
lean_dec(v_a_989_);
lean_dec_ref(v_a_988_);
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isField(lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_){
_start:
{
lean_object* v___x_1013_; 
v___x_1013_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1001_, v_a_1002_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_);
if (lean_obj_tag(v___x_1013_) == 0)
{
lean_object* v_a_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1029_; 
v_a_1014_ = lean_ctor_get(v___x_1013_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_1013_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1016_ = v___x_1013_;
v_isShared_1017_ = v_isSharedCheck_1029_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_dec(v___x_1013_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1029_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v_fieldInst_x3f_1018_; 
v_fieldInst_x3f_1018_ = lean_ctor_get(v_a_1014_, 6);
lean_inc(v_fieldInst_x3f_1018_);
lean_dec(v_a_1014_);
if (lean_obj_tag(v_fieldInst_x3f_1018_) == 0)
{
uint8_t v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1022_; 
v___x_1019_ = 0;
v___x_1020_ = lean_box(v___x_1019_);
if (v_isShared_1017_ == 0)
{
lean_ctor_set(v___x_1016_, 0, v___x_1020_);
v___x_1022_ = v___x_1016_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v___x_1020_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
return v___x_1022_;
}
}
else
{
uint8_t v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1027_; 
lean_dec_ref(v_fieldInst_x3f_1018_);
v___x_1024_ = 1;
v___x_1025_ = lean_box(v___x_1024_);
if (v_isShared_1017_ == 0)
{
lean_ctor_set(v___x_1016_, 0, v___x_1025_);
v___x_1027_ = v___x_1016_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v___x_1025_);
v___x_1027_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
return v___x_1027_;
}
}
}
}
else
{
lean_object* v_a_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1037_; 
v_a_1030_ = lean_ctor_get(v___x_1013_, 0);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_1013_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1032_ = v___x_1013_;
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_a_1030_);
lean_dec(v___x_1013_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___x_1035_; 
if (v_isShared_1033_ == 0)
{
v___x_1035_ = v___x_1032_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v_a_1030_);
v___x_1035_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
return v___x_1035_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isField___boxed(lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l_Lean_Meta_Grind_Arith_CommRing_isField(v_a_1038_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_, v_a_1048_);
lean_dec(v_a_1048_);
lean_dec_ref(v_a_1047_);
lean_dec(v_a_1046_);
lean_dec_ref(v_a_1045_);
lean_dec(v_a_1044_);
lean_dec_ref(v_a_1043_);
lean_dec(v_a_1042_);
lean_dec_ref(v_a_1041_);
lean_dec(v_a_1040_);
lean_dec(v_a_1039_);
lean_dec_ref(v_a_1038_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty(lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_){
_start:
{
lean_object* v___x_1063_; 
v___x_1063_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_, v_a_1058_, v_a_1059_, v_a_1060_, v_a_1061_);
if (lean_obj_tag(v___x_1063_) == 0)
{
lean_object* v_a_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1079_; 
v_a_1064_ = lean_ctor_get(v___x_1063_, 0);
v_isSharedCheck_1079_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1066_ = v___x_1063_;
v_isShared_1067_ = v_isSharedCheck_1079_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_a_1064_);
lean_dec(v___x_1063_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1079_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v_queue_1068_; 
v_queue_1068_ = lean_ctor_get(v_a_1064_, 11);
lean_inc(v_queue_1068_);
lean_dec(v_a_1064_);
if (lean_obj_tag(v_queue_1068_) == 0)
{
uint8_t v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1072_; 
lean_dec_ref(v_queue_1068_);
v___x_1069_ = 0;
v___x_1070_ = lean_box(v___x_1069_);
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 0, v___x_1070_);
v___x_1072_ = v___x_1066_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v___x_1070_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
return v___x_1072_;
}
}
else
{
uint8_t v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1077_; 
v___x_1074_ = 1;
v___x_1075_ = lean_box(v___x_1074_);
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 0, v___x_1075_);
v___x_1077_ = v___x_1066_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v___x_1075_);
v___x_1077_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
return v___x_1077_;
}
}
}
}
else
{
lean_object* v_a_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1087_; 
v_a_1080_ = lean_ctor_get(v___x_1063_, 0);
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_1063_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1082_ = v___x_1063_;
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_a_1080_);
lean_dec(v___x_1063_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1085_; 
if (v_isShared_1083_ == 0)
{
v___x_1085_ = v___x_1082_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_a_1080_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty___boxed(lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_){
_start:
{
lean_object* v_res_1100_; 
v_res_1100_ = l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty(v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_);
lean_dec(v_a_1098_);
lean_dec_ref(v_a_1097_);
lean_dec(v_a_1096_);
lean_dec_ref(v_a_1095_);
lean_dec(v_a_1094_);
lean_dec_ref(v_a_1093_);
lean_dec(v_a_1092_);
lean_dec_ref(v_a_1091_);
lean_dec(v_a_1090_);
lean_dec(v_a_1089_);
lean_dec_ref(v_a_1088_);
return v_res_1100_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(lean_object* v_k_1101_, lean_object* v_t_1102_){
_start:
{
if (lean_obj_tag(v_t_1102_) == 0)
{
lean_object* v_k_1103_; lean_object* v_v_1104_; lean_object* v_l_1105_; lean_object* v_r_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1760_; 
v_k_1103_ = lean_ctor_get(v_t_1102_, 1);
v_v_1104_ = lean_ctor_get(v_t_1102_, 2);
v_l_1105_ = lean_ctor_get(v_t_1102_, 3);
v_r_1106_ = lean_ctor_get(v_t_1102_, 4);
v_isSharedCheck_1760_ = !lean_is_exclusive(v_t_1102_);
if (v_isSharedCheck_1760_ == 0)
{
lean_object* v_unused_1761_; 
v_unused_1761_ = lean_ctor_get(v_t_1102_, 0);
lean_dec(v_unused_1761_);
v___x_1108_ = v_t_1102_;
v_isShared_1109_ = v_isSharedCheck_1760_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_r_1106_);
lean_inc(v_l_1105_);
lean_inc(v_v_1104_);
lean_inc(v_k_1103_);
lean_dec(v_t_1102_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1760_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
uint8_t v___x_1110_; 
v___x_1110_ = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_compare(v_k_1101_, v_k_1103_);
switch(v___x_1110_)
{
case 0:
{
lean_object* v_impl_1111_; lean_object* v___x_1112_; 
v_impl_1111_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_k_1101_, v_l_1105_);
v___x_1112_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1111_) == 0)
{
if (lean_obj_tag(v_r_1106_) == 0)
{
lean_object* v_size_1113_; lean_object* v_size_1114_; lean_object* v_k_1115_; lean_object* v_v_1116_; lean_object* v_l_1117_; lean_object* v_r_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; uint8_t v___x_1121_; 
v_size_1113_ = lean_ctor_get(v_impl_1111_, 0);
lean_inc(v_size_1113_);
v_size_1114_ = lean_ctor_get(v_r_1106_, 0);
v_k_1115_ = lean_ctor_get(v_r_1106_, 1);
v_v_1116_ = lean_ctor_get(v_r_1106_, 2);
v_l_1117_ = lean_ctor_get(v_r_1106_, 3);
lean_inc(v_l_1117_);
v_r_1118_ = lean_ctor_get(v_r_1106_, 4);
v___x_1119_ = lean_unsigned_to_nat(3u);
v___x_1120_ = lean_nat_mul(v___x_1119_, v_size_1113_);
v___x_1121_ = lean_nat_dec_lt(v___x_1120_, v_size_1114_);
lean_dec(v___x_1120_);
if (v___x_1121_ == 0)
{
lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1125_; 
lean_dec(v_l_1117_);
v___x_1122_ = lean_nat_add(v___x_1112_, v_size_1113_);
lean_dec(v_size_1113_);
v___x_1123_ = lean_nat_add(v___x_1122_, v_size_1114_);
lean_dec(v___x_1122_);
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 3, v_impl_1111_);
lean_ctor_set(v___x_1108_, 0, v___x_1123_);
v___x_1125_ = v___x_1108_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v___x_1123_);
lean_ctor_set(v_reuseFailAlloc_1126_, 1, v_k_1103_);
lean_ctor_set(v_reuseFailAlloc_1126_, 2, v_v_1104_);
lean_ctor_set(v_reuseFailAlloc_1126_, 3, v_impl_1111_);
lean_ctor_set(v_reuseFailAlloc_1126_, 4, v_r_1106_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
else
{
lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1190_; 
lean_inc(v_r_1118_);
lean_inc(v_v_1116_);
lean_inc(v_k_1115_);
lean_inc(v_size_1114_);
v_isSharedCheck_1190_ = !lean_is_exclusive(v_r_1106_);
if (v_isSharedCheck_1190_ == 0)
{
lean_object* v_unused_1191_; lean_object* v_unused_1192_; lean_object* v_unused_1193_; lean_object* v_unused_1194_; lean_object* v_unused_1195_; 
v_unused_1191_ = lean_ctor_get(v_r_1106_, 4);
lean_dec(v_unused_1191_);
v_unused_1192_ = lean_ctor_get(v_r_1106_, 3);
lean_dec(v_unused_1192_);
v_unused_1193_ = lean_ctor_get(v_r_1106_, 2);
lean_dec(v_unused_1193_);
v_unused_1194_ = lean_ctor_get(v_r_1106_, 1);
lean_dec(v_unused_1194_);
v_unused_1195_ = lean_ctor_get(v_r_1106_, 0);
lean_dec(v_unused_1195_);
v___x_1128_ = v_r_1106_;
v_isShared_1129_ = v_isSharedCheck_1190_;
goto v_resetjp_1127_;
}
else
{
lean_dec(v_r_1106_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1190_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v_size_1130_; lean_object* v_k_1131_; lean_object* v_v_1132_; lean_object* v_l_1133_; lean_object* v_r_1134_; lean_object* v_size_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; uint8_t v___x_1138_; 
v_size_1130_ = lean_ctor_get(v_l_1117_, 0);
v_k_1131_ = lean_ctor_get(v_l_1117_, 1);
v_v_1132_ = lean_ctor_get(v_l_1117_, 2);
v_l_1133_ = lean_ctor_get(v_l_1117_, 3);
v_r_1134_ = lean_ctor_get(v_l_1117_, 4);
v_size_1135_ = lean_ctor_get(v_r_1118_, 0);
v___x_1136_ = lean_unsigned_to_nat(2u);
v___x_1137_ = lean_nat_mul(v___x_1136_, v_size_1135_);
v___x_1138_ = lean_nat_dec_lt(v_size_1130_, v___x_1137_);
lean_dec(v___x_1137_);
if (v___x_1138_ == 0)
{
lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1166_; 
lean_inc(v_r_1134_);
lean_inc(v_l_1133_);
lean_inc(v_v_1132_);
lean_inc(v_k_1131_);
v_isSharedCheck_1166_ = !lean_is_exclusive(v_l_1117_);
if (v_isSharedCheck_1166_ == 0)
{
lean_object* v_unused_1167_; lean_object* v_unused_1168_; lean_object* v_unused_1169_; lean_object* v_unused_1170_; lean_object* v_unused_1171_; 
v_unused_1167_ = lean_ctor_get(v_l_1117_, 4);
lean_dec(v_unused_1167_);
v_unused_1168_ = lean_ctor_get(v_l_1117_, 3);
lean_dec(v_unused_1168_);
v_unused_1169_ = lean_ctor_get(v_l_1117_, 2);
lean_dec(v_unused_1169_);
v_unused_1170_ = lean_ctor_get(v_l_1117_, 1);
lean_dec(v_unused_1170_);
v_unused_1171_ = lean_ctor_get(v_l_1117_, 0);
lean_dec(v_unused_1171_);
v___x_1140_ = v_l_1117_;
v_isShared_1141_ = v_isSharedCheck_1166_;
goto v_resetjp_1139_;
}
else
{
lean_dec(v_l_1117_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1166_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___y_1145_; lean_object* v___y_1146_; lean_object* v___y_1147_; lean_object* v___y_1156_; 
v___x_1142_ = lean_nat_add(v___x_1112_, v_size_1113_);
lean_dec(v_size_1113_);
v___x_1143_ = lean_nat_add(v___x_1142_, v_size_1114_);
lean_dec(v_size_1114_);
if (lean_obj_tag(v_l_1133_) == 0)
{
lean_object* v_size_1164_; 
v_size_1164_ = lean_ctor_get(v_l_1133_, 0);
lean_inc(v_size_1164_);
v___y_1156_ = v_size_1164_;
goto v___jp_1155_;
}
else
{
lean_object* v___x_1165_; 
v___x_1165_ = lean_unsigned_to_nat(0u);
v___y_1156_ = v___x_1165_;
goto v___jp_1155_;
}
v___jp_1144_:
{
lean_object* v___x_1148_; lean_object* v___x_1150_; 
v___x_1148_ = lean_nat_add(v___y_1145_, v___y_1147_);
lean_dec(v___y_1147_);
lean_dec(v___y_1145_);
if (v_isShared_1141_ == 0)
{
lean_ctor_set(v___x_1140_, 4, v_r_1118_);
lean_ctor_set(v___x_1140_, 3, v_r_1134_);
lean_ctor_set(v___x_1140_, 2, v_v_1116_);
lean_ctor_set(v___x_1140_, 1, v_k_1115_);
lean_ctor_set(v___x_1140_, 0, v___x_1148_);
v___x_1150_ = v___x_1140_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v___x_1148_);
lean_ctor_set(v_reuseFailAlloc_1154_, 1, v_k_1115_);
lean_ctor_set(v_reuseFailAlloc_1154_, 2, v_v_1116_);
lean_ctor_set(v_reuseFailAlloc_1154_, 3, v_r_1134_);
lean_ctor_set(v_reuseFailAlloc_1154_, 4, v_r_1118_);
v___x_1150_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
lean_object* v___x_1152_; 
if (v_isShared_1129_ == 0)
{
lean_ctor_set(v___x_1128_, 4, v___x_1150_);
lean_ctor_set(v___x_1128_, 3, v___y_1146_);
lean_ctor_set(v___x_1128_, 2, v_v_1132_);
lean_ctor_set(v___x_1128_, 1, v_k_1131_);
lean_ctor_set(v___x_1128_, 0, v___x_1143_);
v___x_1152_ = v___x_1128_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v___x_1143_);
lean_ctor_set(v_reuseFailAlloc_1153_, 1, v_k_1131_);
lean_ctor_set(v_reuseFailAlloc_1153_, 2, v_v_1132_);
lean_ctor_set(v_reuseFailAlloc_1153_, 3, v___y_1146_);
lean_ctor_set(v_reuseFailAlloc_1153_, 4, v___x_1150_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
}
v___jp_1155_:
{
lean_object* v___x_1157_; lean_object* v___x_1159_; 
v___x_1157_ = lean_nat_add(v___x_1142_, v___y_1156_);
lean_dec(v___y_1156_);
lean_dec(v___x_1142_);
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 4, v_l_1133_);
lean_ctor_set(v___x_1108_, 3, v_impl_1111_);
lean_ctor_set(v___x_1108_, 0, v___x_1157_);
v___x_1159_ = v___x_1108_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v___x_1157_);
lean_ctor_set(v_reuseFailAlloc_1163_, 1, v_k_1103_);
lean_ctor_set(v_reuseFailAlloc_1163_, 2, v_v_1104_);
lean_ctor_set(v_reuseFailAlloc_1163_, 3, v_impl_1111_);
lean_ctor_set(v_reuseFailAlloc_1163_, 4, v_l_1133_);
v___x_1159_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
lean_object* v___x_1160_; 
v___x_1160_ = lean_nat_add(v___x_1112_, v_size_1135_);
if (lean_obj_tag(v_r_1134_) == 0)
{
lean_object* v_size_1161_; 
v_size_1161_ = lean_ctor_get(v_r_1134_, 0);
lean_inc(v_size_1161_);
v___y_1145_ = v___x_1160_;
v___y_1146_ = v___x_1159_;
v___y_1147_ = v_size_1161_;
goto v___jp_1144_;
}
else
{
lean_object* v___x_1162_; 
v___x_1162_ = lean_unsigned_to_nat(0u);
v___y_1145_ = v___x_1160_;
v___y_1146_ = v___x_1159_;
v___y_1147_ = v___x_1162_;
goto v___jp_1144_;
}
}
}
}
}
else
{
lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1176_; 
lean_del_object(v___x_1108_);
v___x_1172_ = lean_nat_add(v___x_1112_, v_size_1113_);
lean_dec(v_size_1113_);
v___x_1173_ = lean_nat_add(v___x_1172_, v_size_1114_);
lean_dec(v_size_1114_);
v___x_1174_ = lean_nat_add(v___x_1172_, v_size_1130_);
lean_dec(v___x_1172_);
lean_inc_ref(v_impl_1111_);
if (v_isShared_1129_ == 0)
{
lean_ctor_set(v___x_1128_, 4, v_l_1117_);
lean_ctor_set(v___x_1128_, 3, v_impl_1111_);
lean_ctor_set(v___x_1128_, 2, v_v_1104_);
lean_ctor_set(v___x_1128_, 1, v_k_1103_);
lean_ctor_set(v___x_1128_, 0, v___x_1174_);
v___x_1176_ = v___x_1128_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v___x_1174_);
lean_ctor_set(v_reuseFailAlloc_1189_, 1, v_k_1103_);
lean_ctor_set(v_reuseFailAlloc_1189_, 2, v_v_1104_);
lean_ctor_set(v_reuseFailAlloc_1189_, 3, v_impl_1111_);
lean_ctor_set(v_reuseFailAlloc_1189_, 4, v_l_1117_);
v___x_1176_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1183_; 
v_isSharedCheck_1183_ = !lean_is_exclusive(v_impl_1111_);
if (v_isSharedCheck_1183_ == 0)
{
lean_object* v_unused_1184_; lean_object* v_unused_1185_; lean_object* v_unused_1186_; lean_object* v_unused_1187_; lean_object* v_unused_1188_; 
v_unused_1184_ = lean_ctor_get(v_impl_1111_, 4);
lean_dec(v_unused_1184_);
v_unused_1185_ = lean_ctor_get(v_impl_1111_, 3);
lean_dec(v_unused_1185_);
v_unused_1186_ = lean_ctor_get(v_impl_1111_, 2);
lean_dec(v_unused_1186_);
v_unused_1187_ = lean_ctor_get(v_impl_1111_, 1);
lean_dec(v_unused_1187_);
v_unused_1188_ = lean_ctor_get(v_impl_1111_, 0);
lean_dec(v_unused_1188_);
v___x_1178_ = v_impl_1111_;
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
else
{
lean_dec(v_impl_1111_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1181_; 
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 4, v_r_1118_);
lean_ctor_set(v___x_1178_, 3, v___x_1176_);
lean_ctor_set(v___x_1178_, 2, v_v_1116_);
lean_ctor_set(v___x_1178_, 1, v_k_1115_);
lean_ctor_set(v___x_1178_, 0, v___x_1173_);
v___x_1181_ = v___x_1178_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v___x_1173_);
lean_ctor_set(v_reuseFailAlloc_1182_, 1, v_k_1115_);
lean_ctor_set(v_reuseFailAlloc_1182_, 2, v_v_1116_);
lean_ctor_set(v_reuseFailAlloc_1182_, 3, v___x_1176_);
lean_ctor_set(v_reuseFailAlloc_1182_, 4, v_r_1118_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
return v___x_1181_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1196_; lean_object* v___x_1197_; lean_object* v___x_1199_; 
v_size_1196_ = lean_ctor_get(v_impl_1111_, 0);
lean_inc(v_size_1196_);
v___x_1197_ = lean_nat_add(v___x_1112_, v_size_1196_);
lean_dec(v_size_1196_);
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 3, v_impl_1111_);
lean_ctor_set(v___x_1108_, 0, v___x_1197_);
v___x_1199_ = v___x_1108_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v___x_1197_);
lean_ctor_set(v_reuseFailAlloc_1200_, 1, v_k_1103_);
lean_ctor_set(v_reuseFailAlloc_1200_, 2, v_v_1104_);
lean_ctor_set(v_reuseFailAlloc_1200_, 3, v_impl_1111_);
lean_ctor_set(v_reuseFailAlloc_1200_, 4, v_r_1106_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
}
else
{
if (lean_obj_tag(v_r_1106_) == 0)
{
lean_object* v_l_1201_; 
v_l_1201_ = lean_ctor_get(v_r_1106_, 3);
lean_inc(v_l_1201_);
if (lean_obj_tag(v_l_1201_) == 0)
{
lean_object* v_r_1202_; 
v_r_1202_ = lean_ctor_get(v_r_1106_, 4);
lean_inc(v_r_1202_);
if (lean_obj_tag(v_r_1202_) == 0)
{
lean_object* v_size_1203_; lean_object* v_k_1204_; lean_object* v_v_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1218_; 
v_size_1203_ = lean_ctor_get(v_r_1106_, 0);
v_k_1204_ = lean_ctor_get(v_r_1106_, 1);
v_v_1205_ = lean_ctor_get(v_r_1106_, 2);
v_isSharedCheck_1218_ = !lean_is_exclusive(v_r_1106_);
if (v_isSharedCheck_1218_ == 0)
{
lean_object* v_unused_1219_; lean_object* v_unused_1220_; 
v_unused_1219_ = lean_ctor_get(v_r_1106_, 4);
lean_dec(v_unused_1219_);
v_unused_1220_ = lean_ctor_get(v_r_1106_, 3);
lean_dec(v_unused_1220_);
v___x_1207_ = v_r_1106_;
v_isShared_1208_ = v_isSharedCheck_1218_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_v_1205_);
lean_inc(v_k_1204_);
lean_inc(v_size_1203_);
lean_dec(v_r_1106_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1218_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v_size_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1213_; 
v_size_1209_ = lean_ctor_get(v_l_1201_, 0);
v___x_1210_ = lean_nat_add(v___x_1112_, v_size_1203_);
lean_dec(v_size_1203_);
v___x_1211_ = lean_nat_add(v___x_1112_, v_size_1209_);
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 4, v_l_1201_);
lean_ctor_set(v___x_1207_, 3, v_impl_1111_);
lean_ctor_set(v___x_1207_, 2, v_v_1104_);
lean_ctor_set(v___x_1207_, 1, v_k_1103_);
lean_ctor_set(v___x_1207_, 0, v___x_1211_);
v___x_1213_ = v___x_1207_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v___x_1211_);
lean_ctor_set(v_reuseFailAlloc_1217_, 1, v_k_1103_);
lean_ctor_set(v_reuseFailAlloc_1217_, 2, v_v_1104_);
lean_ctor_set(v_reuseFailAlloc_1217_, 3, v_impl_1111_);
lean_ctor_set(v_reuseFailAlloc_1217_, 4, v_l_1201_);
v___x_1213_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
lean_object* v___x_1215_; 
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 4, v_r_1202_);
lean_ctor_set(v___x_1108_, 3, v___x_1213_);
lean_ctor_set(v___x_1108_, 2, v_v_1205_);
lean_ctor_set(v___x_1108_, 1, v_k_1204_);
lean_ctor_set(v___x_1108_, 0, v___x_1210_);
v___x_1215_ = v___x_1108_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v___x_1210_);
lean_ctor_set(v_reuseFailAlloc_1216_, 1, v_k_1204_);
lean_ctor_set(v_reuseFailAlloc_1216_, 2, v_v_1205_);
lean_ctor_set(v_reuseFailAlloc_1216_, 3, v___x_1213_);
lean_ctor_set(v_reuseFailAlloc_1216_, 4, v_r_1202_);
v___x_1215_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
return v___x_1215_;
}
}
}
}
else
{
lean_object* v_k_1221_; lean_object* v_v_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1245_; 
v_k_1221_ = lean_ctor_get(v_r_1106_, 1);
v_v_1222_ = lean_ctor_get(v_r_1106_, 2);
v_isSharedCheck_1245_ = !lean_is_exclusive(v_r_1106_);
if (v_isSharedCheck_1245_ == 0)
{
lean_object* v_unused_1246_; lean_object* v_unused_1247_; lean_object* v_unused_1248_; 
v_unused_1246_ = lean_ctor_get(v_r_1106_, 4);
lean_dec(v_unused_1246_);
v_unused_1247_ = lean_ctor_get(v_r_1106_, 3);
lean_dec(v_unused_1247_);
v_unused_1248_ = lean_ctor_get(v_r_1106_, 0);
lean_dec(v_unused_1248_);
v___x_1224_ = v_r_1106_;
v_isShared_1225_ = v_isSharedCheck_1245_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_v_1222_);
lean_inc(v_k_1221_);
lean_dec(v_r_1106_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1245_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v_k_1226_; lean_object* v_v_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1241_; 
v_k_1226_ = lean_ctor_get(v_l_1201_, 1);
v_v_1227_ = lean_ctor_get(v_l_1201_, 2);
v_isSharedCheck_1241_ = !lean_is_exclusive(v_l_1201_);
if (v_isSharedCheck_1241_ == 0)
{
lean_object* v_unused_1242_; lean_object* v_unused_1243_; lean_object* v_unused_1244_; 
v_unused_1242_ = lean_ctor_get(v_l_1201_, 4);
lean_dec(v_unused_1242_);
v_unused_1243_ = lean_ctor_get(v_l_1201_, 3);
lean_dec(v_unused_1243_);
v_unused_1244_ = lean_ctor_get(v_l_1201_, 0);
lean_dec(v_unused_1244_);
v___x_1229_ = v_l_1201_;
v_isShared_1230_ = v_isSharedCheck_1241_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_v_1227_);
lean_inc(v_k_1226_);
lean_dec(v_l_1201_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1241_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___x_1231_; lean_object* v___x_1233_; 
v___x_1231_ = lean_unsigned_to_nat(3u);
if (v_isShared_1230_ == 0)
{
lean_ctor_set(v___x_1229_, 4, v_r_1202_);
lean_ctor_set(v___x_1229_, 3, v_r_1202_);
lean_ctor_set(v___x_1229_, 2, v_v_1104_);
lean_ctor_set(v___x_1229_, 1, v_k_1103_);
lean_ctor_set(v___x_1229_, 0, v___x_1112_);
v___x_1233_ = v___x_1229_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v___x_1112_);
lean_ctor_set(v_reuseFailAlloc_1240_, 1, v_k_1103_);
lean_ctor_set(v_reuseFailAlloc_1240_, 2, v_v_1104_);
lean_ctor_set(v_reuseFailAlloc_1240_, 3, v_r_1202_);
lean_ctor_set(v_reuseFailAlloc_1240_, 4, v_r_1202_);
v___x_1233_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
lean_object* v___x_1235_; 
if (v_isShared_1225_ == 0)
{
lean_ctor_set(v___x_1224_, 3, v_r_1202_);
lean_ctor_set(v___x_1224_, 0, v___x_1112_);
v___x_1235_ = v___x_1224_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v___x_1112_);
lean_ctor_set(v_reuseFailAlloc_1239_, 1, v_k_1221_);
lean_ctor_set(v_reuseFailAlloc_1239_, 2, v_v_1222_);
lean_ctor_set(v_reuseFailAlloc_1239_, 3, v_r_1202_);
lean_ctor_set(v_reuseFailAlloc_1239_, 4, v_r_1202_);
v___x_1235_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
lean_object* v___x_1237_; 
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 4, v___x_1235_);
lean_ctor_set(v___x_1108_, 3, v___x_1233_);
lean_ctor_set(v___x_1108_, 2, v_v_1227_);
lean_ctor_set(v___x_1108_, 1, v_k_1226_);
lean_ctor_set(v___x_1108_, 0, v___x_1231_);
v___x_1237_ = v___x_1108_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v___x_1231_);
lean_ctor_set(v_reuseFailAlloc_1238_, 1, v_k_1226_);
lean_ctor_set(v_reuseFailAlloc_1238_, 2, v_v_1227_);
lean_ctor_set(v_reuseFailAlloc_1238_, 3, v___x_1233_);
lean_ctor_set(v_reuseFailAlloc_1238_, 4, v___x_1235_);
v___x_1237_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
return v___x_1237_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_1249_; 
v_r_1249_ = lean_ctor_get(v_r_1106_, 4);
lean_inc(v_r_1249_);
if (lean_obj_tag(v_r_1249_) == 0)
{
lean_object* v_k_1250_; lean_object* v_v_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1262_; 
v_k_1250_ = lean_ctor_get(v_r_1106_, 1);
v_v_1251_ = lean_ctor_get(v_r_1106_, 2);
v_isSharedCheck_1262_ = !lean_is_exclusive(v_r_1106_);
if (v_isSharedCheck_1262_ == 0)
{
lean_object* v_unused_1263_; lean_object* v_unused_1264_; lean_object* v_unused_1265_; 
v_unused_1263_ = lean_ctor_get(v_r_1106_, 4);
lean_dec(v_unused_1263_);
v_unused_1264_ = lean_ctor_get(v_r_1106_, 3);
lean_dec(v_unused_1264_);
v_unused_1265_ = lean_ctor_get(v_r_1106_, 0);
lean_dec(v_unused_1265_);
v___x_1253_ = v_r_1106_;
v_isShared_1254_ = v_isSharedCheck_1262_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_v_1251_);
lean_inc(v_k_1250_);
lean_dec(v_r_1106_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1262_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v___x_1255_; lean_object* v___x_1257_; 
v___x_1255_ = lean_unsigned_to_nat(3u);
if (v_isShared_1254_ == 0)
{
lean_ctor_set(v___x_1253_, 4, v_l_1201_);
lean_ctor_set(v___x_1253_, 2, v_v_1104_);
lean_ctor_set(v___x_1253_, 1, v_k_1103_);
lean_ctor_set(v___x_1253_, 0, v___x_1112_);
v___x_1257_ = v___x_1253_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v___x_1112_);
lean_ctor_set(v_reuseFailAlloc_1261_, 1, v_k_1103_);
lean_ctor_set(v_reuseFailAlloc_1261_, 2, v_v_1104_);
lean_ctor_set(v_reuseFailAlloc_1261_, 3, v_l_1201_);
lean_ctor_set(v_reuseFailAlloc_1261_, 4, v_l_1201_);
v___x_1257_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
lean_object* v___x_1259_; 
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 4, v_r_1249_);
lean_ctor_set(v___x_1108_, 3, v___x_1257_);
lean_ctor_set(v___x_1108_, 2, v_v_1251_);
lean_ctor_set(v___x_1108_, 1, v_k_1250_);
lean_ctor_set(v___x_1108_, 0, v___x_1255_);
v___x_1259_ = v___x_1108_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v___x_1255_);
lean_ctor_set(v_reuseFailAlloc_1260_, 1, v_k_1250_);
lean_ctor_set(v_reuseFailAlloc_1260_, 2, v_v_1251_);
lean_ctor_set(v_reuseFailAlloc_1260_, 3, v___x_1257_);
lean_ctor_set(v_reuseFailAlloc_1260_, 4, v_r_1249_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
return v___x_1259_;
}
}
}
}
else
{
lean_object* v_size_1266_; lean_object* v_k_1267_; lean_object* v_v_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1279_; 
v_size_1266_ = lean_ctor_get(v_r_1106_, 0);
v_k_1267_ = lean_ctor_get(v_r_1106_, 1);
v_v_1268_ = lean_ctor_get(v_r_1106_, 2);
v_isSharedCheck_1279_ = !lean_is_exclusive(v_r_1106_);
if (v_isSharedCheck_1279_ == 0)
{
lean_object* v_unused_1280_; lean_object* v_unused_1281_; 
v_unused_1280_ = lean_ctor_get(v_r_1106_, 4);
lean_dec(v_unused_1280_);
v_unused_1281_ = lean_ctor_get(v_r_1106_, 3);
lean_dec(v_unused_1281_);
v___x_1270_ = v_r_1106_;
v_isShared_1271_ = v_isSharedCheck_1279_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_v_1268_);
lean_inc(v_k_1267_);
lean_inc(v_size_1266_);
lean_dec(v_r_1106_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1279_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v___x_1273_; 
if (v_isShared_1271_ == 0)
{
lean_ctor_set(v___x_1270_, 3, v_r_1249_);
v___x_1273_ = v___x_1270_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_size_1266_);
lean_ctor_set(v_reuseFailAlloc_1278_, 1, v_k_1267_);
lean_ctor_set(v_reuseFailAlloc_1278_, 2, v_v_1268_);
lean_ctor_set(v_reuseFailAlloc_1278_, 3, v_r_1249_);
lean_ctor_set(v_reuseFailAlloc_1278_, 4, v_r_1249_);
v___x_1273_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
lean_object* v___x_1274_; lean_object* v___x_1276_; 
v___x_1274_ = lean_unsigned_to_nat(2u);
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 4, v___x_1273_);
lean_ctor_set(v___x_1108_, 3, v_r_1249_);
lean_ctor_set(v___x_1108_, 0, v___x_1274_);
v___x_1276_ = v___x_1108_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v___x_1274_);
lean_ctor_set(v_reuseFailAlloc_1277_, 1, v_k_1103_);
lean_ctor_set(v_reuseFailAlloc_1277_, 2, v_v_1104_);
lean_ctor_set(v_reuseFailAlloc_1277_, 3, v_r_1249_);
lean_ctor_set(v_reuseFailAlloc_1277_, 4, v___x_1273_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
return v___x_1276_;
}
}
}
}
}
}
else
{
lean_object* v___x_1283_; 
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 3, v_r_1106_);
lean_ctor_set(v___x_1108_, 0, v___x_1112_);
v___x_1283_ = v___x_1108_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v___x_1112_);
lean_ctor_set(v_reuseFailAlloc_1284_, 1, v_k_1103_);
lean_ctor_set(v_reuseFailAlloc_1284_, 2, v_v_1104_);
lean_ctor_set(v_reuseFailAlloc_1284_, 3, v_r_1106_);
lean_ctor_set(v_reuseFailAlloc_1284_, 4, v_r_1106_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
return v___x_1283_;
}
}
}
}
case 1:
{
lean_del_object(v___x_1108_);
lean_dec(v_v_1104_);
lean_dec(v_k_1103_);
if (lean_obj_tag(v_l_1105_) == 0)
{
if (lean_obj_tag(v_r_1106_) == 0)
{
lean_object* v_size_1285_; lean_object* v_k_1286_; lean_object* v_v_1287_; lean_object* v_l_1288_; lean_object* v_r_1289_; lean_object* v_size_1290_; lean_object* v_k_1291_; lean_object* v_v_1292_; lean_object* v_l_1293_; lean_object* v_r_1294_; lean_object* v___x_1295_; uint8_t v___x_1296_; 
v_size_1285_ = lean_ctor_get(v_l_1105_, 0);
v_k_1286_ = lean_ctor_get(v_l_1105_, 1);
v_v_1287_ = lean_ctor_get(v_l_1105_, 2);
v_l_1288_ = lean_ctor_get(v_l_1105_, 3);
v_r_1289_ = lean_ctor_get(v_l_1105_, 4);
lean_inc(v_r_1289_);
v_size_1290_ = lean_ctor_get(v_r_1106_, 0);
v_k_1291_ = lean_ctor_get(v_r_1106_, 1);
v_v_1292_ = lean_ctor_get(v_r_1106_, 2);
v_l_1293_ = lean_ctor_get(v_r_1106_, 3);
lean_inc(v_l_1293_);
v_r_1294_ = lean_ctor_get(v_r_1106_, 4);
v___x_1295_ = lean_unsigned_to_nat(1u);
v___x_1296_ = lean_nat_dec_lt(v_size_1285_, v_size_1290_);
if (v___x_1296_ == 0)
{
lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1432_; 
lean_inc(v_l_1288_);
lean_inc(v_v_1287_);
lean_inc(v_k_1286_);
v_isSharedCheck_1432_ = !lean_is_exclusive(v_l_1105_);
if (v_isSharedCheck_1432_ == 0)
{
lean_object* v_unused_1433_; lean_object* v_unused_1434_; lean_object* v_unused_1435_; lean_object* v_unused_1436_; lean_object* v_unused_1437_; 
v_unused_1433_ = lean_ctor_get(v_l_1105_, 4);
lean_dec(v_unused_1433_);
v_unused_1434_ = lean_ctor_get(v_l_1105_, 3);
lean_dec(v_unused_1434_);
v_unused_1435_ = lean_ctor_get(v_l_1105_, 2);
lean_dec(v_unused_1435_);
v_unused_1436_ = lean_ctor_get(v_l_1105_, 1);
lean_dec(v_unused_1436_);
v_unused_1437_ = lean_ctor_get(v_l_1105_, 0);
lean_dec(v_unused_1437_);
v___x_1298_ = v_l_1105_;
v_isShared_1299_ = v_isSharedCheck_1432_;
goto v_resetjp_1297_;
}
else
{
lean_dec(v_l_1105_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1432_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1300_; lean_object* v_tree_1301_; 
v___x_1300_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_1286_, v_v_1287_, v_l_1288_, v_r_1289_);
v_tree_1301_ = lean_ctor_get(v___x_1300_, 2);
lean_inc(v_tree_1301_);
if (lean_obj_tag(v_tree_1301_) == 0)
{
lean_object* v_k_1302_; lean_object* v_v_1303_; lean_object* v_size_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; uint8_t v___x_1307_; 
v_k_1302_ = lean_ctor_get(v___x_1300_, 0);
lean_inc(v_k_1302_);
v_v_1303_ = lean_ctor_get(v___x_1300_, 1);
lean_inc(v_v_1303_);
lean_dec_ref(v___x_1300_);
v_size_1304_ = lean_ctor_get(v_tree_1301_, 0);
v___x_1305_ = lean_unsigned_to_nat(3u);
v___x_1306_ = lean_nat_mul(v___x_1305_, v_size_1304_);
v___x_1307_ = lean_nat_dec_lt(v___x_1306_, v_size_1290_);
lean_dec(v___x_1306_);
if (v___x_1307_ == 0)
{
lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1311_; 
lean_dec(v_l_1293_);
v___x_1308_ = lean_nat_add(v___x_1295_, v_size_1304_);
v___x_1309_ = lean_nat_add(v___x_1308_, v_size_1290_);
lean_dec(v___x_1308_);
if (v_isShared_1299_ == 0)
{
lean_ctor_set(v___x_1298_, 4, v_r_1106_);
lean_ctor_set(v___x_1298_, 3, v_tree_1301_);
lean_ctor_set(v___x_1298_, 2, v_v_1303_);
lean_ctor_set(v___x_1298_, 1, v_k_1302_);
lean_ctor_set(v___x_1298_, 0, v___x_1309_);
v___x_1311_ = v___x_1298_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v___x_1309_);
lean_ctor_set(v_reuseFailAlloc_1312_, 1, v_k_1302_);
lean_ctor_set(v_reuseFailAlloc_1312_, 2, v_v_1303_);
lean_ctor_set(v_reuseFailAlloc_1312_, 3, v_tree_1301_);
lean_ctor_set(v_reuseFailAlloc_1312_, 4, v_r_1106_);
v___x_1311_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
return v___x_1311_;
}
}
else
{
lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1367_; 
lean_inc(v_r_1294_);
lean_inc(v_v_1292_);
lean_inc(v_k_1291_);
lean_inc(v_size_1290_);
v_isSharedCheck_1367_ = !lean_is_exclusive(v_r_1106_);
if (v_isSharedCheck_1367_ == 0)
{
lean_object* v_unused_1368_; lean_object* v_unused_1369_; lean_object* v_unused_1370_; lean_object* v_unused_1371_; lean_object* v_unused_1372_; 
v_unused_1368_ = lean_ctor_get(v_r_1106_, 4);
lean_dec(v_unused_1368_);
v_unused_1369_ = lean_ctor_get(v_r_1106_, 3);
lean_dec(v_unused_1369_);
v_unused_1370_ = lean_ctor_get(v_r_1106_, 2);
lean_dec(v_unused_1370_);
v_unused_1371_ = lean_ctor_get(v_r_1106_, 1);
lean_dec(v_unused_1371_);
v_unused_1372_ = lean_ctor_get(v_r_1106_, 0);
lean_dec(v_unused_1372_);
v___x_1314_ = v_r_1106_;
v_isShared_1315_ = v_isSharedCheck_1367_;
goto v_resetjp_1313_;
}
else
{
lean_dec(v_r_1106_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1367_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v_size_1316_; lean_object* v_k_1317_; lean_object* v_v_1318_; lean_object* v_l_1319_; lean_object* v_r_1320_; lean_object* v_size_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; uint8_t v___x_1324_; 
v_size_1316_ = lean_ctor_get(v_l_1293_, 0);
v_k_1317_ = lean_ctor_get(v_l_1293_, 1);
v_v_1318_ = lean_ctor_get(v_l_1293_, 2);
v_l_1319_ = lean_ctor_get(v_l_1293_, 3);
v_r_1320_ = lean_ctor_get(v_l_1293_, 4);
v_size_1321_ = lean_ctor_get(v_r_1294_, 0);
v___x_1322_ = lean_unsigned_to_nat(2u);
v___x_1323_ = lean_nat_mul(v___x_1322_, v_size_1321_);
v___x_1324_ = lean_nat_dec_lt(v_size_1316_, v___x_1323_);
lean_dec(v___x_1323_);
if (v___x_1324_ == 0)
{
lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1352_; 
lean_inc(v_r_1320_);
lean_inc(v_l_1319_);
lean_inc(v_v_1318_);
lean_inc(v_k_1317_);
v_isSharedCheck_1352_ = !lean_is_exclusive(v_l_1293_);
if (v_isSharedCheck_1352_ == 0)
{
lean_object* v_unused_1353_; lean_object* v_unused_1354_; lean_object* v_unused_1355_; lean_object* v_unused_1356_; lean_object* v_unused_1357_; 
v_unused_1353_ = lean_ctor_get(v_l_1293_, 4);
lean_dec(v_unused_1353_);
v_unused_1354_ = lean_ctor_get(v_l_1293_, 3);
lean_dec(v_unused_1354_);
v_unused_1355_ = lean_ctor_get(v_l_1293_, 2);
lean_dec(v_unused_1355_);
v_unused_1356_ = lean_ctor_get(v_l_1293_, 1);
lean_dec(v_unused_1356_);
v_unused_1357_ = lean_ctor_get(v_l_1293_, 0);
lean_dec(v_unused_1357_);
v___x_1326_ = v_l_1293_;
v_isShared_1327_ = v_isSharedCheck_1352_;
goto v_resetjp_1325_;
}
else
{
lean_dec(v_l_1293_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1352_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___y_1331_; lean_object* v___y_1332_; lean_object* v___y_1333_; lean_object* v___y_1342_; 
v___x_1328_ = lean_nat_add(v___x_1295_, v_size_1304_);
v___x_1329_ = lean_nat_add(v___x_1328_, v_size_1290_);
lean_dec(v_size_1290_);
if (lean_obj_tag(v_l_1319_) == 0)
{
lean_object* v_size_1350_; 
v_size_1350_ = lean_ctor_get(v_l_1319_, 0);
lean_inc(v_size_1350_);
v___y_1342_ = v_size_1350_;
goto v___jp_1341_;
}
else
{
lean_object* v___x_1351_; 
v___x_1351_ = lean_unsigned_to_nat(0u);
v___y_1342_ = v___x_1351_;
goto v___jp_1341_;
}
v___jp_1330_:
{
lean_object* v___x_1334_; lean_object* v___x_1336_; 
v___x_1334_ = lean_nat_add(v___y_1332_, v___y_1333_);
lean_dec(v___y_1333_);
lean_dec(v___y_1332_);
if (v_isShared_1327_ == 0)
{
lean_ctor_set(v___x_1326_, 4, v_r_1294_);
lean_ctor_set(v___x_1326_, 3, v_r_1320_);
lean_ctor_set(v___x_1326_, 2, v_v_1292_);
lean_ctor_set(v___x_1326_, 1, v_k_1291_);
lean_ctor_set(v___x_1326_, 0, v___x_1334_);
v___x_1336_ = v___x_1326_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v___x_1334_);
lean_ctor_set(v_reuseFailAlloc_1340_, 1, v_k_1291_);
lean_ctor_set(v_reuseFailAlloc_1340_, 2, v_v_1292_);
lean_ctor_set(v_reuseFailAlloc_1340_, 3, v_r_1320_);
lean_ctor_set(v_reuseFailAlloc_1340_, 4, v_r_1294_);
v___x_1336_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
lean_object* v___x_1338_; 
if (v_isShared_1315_ == 0)
{
lean_ctor_set(v___x_1314_, 4, v___x_1336_);
lean_ctor_set(v___x_1314_, 3, v___y_1331_);
lean_ctor_set(v___x_1314_, 2, v_v_1318_);
lean_ctor_set(v___x_1314_, 1, v_k_1317_);
lean_ctor_set(v___x_1314_, 0, v___x_1329_);
v___x_1338_ = v___x_1314_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v___x_1329_);
lean_ctor_set(v_reuseFailAlloc_1339_, 1, v_k_1317_);
lean_ctor_set(v_reuseFailAlloc_1339_, 2, v_v_1318_);
lean_ctor_set(v_reuseFailAlloc_1339_, 3, v___y_1331_);
lean_ctor_set(v_reuseFailAlloc_1339_, 4, v___x_1336_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
}
v___jp_1341_:
{
lean_object* v___x_1343_; lean_object* v___x_1345_; 
v___x_1343_ = lean_nat_add(v___x_1328_, v___y_1342_);
lean_dec(v___y_1342_);
lean_dec(v___x_1328_);
if (v_isShared_1299_ == 0)
{
lean_ctor_set(v___x_1298_, 4, v_l_1319_);
lean_ctor_set(v___x_1298_, 3, v_tree_1301_);
lean_ctor_set(v___x_1298_, 2, v_v_1303_);
lean_ctor_set(v___x_1298_, 1, v_k_1302_);
lean_ctor_set(v___x_1298_, 0, v___x_1343_);
v___x_1345_ = v___x_1298_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v___x_1343_);
lean_ctor_set(v_reuseFailAlloc_1349_, 1, v_k_1302_);
lean_ctor_set(v_reuseFailAlloc_1349_, 2, v_v_1303_);
lean_ctor_set(v_reuseFailAlloc_1349_, 3, v_tree_1301_);
lean_ctor_set(v_reuseFailAlloc_1349_, 4, v_l_1319_);
v___x_1345_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
lean_object* v___x_1346_; 
v___x_1346_ = lean_nat_add(v___x_1295_, v_size_1321_);
if (lean_obj_tag(v_r_1320_) == 0)
{
lean_object* v_size_1347_; 
v_size_1347_ = lean_ctor_get(v_r_1320_, 0);
lean_inc(v_size_1347_);
v___y_1331_ = v___x_1345_;
v___y_1332_ = v___x_1346_;
v___y_1333_ = v_size_1347_;
goto v___jp_1330_;
}
else
{
lean_object* v___x_1348_; 
v___x_1348_ = lean_unsigned_to_nat(0u);
v___y_1331_ = v___x_1345_;
v___y_1332_ = v___x_1346_;
v___y_1333_ = v___x_1348_;
goto v___jp_1330_;
}
}
}
}
}
else
{
lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1362_; 
v___x_1358_ = lean_nat_add(v___x_1295_, v_size_1304_);
v___x_1359_ = lean_nat_add(v___x_1358_, v_size_1290_);
lean_dec(v_size_1290_);
v___x_1360_ = lean_nat_add(v___x_1358_, v_size_1316_);
lean_dec(v___x_1358_);
if (v_isShared_1315_ == 0)
{
lean_ctor_set(v___x_1314_, 4, v_l_1293_);
lean_ctor_set(v___x_1314_, 3, v_tree_1301_);
lean_ctor_set(v___x_1314_, 2, v_v_1303_);
lean_ctor_set(v___x_1314_, 1, v_k_1302_);
lean_ctor_set(v___x_1314_, 0, v___x_1360_);
v___x_1362_ = v___x_1314_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v___x_1360_);
lean_ctor_set(v_reuseFailAlloc_1366_, 1, v_k_1302_);
lean_ctor_set(v_reuseFailAlloc_1366_, 2, v_v_1303_);
lean_ctor_set(v_reuseFailAlloc_1366_, 3, v_tree_1301_);
lean_ctor_set(v_reuseFailAlloc_1366_, 4, v_l_1293_);
v___x_1362_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
lean_object* v___x_1364_; 
if (v_isShared_1299_ == 0)
{
lean_ctor_set(v___x_1298_, 4, v_r_1294_);
lean_ctor_set(v___x_1298_, 3, v___x_1362_);
lean_ctor_set(v___x_1298_, 2, v_v_1292_);
lean_ctor_set(v___x_1298_, 1, v_k_1291_);
lean_ctor_set(v___x_1298_, 0, v___x_1359_);
v___x_1364_ = v___x_1298_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v___x_1359_);
lean_ctor_set(v_reuseFailAlloc_1365_, 1, v_k_1291_);
lean_ctor_set(v_reuseFailAlloc_1365_, 2, v_v_1292_);
lean_ctor_set(v_reuseFailAlloc_1365_, 3, v___x_1362_);
lean_ctor_set(v_reuseFailAlloc_1365_, 4, v_r_1294_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
return v___x_1364_;
}
}
}
}
}
}
else
{
lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1426_; 
lean_inc(v_r_1294_);
lean_inc(v_v_1292_);
lean_inc(v_k_1291_);
lean_inc(v_size_1290_);
v_isSharedCheck_1426_ = !lean_is_exclusive(v_r_1106_);
if (v_isSharedCheck_1426_ == 0)
{
lean_object* v_unused_1427_; lean_object* v_unused_1428_; lean_object* v_unused_1429_; lean_object* v_unused_1430_; lean_object* v_unused_1431_; 
v_unused_1427_ = lean_ctor_get(v_r_1106_, 4);
lean_dec(v_unused_1427_);
v_unused_1428_ = lean_ctor_get(v_r_1106_, 3);
lean_dec(v_unused_1428_);
v_unused_1429_ = lean_ctor_get(v_r_1106_, 2);
lean_dec(v_unused_1429_);
v_unused_1430_ = lean_ctor_get(v_r_1106_, 1);
lean_dec(v_unused_1430_);
v_unused_1431_ = lean_ctor_get(v_r_1106_, 0);
lean_dec(v_unused_1431_);
v___x_1374_ = v_r_1106_;
v_isShared_1375_ = v_isSharedCheck_1426_;
goto v_resetjp_1373_;
}
else
{
lean_dec(v_r_1106_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1426_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
if (lean_obj_tag(v_l_1293_) == 0)
{
if (lean_obj_tag(v_r_1294_) == 0)
{
lean_object* v_k_1376_; lean_object* v_v_1377_; lean_object* v_size_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1382_; 
v_k_1376_ = lean_ctor_get(v___x_1300_, 0);
lean_inc(v_k_1376_);
v_v_1377_ = lean_ctor_get(v___x_1300_, 1);
lean_inc(v_v_1377_);
lean_dec_ref(v___x_1300_);
v_size_1378_ = lean_ctor_get(v_l_1293_, 0);
v___x_1379_ = lean_nat_add(v___x_1295_, v_size_1290_);
lean_dec(v_size_1290_);
v___x_1380_ = lean_nat_add(v___x_1295_, v_size_1378_);
if (v_isShared_1375_ == 0)
{
lean_ctor_set(v___x_1374_, 4, v_l_1293_);
lean_ctor_set(v___x_1374_, 3, v_tree_1301_);
lean_ctor_set(v___x_1374_, 2, v_v_1377_);
lean_ctor_set(v___x_1374_, 1, v_k_1376_);
lean_ctor_set(v___x_1374_, 0, v___x_1380_);
v___x_1382_ = v___x_1374_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v___x_1380_);
lean_ctor_set(v_reuseFailAlloc_1386_, 1, v_k_1376_);
lean_ctor_set(v_reuseFailAlloc_1386_, 2, v_v_1377_);
lean_ctor_set(v_reuseFailAlloc_1386_, 3, v_tree_1301_);
lean_ctor_set(v_reuseFailAlloc_1386_, 4, v_l_1293_);
v___x_1382_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
lean_object* v___x_1384_; 
if (v_isShared_1299_ == 0)
{
lean_ctor_set(v___x_1298_, 4, v_r_1294_);
lean_ctor_set(v___x_1298_, 3, v___x_1382_);
lean_ctor_set(v___x_1298_, 2, v_v_1292_);
lean_ctor_set(v___x_1298_, 1, v_k_1291_);
lean_ctor_set(v___x_1298_, 0, v___x_1379_);
v___x_1384_ = v___x_1298_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v___x_1379_);
lean_ctor_set(v_reuseFailAlloc_1385_, 1, v_k_1291_);
lean_ctor_set(v_reuseFailAlloc_1385_, 2, v_v_1292_);
lean_ctor_set(v_reuseFailAlloc_1385_, 3, v___x_1382_);
lean_ctor_set(v_reuseFailAlloc_1385_, 4, v_r_1294_);
v___x_1384_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
return v___x_1384_;
}
}
}
else
{
lean_object* v_k_1387_; lean_object* v_v_1388_; lean_object* v_k_1389_; lean_object* v_v_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1404_; 
lean_dec(v_size_1290_);
v_k_1387_ = lean_ctor_get(v___x_1300_, 0);
lean_inc(v_k_1387_);
v_v_1388_ = lean_ctor_get(v___x_1300_, 1);
lean_inc(v_v_1388_);
lean_dec_ref(v___x_1300_);
v_k_1389_ = lean_ctor_get(v_l_1293_, 1);
v_v_1390_ = lean_ctor_get(v_l_1293_, 2);
v_isSharedCheck_1404_ = !lean_is_exclusive(v_l_1293_);
if (v_isSharedCheck_1404_ == 0)
{
lean_object* v_unused_1405_; lean_object* v_unused_1406_; lean_object* v_unused_1407_; 
v_unused_1405_ = lean_ctor_get(v_l_1293_, 4);
lean_dec(v_unused_1405_);
v_unused_1406_ = lean_ctor_get(v_l_1293_, 3);
lean_dec(v_unused_1406_);
v_unused_1407_ = lean_ctor_get(v_l_1293_, 0);
lean_dec(v_unused_1407_);
v___x_1392_ = v_l_1293_;
v_isShared_1393_ = v_isSharedCheck_1404_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_v_1390_);
lean_inc(v_k_1389_);
lean_dec(v_l_1293_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1404_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v___x_1394_; lean_object* v___x_1396_; 
v___x_1394_ = lean_unsigned_to_nat(3u);
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 4, v_r_1294_);
lean_ctor_set(v___x_1392_, 3, v_r_1294_);
lean_ctor_set(v___x_1392_, 2, v_v_1388_);
lean_ctor_set(v___x_1392_, 1, v_k_1387_);
lean_ctor_set(v___x_1392_, 0, v___x_1295_);
v___x_1396_ = v___x_1392_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v___x_1295_);
lean_ctor_set(v_reuseFailAlloc_1403_, 1, v_k_1387_);
lean_ctor_set(v_reuseFailAlloc_1403_, 2, v_v_1388_);
lean_ctor_set(v_reuseFailAlloc_1403_, 3, v_r_1294_);
lean_ctor_set(v_reuseFailAlloc_1403_, 4, v_r_1294_);
v___x_1396_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
lean_object* v___x_1398_; 
if (v_isShared_1375_ == 0)
{
lean_ctor_set(v___x_1374_, 3, v_r_1294_);
lean_ctor_set(v___x_1374_, 0, v___x_1295_);
v___x_1398_ = v___x_1374_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v___x_1295_);
lean_ctor_set(v_reuseFailAlloc_1402_, 1, v_k_1291_);
lean_ctor_set(v_reuseFailAlloc_1402_, 2, v_v_1292_);
lean_ctor_set(v_reuseFailAlloc_1402_, 3, v_r_1294_);
lean_ctor_set(v_reuseFailAlloc_1402_, 4, v_r_1294_);
v___x_1398_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
lean_object* v___x_1400_; 
if (v_isShared_1299_ == 0)
{
lean_ctor_set(v___x_1298_, 4, v___x_1398_);
lean_ctor_set(v___x_1298_, 3, v___x_1396_);
lean_ctor_set(v___x_1298_, 2, v_v_1390_);
lean_ctor_set(v___x_1298_, 1, v_k_1389_);
lean_ctor_set(v___x_1298_, 0, v___x_1394_);
v___x_1400_ = v___x_1298_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v___x_1394_);
lean_ctor_set(v_reuseFailAlloc_1401_, 1, v_k_1389_);
lean_ctor_set(v_reuseFailAlloc_1401_, 2, v_v_1390_);
lean_ctor_set(v_reuseFailAlloc_1401_, 3, v___x_1396_);
lean_ctor_set(v_reuseFailAlloc_1401_, 4, v___x_1398_);
v___x_1400_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
return v___x_1400_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1294_) == 0)
{
lean_object* v_k_1408_; lean_object* v_v_1409_; lean_object* v___x_1410_; lean_object* v___x_1412_; 
lean_dec(v_size_1290_);
v_k_1408_ = lean_ctor_get(v___x_1300_, 0);
lean_inc(v_k_1408_);
v_v_1409_ = lean_ctor_get(v___x_1300_, 1);
lean_inc(v_v_1409_);
lean_dec_ref(v___x_1300_);
v___x_1410_ = lean_unsigned_to_nat(3u);
if (v_isShared_1375_ == 0)
{
lean_ctor_set(v___x_1374_, 4, v_l_1293_);
lean_ctor_set(v___x_1374_, 2, v_v_1409_);
lean_ctor_set(v___x_1374_, 1, v_k_1408_);
lean_ctor_set(v___x_1374_, 0, v___x_1295_);
v___x_1412_ = v___x_1374_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v___x_1295_);
lean_ctor_set(v_reuseFailAlloc_1416_, 1, v_k_1408_);
lean_ctor_set(v_reuseFailAlloc_1416_, 2, v_v_1409_);
lean_ctor_set(v_reuseFailAlloc_1416_, 3, v_l_1293_);
lean_ctor_set(v_reuseFailAlloc_1416_, 4, v_l_1293_);
v___x_1412_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
lean_object* v___x_1414_; 
if (v_isShared_1299_ == 0)
{
lean_ctor_set(v___x_1298_, 4, v_r_1294_);
lean_ctor_set(v___x_1298_, 3, v___x_1412_);
lean_ctor_set(v___x_1298_, 2, v_v_1292_);
lean_ctor_set(v___x_1298_, 1, v_k_1291_);
lean_ctor_set(v___x_1298_, 0, v___x_1410_);
v___x_1414_ = v___x_1298_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v___x_1410_);
lean_ctor_set(v_reuseFailAlloc_1415_, 1, v_k_1291_);
lean_ctor_set(v_reuseFailAlloc_1415_, 2, v_v_1292_);
lean_ctor_set(v_reuseFailAlloc_1415_, 3, v___x_1412_);
lean_ctor_set(v_reuseFailAlloc_1415_, 4, v_r_1294_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
return v___x_1414_;
}
}
}
else
{
lean_object* v_k_1417_; lean_object* v_v_1418_; lean_object* v___x_1420_; 
v_k_1417_ = lean_ctor_get(v___x_1300_, 0);
lean_inc(v_k_1417_);
v_v_1418_ = lean_ctor_get(v___x_1300_, 1);
lean_inc(v_v_1418_);
lean_dec_ref(v___x_1300_);
if (v_isShared_1375_ == 0)
{
lean_ctor_set(v___x_1374_, 3, v_r_1294_);
v___x_1420_ = v___x_1374_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v_size_1290_);
lean_ctor_set(v_reuseFailAlloc_1425_, 1, v_k_1291_);
lean_ctor_set(v_reuseFailAlloc_1425_, 2, v_v_1292_);
lean_ctor_set(v_reuseFailAlloc_1425_, 3, v_r_1294_);
lean_ctor_set(v_reuseFailAlloc_1425_, 4, v_r_1294_);
v___x_1420_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
lean_object* v___x_1421_; lean_object* v___x_1423_; 
v___x_1421_ = lean_unsigned_to_nat(2u);
if (v_isShared_1299_ == 0)
{
lean_ctor_set(v___x_1298_, 4, v___x_1420_);
lean_ctor_set(v___x_1298_, 3, v_r_1294_);
lean_ctor_set(v___x_1298_, 2, v_v_1418_);
lean_ctor_set(v___x_1298_, 1, v_k_1417_);
lean_ctor_set(v___x_1298_, 0, v___x_1421_);
v___x_1423_ = v___x_1298_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v___x_1421_);
lean_ctor_set(v_reuseFailAlloc_1424_, 1, v_k_1417_);
lean_ctor_set(v_reuseFailAlloc_1424_, 2, v_v_1418_);
lean_ctor_set(v_reuseFailAlloc_1424_, 3, v_r_1294_);
lean_ctor_set(v_reuseFailAlloc_1424_, 4, v___x_1420_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
return v___x_1423_;
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
lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1590_; 
lean_inc(v_r_1294_);
lean_inc(v_v_1292_);
lean_inc(v_k_1291_);
v_isSharedCheck_1590_ = !lean_is_exclusive(v_r_1106_);
if (v_isSharedCheck_1590_ == 0)
{
lean_object* v_unused_1591_; lean_object* v_unused_1592_; lean_object* v_unused_1593_; lean_object* v_unused_1594_; lean_object* v_unused_1595_; 
v_unused_1591_ = lean_ctor_get(v_r_1106_, 4);
lean_dec(v_unused_1591_);
v_unused_1592_ = lean_ctor_get(v_r_1106_, 3);
lean_dec(v_unused_1592_);
v_unused_1593_ = lean_ctor_get(v_r_1106_, 2);
lean_dec(v_unused_1593_);
v_unused_1594_ = lean_ctor_get(v_r_1106_, 1);
lean_dec(v_unused_1594_);
v_unused_1595_ = lean_ctor_get(v_r_1106_, 0);
lean_dec(v_unused_1595_);
v___x_1439_ = v_r_1106_;
v_isShared_1440_ = v_isSharedCheck_1590_;
goto v_resetjp_1438_;
}
else
{
lean_dec(v_r_1106_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1590_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v___x_1441_; lean_object* v_tree_1442_; 
v___x_1441_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_1291_, v_v_1292_, v_l_1293_, v_r_1294_);
v_tree_1442_ = lean_ctor_get(v___x_1441_, 2);
lean_inc(v_tree_1442_);
if (lean_obj_tag(v_tree_1442_) == 0)
{
lean_object* v_k_1443_; lean_object* v_v_1444_; lean_object* v_size_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; uint8_t v___x_1448_; 
v_k_1443_ = lean_ctor_get(v___x_1441_, 0);
lean_inc(v_k_1443_);
v_v_1444_ = lean_ctor_get(v___x_1441_, 1);
lean_inc(v_v_1444_);
lean_dec_ref(v___x_1441_);
v_size_1445_ = lean_ctor_get(v_tree_1442_, 0);
v___x_1446_ = lean_unsigned_to_nat(3u);
v___x_1447_ = lean_nat_mul(v___x_1446_, v_size_1445_);
v___x_1448_ = lean_nat_dec_lt(v___x_1447_, v_size_1285_);
lean_dec(v___x_1447_);
if (v___x_1448_ == 0)
{
lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1452_; 
lean_dec(v_r_1289_);
v___x_1449_ = lean_nat_add(v___x_1295_, v_size_1285_);
v___x_1450_ = lean_nat_add(v___x_1449_, v_size_1445_);
lean_dec(v___x_1449_);
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 4, v_tree_1442_);
lean_ctor_set(v___x_1439_, 3, v_l_1105_);
lean_ctor_set(v___x_1439_, 2, v_v_1444_);
lean_ctor_set(v___x_1439_, 1, v_k_1443_);
lean_ctor_set(v___x_1439_, 0, v___x_1450_);
v___x_1452_ = v___x_1439_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v___x_1450_);
lean_ctor_set(v_reuseFailAlloc_1453_, 1, v_k_1443_);
lean_ctor_set(v_reuseFailAlloc_1453_, 2, v_v_1444_);
lean_ctor_set(v_reuseFailAlloc_1453_, 3, v_l_1105_);
lean_ctor_set(v_reuseFailAlloc_1453_, 4, v_tree_1442_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
else
{
lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1519_; 
lean_inc(v_l_1288_);
lean_inc(v_v_1287_);
lean_inc(v_k_1286_);
lean_inc(v_size_1285_);
v_isSharedCheck_1519_ = !lean_is_exclusive(v_l_1105_);
if (v_isSharedCheck_1519_ == 0)
{
lean_object* v_unused_1520_; lean_object* v_unused_1521_; lean_object* v_unused_1522_; lean_object* v_unused_1523_; lean_object* v_unused_1524_; 
v_unused_1520_ = lean_ctor_get(v_l_1105_, 4);
lean_dec(v_unused_1520_);
v_unused_1521_ = lean_ctor_get(v_l_1105_, 3);
lean_dec(v_unused_1521_);
v_unused_1522_ = lean_ctor_get(v_l_1105_, 2);
lean_dec(v_unused_1522_);
v_unused_1523_ = lean_ctor_get(v_l_1105_, 1);
lean_dec(v_unused_1523_);
v_unused_1524_ = lean_ctor_get(v_l_1105_, 0);
lean_dec(v_unused_1524_);
v___x_1455_ = v_l_1105_;
v_isShared_1456_ = v_isSharedCheck_1519_;
goto v_resetjp_1454_;
}
else
{
lean_dec(v_l_1105_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1519_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
lean_object* v_size_1457_; lean_object* v_size_1458_; lean_object* v_k_1459_; lean_object* v_v_1460_; lean_object* v_l_1461_; lean_object* v_r_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; uint8_t v___x_1465_; 
v_size_1457_ = lean_ctor_get(v_l_1288_, 0);
v_size_1458_ = lean_ctor_get(v_r_1289_, 0);
v_k_1459_ = lean_ctor_get(v_r_1289_, 1);
v_v_1460_ = lean_ctor_get(v_r_1289_, 2);
v_l_1461_ = lean_ctor_get(v_r_1289_, 3);
v_r_1462_ = lean_ctor_get(v_r_1289_, 4);
v___x_1463_ = lean_unsigned_to_nat(2u);
v___x_1464_ = lean_nat_mul(v___x_1463_, v_size_1457_);
v___x_1465_ = lean_nat_dec_lt(v_size_1458_, v___x_1464_);
lean_dec(v___x_1464_);
if (v___x_1465_ == 0)
{
lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1503_; 
lean_inc(v_r_1462_);
lean_inc(v_l_1461_);
lean_inc(v_v_1460_);
lean_inc(v_k_1459_);
lean_del_object(v___x_1455_);
v_isSharedCheck_1503_ = !lean_is_exclusive(v_r_1289_);
if (v_isSharedCheck_1503_ == 0)
{
lean_object* v_unused_1504_; lean_object* v_unused_1505_; lean_object* v_unused_1506_; lean_object* v_unused_1507_; lean_object* v_unused_1508_; 
v_unused_1504_ = lean_ctor_get(v_r_1289_, 4);
lean_dec(v_unused_1504_);
v_unused_1505_ = lean_ctor_get(v_r_1289_, 3);
lean_dec(v_unused_1505_);
v_unused_1506_ = lean_ctor_get(v_r_1289_, 2);
lean_dec(v_unused_1506_);
v_unused_1507_ = lean_ctor_get(v_r_1289_, 1);
lean_dec(v_unused_1507_);
v_unused_1508_ = lean_ctor_get(v_r_1289_, 0);
lean_dec(v_unused_1508_);
v___x_1467_ = v_r_1289_;
v_isShared_1468_ = v_isSharedCheck_1503_;
goto v_resetjp_1466_;
}
else
{
lean_dec(v_r_1289_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1503_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___y_1472_; lean_object* v___y_1473_; lean_object* v___y_1474_; lean_object* v___x_1491_; lean_object* v___y_1493_; 
v___x_1469_ = lean_nat_add(v___x_1295_, v_size_1285_);
lean_dec(v_size_1285_);
v___x_1470_ = lean_nat_add(v___x_1469_, v_size_1445_);
lean_dec(v___x_1469_);
v___x_1491_ = lean_nat_add(v___x_1295_, v_size_1457_);
if (lean_obj_tag(v_l_1461_) == 0)
{
lean_object* v_size_1501_; 
v_size_1501_ = lean_ctor_get(v_l_1461_, 0);
lean_inc(v_size_1501_);
v___y_1493_ = v_size_1501_;
goto v___jp_1492_;
}
else
{
lean_object* v___x_1502_; 
v___x_1502_ = lean_unsigned_to_nat(0u);
v___y_1493_ = v___x_1502_;
goto v___jp_1492_;
}
v___jp_1471_:
{
lean_object* v___x_1475_; lean_object* v___x_1477_; 
v___x_1475_ = lean_nat_add(v___y_1472_, v___y_1474_);
lean_dec(v___y_1474_);
lean_dec(v___y_1472_);
lean_inc_ref(v_tree_1442_);
if (v_isShared_1468_ == 0)
{
lean_ctor_set(v___x_1467_, 4, v_tree_1442_);
lean_ctor_set(v___x_1467_, 3, v_r_1462_);
lean_ctor_set(v___x_1467_, 2, v_v_1444_);
lean_ctor_set(v___x_1467_, 1, v_k_1443_);
lean_ctor_set(v___x_1467_, 0, v___x_1475_);
v___x_1477_ = v___x_1467_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v___x_1475_);
lean_ctor_set(v_reuseFailAlloc_1490_, 1, v_k_1443_);
lean_ctor_set(v_reuseFailAlloc_1490_, 2, v_v_1444_);
lean_ctor_set(v_reuseFailAlloc_1490_, 3, v_r_1462_);
lean_ctor_set(v_reuseFailAlloc_1490_, 4, v_tree_1442_);
v___x_1477_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
lean_object* v___x_1479_; uint8_t v_isShared_1480_; uint8_t v_isSharedCheck_1484_; 
v_isSharedCheck_1484_ = !lean_is_exclusive(v_tree_1442_);
if (v_isSharedCheck_1484_ == 0)
{
lean_object* v_unused_1485_; lean_object* v_unused_1486_; lean_object* v_unused_1487_; lean_object* v_unused_1488_; lean_object* v_unused_1489_; 
v_unused_1485_ = lean_ctor_get(v_tree_1442_, 4);
lean_dec(v_unused_1485_);
v_unused_1486_ = lean_ctor_get(v_tree_1442_, 3);
lean_dec(v_unused_1486_);
v_unused_1487_ = lean_ctor_get(v_tree_1442_, 2);
lean_dec(v_unused_1487_);
v_unused_1488_ = lean_ctor_get(v_tree_1442_, 1);
lean_dec(v_unused_1488_);
v_unused_1489_ = lean_ctor_get(v_tree_1442_, 0);
lean_dec(v_unused_1489_);
v___x_1479_ = v_tree_1442_;
v_isShared_1480_ = v_isSharedCheck_1484_;
goto v_resetjp_1478_;
}
else
{
lean_dec(v_tree_1442_);
v___x_1479_ = lean_box(0);
v_isShared_1480_ = v_isSharedCheck_1484_;
goto v_resetjp_1478_;
}
v_resetjp_1478_:
{
lean_object* v___x_1482_; 
if (v_isShared_1480_ == 0)
{
lean_ctor_set(v___x_1479_, 4, v___x_1477_);
lean_ctor_set(v___x_1479_, 3, v___y_1473_);
lean_ctor_set(v___x_1479_, 2, v_v_1460_);
lean_ctor_set(v___x_1479_, 1, v_k_1459_);
lean_ctor_set(v___x_1479_, 0, v___x_1470_);
v___x_1482_ = v___x_1479_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v___x_1470_);
lean_ctor_set(v_reuseFailAlloc_1483_, 1, v_k_1459_);
lean_ctor_set(v_reuseFailAlloc_1483_, 2, v_v_1460_);
lean_ctor_set(v_reuseFailAlloc_1483_, 3, v___y_1473_);
lean_ctor_set(v_reuseFailAlloc_1483_, 4, v___x_1477_);
v___x_1482_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
return v___x_1482_;
}
}
}
}
v___jp_1492_:
{
lean_object* v___x_1494_; lean_object* v___x_1496_; 
v___x_1494_ = lean_nat_add(v___x_1491_, v___y_1493_);
lean_dec(v___y_1493_);
lean_dec(v___x_1491_);
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 4, v_l_1461_);
lean_ctor_set(v___x_1439_, 3, v_l_1288_);
lean_ctor_set(v___x_1439_, 2, v_v_1287_);
lean_ctor_set(v___x_1439_, 1, v_k_1286_);
lean_ctor_set(v___x_1439_, 0, v___x_1494_);
v___x_1496_ = v___x_1439_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v___x_1494_);
lean_ctor_set(v_reuseFailAlloc_1500_, 1, v_k_1286_);
lean_ctor_set(v_reuseFailAlloc_1500_, 2, v_v_1287_);
lean_ctor_set(v_reuseFailAlloc_1500_, 3, v_l_1288_);
lean_ctor_set(v_reuseFailAlloc_1500_, 4, v_l_1461_);
v___x_1496_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
lean_object* v___x_1497_; 
v___x_1497_ = lean_nat_add(v___x_1295_, v_size_1445_);
if (lean_obj_tag(v_r_1462_) == 0)
{
lean_object* v_size_1498_; 
v_size_1498_ = lean_ctor_get(v_r_1462_, 0);
lean_inc(v_size_1498_);
v___y_1472_ = v___x_1497_;
v___y_1473_ = v___x_1496_;
v___y_1474_ = v_size_1498_;
goto v___jp_1471_;
}
else
{
lean_object* v___x_1499_; 
v___x_1499_ = lean_unsigned_to_nat(0u);
v___y_1472_ = v___x_1497_;
v___y_1473_ = v___x_1496_;
v___y_1474_ = v___x_1499_;
goto v___jp_1471_;
}
}
}
}
}
else
{
lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1514_; 
v___x_1509_ = lean_nat_add(v___x_1295_, v_size_1285_);
lean_dec(v_size_1285_);
v___x_1510_ = lean_nat_add(v___x_1509_, v_size_1445_);
lean_dec(v___x_1509_);
v___x_1511_ = lean_nat_add(v___x_1295_, v_size_1445_);
v___x_1512_ = lean_nat_add(v___x_1511_, v_size_1458_);
lean_dec(v___x_1511_);
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 4, v_tree_1442_);
lean_ctor_set(v___x_1439_, 3, v_r_1289_);
lean_ctor_set(v___x_1439_, 2, v_v_1444_);
lean_ctor_set(v___x_1439_, 1, v_k_1443_);
lean_ctor_set(v___x_1439_, 0, v___x_1512_);
v___x_1514_ = v___x_1439_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v___x_1512_);
lean_ctor_set(v_reuseFailAlloc_1518_, 1, v_k_1443_);
lean_ctor_set(v_reuseFailAlloc_1518_, 2, v_v_1444_);
lean_ctor_set(v_reuseFailAlloc_1518_, 3, v_r_1289_);
lean_ctor_set(v_reuseFailAlloc_1518_, 4, v_tree_1442_);
v___x_1514_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
lean_object* v___x_1516_; 
if (v_isShared_1456_ == 0)
{
lean_ctor_set(v___x_1455_, 4, v___x_1514_);
lean_ctor_set(v___x_1455_, 0, v___x_1510_);
v___x_1516_ = v___x_1455_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v___x_1510_);
lean_ctor_set(v_reuseFailAlloc_1517_, 1, v_k_1286_);
lean_ctor_set(v_reuseFailAlloc_1517_, 2, v_v_1287_);
lean_ctor_set(v_reuseFailAlloc_1517_, 3, v_l_1288_);
lean_ctor_set(v_reuseFailAlloc_1517_, 4, v___x_1514_);
v___x_1516_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
return v___x_1516_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_1288_) == 0)
{
lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1548_; 
lean_inc_ref(v_l_1288_);
lean_inc(v_v_1287_);
lean_inc(v_k_1286_);
lean_inc(v_size_1285_);
v_isSharedCheck_1548_ = !lean_is_exclusive(v_l_1105_);
if (v_isSharedCheck_1548_ == 0)
{
lean_object* v_unused_1549_; lean_object* v_unused_1550_; lean_object* v_unused_1551_; lean_object* v_unused_1552_; lean_object* v_unused_1553_; 
v_unused_1549_ = lean_ctor_get(v_l_1105_, 4);
lean_dec(v_unused_1549_);
v_unused_1550_ = lean_ctor_get(v_l_1105_, 3);
lean_dec(v_unused_1550_);
v_unused_1551_ = lean_ctor_get(v_l_1105_, 2);
lean_dec(v_unused_1551_);
v_unused_1552_ = lean_ctor_get(v_l_1105_, 1);
lean_dec(v_unused_1552_);
v_unused_1553_ = lean_ctor_get(v_l_1105_, 0);
lean_dec(v_unused_1553_);
v___x_1526_ = v_l_1105_;
v_isShared_1527_ = v_isSharedCheck_1548_;
goto v_resetjp_1525_;
}
else
{
lean_dec(v_l_1105_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1548_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
if (lean_obj_tag(v_r_1289_) == 0)
{
lean_object* v_k_1528_; lean_object* v_v_1529_; lean_object* v_size_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1534_; 
v_k_1528_ = lean_ctor_get(v___x_1441_, 0);
lean_inc(v_k_1528_);
v_v_1529_ = lean_ctor_get(v___x_1441_, 1);
lean_inc(v_v_1529_);
lean_dec_ref(v___x_1441_);
v_size_1530_ = lean_ctor_get(v_r_1289_, 0);
v___x_1531_ = lean_nat_add(v___x_1295_, v_size_1285_);
lean_dec(v_size_1285_);
v___x_1532_ = lean_nat_add(v___x_1295_, v_size_1530_);
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 4, v_tree_1442_);
lean_ctor_set(v___x_1439_, 3, v_r_1289_);
lean_ctor_set(v___x_1439_, 2, v_v_1529_);
lean_ctor_set(v___x_1439_, 1, v_k_1528_);
lean_ctor_set(v___x_1439_, 0, v___x_1532_);
v___x_1534_ = v___x_1439_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v___x_1532_);
lean_ctor_set(v_reuseFailAlloc_1538_, 1, v_k_1528_);
lean_ctor_set(v_reuseFailAlloc_1538_, 2, v_v_1529_);
lean_ctor_set(v_reuseFailAlloc_1538_, 3, v_r_1289_);
lean_ctor_set(v_reuseFailAlloc_1538_, 4, v_tree_1442_);
v___x_1534_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
lean_object* v___x_1536_; 
if (v_isShared_1527_ == 0)
{
lean_ctor_set(v___x_1526_, 4, v___x_1534_);
lean_ctor_set(v___x_1526_, 0, v___x_1531_);
v___x_1536_ = v___x_1526_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v___x_1531_);
lean_ctor_set(v_reuseFailAlloc_1537_, 1, v_k_1286_);
lean_ctor_set(v_reuseFailAlloc_1537_, 2, v_v_1287_);
lean_ctor_set(v_reuseFailAlloc_1537_, 3, v_l_1288_);
lean_ctor_set(v_reuseFailAlloc_1537_, 4, v___x_1534_);
v___x_1536_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
return v___x_1536_;
}
}
}
else
{
lean_object* v_k_1539_; lean_object* v_v_1540_; lean_object* v___x_1541_; lean_object* v___x_1543_; 
lean_dec(v_size_1285_);
v_k_1539_ = lean_ctor_get(v___x_1441_, 0);
lean_inc(v_k_1539_);
v_v_1540_ = lean_ctor_get(v___x_1441_, 1);
lean_inc(v_v_1540_);
lean_dec_ref(v___x_1441_);
v___x_1541_ = lean_unsigned_to_nat(3u);
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 4, v_r_1289_);
lean_ctor_set(v___x_1439_, 3, v_r_1289_);
lean_ctor_set(v___x_1439_, 2, v_v_1540_);
lean_ctor_set(v___x_1439_, 1, v_k_1539_);
lean_ctor_set(v___x_1439_, 0, v___x_1295_);
v___x_1543_ = v___x_1439_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v___x_1295_);
lean_ctor_set(v_reuseFailAlloc_1547_, 1, v_k_1539_);
lean_ctor_set(v_reuseFailAlloc_1547_, 2, v_v_1540_);
lean_ctor_set(v_reuseFailAlloc_1547_, 3, v_r_1289_);
lean_ctor_set(v_reuseFailAlloc_1547_, 4, v_r_1289_);
v___x_1543_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
lean_object* v___x_1545_; 
if (v_isShared_1527_ == 0)
{
lean_ctor_set(v___x_1526_, 4, v___x_1543_);
lean_ctor_set(v___x_1526_, 0, v___x_1541_);
v___x_1545_ = v___x_1526_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v___x_1541_);
lean_ctor_set(v_reuseFailAlloc_1546_, 1, v_k_1286_);
lean_ctor_set(v_reuseFailAlloc_1546_, 2, v_v_1287_);
lean_ctor_set(v_reuseFailAlloc_1546_, 3, v_l_1288_);
lean_ctor_set(v_reuseFailAlloc_1546_, 4, v___x_1543_);
v___x_1545_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
return v___x_1545_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1289_) == 0)
{
lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1578_; 
lean_inc(v_l_1288_);
lean_inc(v_v_1287_);
lean_inc(v_k_1286_);
v_isSharedCheck_1578_ = !lean_is_exclusive(v_l_1105_);
if (v_isSharedCheck_1578_ == 0)
{
lean_object* v_unused_1579_; lean_object* v_unused_1580_; lean_object* v_unused_1581_; lean_object* v_unused_1582_; lean_object* v_unused_1583_; 
v_unused_1579_ = lean_ctor_get(v_l_1105_, 4);
lean_dec(v_unused_1579_);
v_unused_1580_ = lean_ctor_get(v_l_1105_, 3);
lean_dec(v_unused_1580_);
v_unused_1581_ = lean_ctor_get(v_l_1105_, 2);
lean_dec(v_unused_1581_);
v_unused_1582_ = lean_ctor_get(v_l_1105_, 1);
lean_dec(v_unused_1582_);
v_unused_1583_ = lean_ctor_get(v_l_1105_, 0);
lean_dec(v_unused_1583_);
v___x_1555_ = v_l_1105_;
v_isShared_1556_ = v_isSharedCheck_1578_;
goto v_resetjp_1554_;
}
else
{
lean_dec(v_l_1105_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1578_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v_k_1557_; lean_object* v_v_1558_; lean_object* v_k_1559_; lean_object* v_v_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1574_; 
v_k_1557_ = lean_ctor_get(v___x_1441_, 0);
lean_inc(v_k_1557_);
v_v_1558_ = lean_ctor_get(v___x_1441_, 1);
lean_inc(v_v_1558_);
lean_dec_ref(v___x_1441_);
v_k_1559_ = lean_ctor_get(v_r_1289_, 1);
v_v_1560_ = lean_ctor_get(v_r_1289_, 2);
v_isSharedCheck_1574_ = !lean_is_exclusive(v_r_1289_);
if (v_isSharedCheck_1574_ == 0)
{
lean_object* v_unused_1575_; lean_object* v_unused_1576_; lean_object* v_unused_1577_; 
v_unused_1575_ = lean_ctor_get(v_r_1289_, 4);
lean_dec(v_unused_1575_);
v_unused_1576_ = lean_ctor_get(v_r_1289_, 3);
lean_dec(v_unused_1576_);
v_unused_1577_ = lean_ctor_get(v_r_1289_, 0);
lean_dec(v_unused_1577_);
v___x_1562_ = v_r_1289_;
v_isShared_1563_ = v_isSharedCheck_1574_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_v_1560_);
lean_inc(v_k_1559_);
lean_dec(v_r_1289_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1574_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1564_; lean_object* v___x_1566_; 
v___x_1564_ = lean_unsigned_to_nat(3u);
if (v_isShared_1563_ == 0)
{
lean_ctor_set(v___x_1562_, 4, v_l_1288_);
lean_ctor_set(v___x_1562_, 3, v_l_1288_);
lean_ctor_set(v___x_1562_, 2, v_v_1287_);
lean_ctor_set(v___x_1562_, 1, v_k_1286_);
lean_ctor_set(v___x_1562_, 0, v___x_1295_);
v___x_1566_ = v___x_1562_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v___x_1295_);
lean_ctor_set(v_reuseFailAlloc_1573_, 1, v_k_1286_);
lean_ctor_set(v_reuseFailAlloc_1573_, 2, v_v_1287_);
lean_ctor_set(v_reuseFailAlloc_1573_, 3, v_l_1288_);
lean_ctor_set(v_reuseFailAlloc_1573_, 4, v_l_1288_);
v___x_1566_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
lean_object* v___x_1568_; 
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 4, v_l_1288_);
lean_ctor_set(v___x_1439_, 3, v_l_1288_);
lean_ctor_set(v___x_1439_, 2, v_v_1558_);
lean_ctor_set(v___x_1439_, 1, v_k_1557_);
lean_ctor_set(v___x_1439_, 0, v___x_1295_);
v___x_1568_ = v___x_1439_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v___x_1295_);
lean_ctor_set(v_reuseFailAlloc_1572_, 1, v_k_1557_);
lean_ctor_set(v_reuseFailAlloc_1572_, 2, v_v_1558_);
lean_ctor_set(v_reuseFailAlloc_1572_, 3, v_l_1288_);
lean_ctor_set(v_reuseFailAlloc_1572_, 4, v_l_1288_);
v___x_1568_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
lean_object* v___x_1570_; 
if (v_isShared_1556_ == 0)
{
lean_ctor_set(v___x_1555_, 4, v___x_1568_);
lean_ctor_set(v___x_1555_, 3, v___x_1566_);
lean_ctor_set(v___x_1555_, 2, v_v_1560_);
lean_ctor_set(v___x_1555_, 1, v_k_1559_);
lean_ctor_set(v___x_1555_, 0, v___x_1564_);
v___x_1570_ = v___x_1555_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v___x_1564_);
lean_ctor_set(v_reuseFailAlloc_1571_, 1, v_k_1559_);
lean_ctor_set(v_reuseFailAlloc_1571_, 2, v_v_1560_);
lean_ctor_set(v_reuseFailAlloc_1571_, 3, v___x_1566_);
lean_ctor_set(v_reuseFailAlloc_1571_, 4, v___x_1568_);
v___x_1570_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
return v___x_1570_;
}
}
}
}
}
}
else
{
lean_object* v_k_1584_; lean_object* v_v_1585_; lean_object* v___x_1586_; lean_object* v___x_1588_; 
v_k_1584_ = lean_ctor_get(v___x_1441_, 0);
lean_inc(v_k_1584_);
v_v_1585_ = lean_ctor_get(v___x_1441_, 1);
lean_inc(v_v_1585_);
lean_dec_ref(v___x_1441_);
v___x_1586_ = lean_unsigned_to_nat(2u);
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 4, v_r_1289_);
lean_ctor_set(v___x_1439_, 3, v_l_1105_);
lean_ctor_set(v___x_1439_, 2, v_v_1585_);
lean_ctor_set(v___x_1439_, 1, v_k_1584_);
lean_ctor_set(v___x_1439_, 0, v___x_1586_);
v___x_1588_ = v___x_1439_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v___x_1586_);
lean_ctor_set(v_reuseFailAlloc_1589_, 1, v_k_1584_);
lean_ctor_set(v_reuseFailAlloc_1589_, 2, v_v_1585_);
lean_ctor_set(v_reuseFailAlloc_1589_, 3, v_l_1105_);
lean_ctor_set(v_reuseFailAlloc_1589_, 4, v_r_1289_);
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
}
else
{
return v_l_1105_;
}
}
else
{
return v_r_1106_;
}
}
default: 
{
lean_object* v_impl_1596_; lean_object* v___x_1597_; 
v_impl_1596_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_k_1101_, v_r_1106_);
v___x_1597_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1596_) == 0)
{
if (lean_obj_tag(v_l_1105_) == 0)
{
lean_object* v_size_1598_; lean_object* v_size_1599_; lean_object* v_k_1600_; lean_object* v_v_1601_; lean_object* v_l_1602_; lean_object* v_r_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; uint8_t v___x_1606_; 
v_size_1598_ = lean_ctor_get(v_impl_1596_, 0);
lean_inc(v_size_1598_);
v_size_1599_ = lean_ctor_get(v_l_1105_, 0);
v_k_1600_ = lean_ctor_get(v_l_1105_, 1);
v_v_1601_ = lean_ctor_get(v_l_1105_, 2);
v_l_1602_ = lean_ctor_get(v_l_1105_, 3);
v_r_1603_ = lean_ctor_get(v_l_1105_, 4);
lean_inc(v_r_1603_);
v___x_1604_ = lean_unsigned_to_nat(3u);
v___x_1605_ = lean_nat_mul(v___x_1604_, v_size_1598_);
v___x_1606_ = lean_nat_dec_lt(v___x_1605_, v_size_1599_);
lean_dec(v___x_1605_);
if (v___x_1606_ == 0)
{
lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1610_; 
lean_dec(v_r_1603_);
v___x_1607_ = lean_nat_add(v___x_1597_, v_size_1599_);
v___x_1608_ = lean_nat_add(v___x_1607_, v_size_1598_);
lean_dec(v_size_1598_);
lean_dec(v___x_1607_);
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 4, v_impl_1596_);
lean_ctor_set(v___x_1108_, 0, v___x_1608_);
v___x_1610_ = v___x_1108_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v___x_1608_);
lean_ctor_set(v_reuseFailAlloc_1611_, 1, v_k_1103_);
lean_ctor_set(v_reuseFailAlloc_1611_, 2, v_v_1104_);
lean_ctor_set(v_reuseFailAlloc_1611_, 3, v_l_1105_);
lean_ctor_set(v_reuseFailAlloc_1611_, 4, v_impl_1596_);
v___x_1610_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
return v___x_1610_;
}
}
else
{
lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1677_; 
lean_inc(v_l_1602_);
lean_inc(v_v_1601_);
lean_inc(v_k_1600_);
lean_inc(v_size_1599_);
v_isSharedCheck_1677_ = !lean_is_exclusive(v_l_1105_);
if (v_isSharedCheck_1677_ == 0)
{
lean_object* v_unused_1678_; lean_object* v_unused_1679_; lean_object* v_unused_1680_; lean_object* v_unused_1681_; lean_object* v_unused_1682_; 
v_unused_1678_ = lean_ctor_get(v_l_1105_, 4);
lean_dec(v_unused_1678_);
v_unused_1679_ = lean_ctor_get(v_l_1105_, 3);
lean_dec(v_unused_1679_);
v_unused_1680_ = lean_ctor_get(v_l_1105_, 2);
lean_dec(v_unused_1680_);
v_unused_1681_ = lean_ctor_get(v_l_1105_, 1);
lean_dec(v_unused_1681_);
v_unused_1682_ = lean_ctor_get(v_l_1105_, 0);
lean_dec(v_unused_1682_);
v___x_1613_ = v_l_1105_;
v_isShared_1614_ = v_isSharedCheck_1677_;
goto v_resetjp_1612_;
}
else
{
lean_dec(v_l_1105_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1677_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v_size_1615_; lean_object* v_size_1616_; lean_object* v_k_1617_; lean_object* v_v_1618_; lean_object* v_l_1619_; lean_object* v_r_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; uint8_t v___x_1623_; 
v_size_1615_ = lean_ctor_get(v_l_1602_, 0);
v_size_1616_ = lean_ctor_get(v_r_1603_, 0);
v_k_1617_ = lean_ctor_get(v_r_1603_, 1);
v_v_1618_ = lean_ctor_get(v_r_1603_, 2);
v_l_1619_ = lean_ctor_get(v_r_1603_, 3);
v_r_1620_ = lean_ctor_get(v_r_1603_, 4);
v___x_1621_ = lean_unsigned_to_nat(2u);
v___x_1622_ = lean_nat_mul(v___x_1621_, v_size_1615_);
v___x_1623_ = lean_nat_dec_lt(v_size_1616_, v___x_1622_);
lean_dec(v___x_1622_);
if (v___x_1623_ == 0)
{
lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1652_; 
lean_inc(v_r_1620_);
lean_inc(v_l_1619_);
lean_inc(v_v_1618_);
lean_inc(v_k_1617_);
v_isSharedCheck_1652_ = !lean_is_exclusive(v_r_1603_);
if (v_isSharedCheck_1652_ == 0)
{
lean_object* v_unused_1653_; lean_object* v_unused_1654_; lean_object* v_unused_1655_; lean_object* v_unused_1656_; lean_object* v_unused_1657_; 
v_unused_1653_ = lean_ctor_get(v_r_1603_, 4);
lean_dec(v_unused_1653_);
v_unused_1654_ = lean_ctor_get(v_r_1603_, 3);
lean_dec(v_unused_1654_);
v_unused_1655_ = lean_ctor_get(v_r_1603_, 2);
lean_dec(v_unused_1655_);
v_unused_1656_ = lean_ctor_get(v_r_1603_, 1);
lean_dec(v_unused_1656_);
v_unused_1657_ = lean_ctor_get(v_r_1603_, 0);
lean_dec(v_unused_1657_);
v___x_1625_ = v_r_1603_;
v_isShared_1626_ = v_isSharedCheck_1652_;
goto v_resetjp_1624_;
}
else
{
lean_dec(v_r_1603_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1652_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___y_1630_; lean_object* v___y_1631_; lean_object* v___y_1632_; lean_object* v___x_1640_; lean_object* v___y_1642_; 
v___x_1627_ = lean_nat_add(v___x_1597_, v_size_1599_);
lean_dec(v_size_1599_);
v___x_1628_ = lean_nat_add(v___x_1627_, v_size_1598_);
lean_dec(v___x_1627_);
v___x_1640_ = lean_nat_add(v___x_1597_, v_size_1615_);
if (lean_obj_tag(v_l_1619_) == 0)
{
lean_object* v_size_1650_; 
v_size_1650_ = lean_ctor_get(v_l_1619_, 0);
lean_inc(v_size_1650_);
v___y_1642_ = v_size_1650_;
goto v___jp_1641_;
}
else
{
lean_object* v___x_1651_; 
v___x_1651_ = lean_unsigned_to_nat(0u);
v___y_1642_ = v___x_1651_;
goto v___jp_1641_;
}
v___jp_1629_:
{
lean_object* v___x_1633_; lean_object* v___x_1635_; 
v___x_1633_ = lean_nat_add(v___y_1630_, v___y_1632_);
lean_dec(v___y_1632_);
lean_dec(v___y_1630_);
if (v_isShared_1626_ == 0)
{
lean_ctor_set(v___x_1625_, 4, v_impl_1596_);
lean_ctor_set(v___x_1625_, 3, v_r_1620_);
lean_ctor_set(v___x_1625_, 2, v_v_1104_);
lean_ctor_set(v___x_1625_, 1, v_k_1103_);
lean_ctor_set(v___x_1625_, 0, v___x_1633_);
v___x_1635_ = v___x_1625_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v___x_1633_);
lean_ctor_set(v_reuseFailAlloc_1639_, 1, v_k_1103_);
lean_ctor_set(v_reuseFailAlloc_1639_, 2, v_v_1104_);
lean_ctor_set(v_reuseFailAlloc_1639_, 3, v_r_1620_);
lean_ctor_set(v_reuseFailAlloc_1639_, 4, v_impl_1596_);
v___x_1635_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
lean_object* v___x_1637_; 
if (v_isShared_1614_ == 0)
{
lean_ctor_set(v___x_1613_, 4, v___x_1635_);
lean_ctor_set(v___x_1613_, 3, v___y_1631_);
lean_ctor_set(v___x_1613_, 2, v_v_1618_);
lean_ctor_set(v___x_1613_, 1, v_k_1617_);
lean_ctor_set(v___x_1613_, 0, v___x_1628_);
v___x_1637_ = v___x_1613_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v___x_1628_);
lean_ctor_set(v_reuseFailAlloc_1638_, 1, v_k_1617_);
lean_ctor_set(v_reuseFailAlloc_1638_, 2, v_v_1618_);
lean_ctor_set(v_reuseFailAlloc_1638_, 3, v___y_1631_);
lean_ctor_set(v_reuseFailAlloc_1638_, 4, v___x_1635_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
return v___x_1637_;
}
}
}
v___jp_1641_:
{
lean_object* v___x_1643_; lean_object* v___x_1645_; 
v___x_1643_ = lean_nat_add(v___x_1640_, v___y_1642_);
lean_dec(v___y_1642_);
lean_dec(v___x_1640_);
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 4, v_l_1619_);
lean_ctor_set(v___x_1108_, 3, v_l_1602_);
lean_ctor_set(v___x_1108_, 2, v_v_1601_);
lean_ctor_set(v___x_1108_, 1, v_k_1600_);
lean_ctor_set(v___x_1108_, 0, v___x_1643_);
v___x_1645_ = v___x_1108_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v___x_1643_);
lean_ctor_set(v_reuseFailAlloc_1649_, 1, v_k_1600_);
lean_ctor_set(v_reuseFailAlloc_1649_, 2, v_v_1601_);
lean_ctor_set(v_reuseFailAlloc_1649_, 3, v_l_1602_);
lean_ctor_set(v_reuseFailAlloc_1649_, 4, v_l_1619_);
v___x_1645_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
lean_object* v___x_1646_; 
v___x_1646_ = lean_nat_add(v___x_1597_, v_size_1598_);
lean_dec(v_size_1598_);
if (lean_obj_tag(v_r_1620_) == 0)
{
lean_object* v_size_1647_; 
v_size_1647_ = lean_ctor_get(v_r_1620_, 0);
lean_inc(v_size_1647_);
v___y_1630_ = v___x_1646_;
v___y_1631_ = v___x_1645_;
v___y_1632_ = v_size_1647_;
goto v___jp_1629_;
}
else
{
lean_object* v___x_1648_; 
v___x_1648_ = lean_unsigned_to_nat(0u);
v___y_1630_ = v___x_1646_;
v___y_1631_ = v___x_1645_;
v___y_1632_ = v___x_1648_;
goto v___jp_1629_;
}
}
}
}
}
else
{
lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1663_; 
lean_del_object(v___x_1108_);
v___x_1658_ = lean_nat_add(v___x_1597_, v_size_1599_);
lean_dec(v_size_1599_);
v___x_1659_ = lean_nat_add(v___x_1658_, v_size_1598_);
lean_dec(v___x_1658_);
v___x_1660_ = lean_nat_add(v___x_1597_, v_size_1598_);
lean_dec(v_size_1598_);
v___x_1661_ = lean_nat_add(v___x_1660_, v_size_1616_);
lean_dec(v___x_1660_);
lean_inc_ref(v_impl_1596_);
if (v_isShared_1614_ == 0)
{
lean_ctor_set(v___x_1613_, 4, v_impl_1596_);
lean_ctor_set(v___x_1613_, 3, v_r_1603_);
lean_ctor_set(v___x_1613_, 2, v_v_1104_);
lean_ctor_set(v___x_1613_, 1, v_k_1103_);
lean_ctor_set(v___x_1613_, 0, v___x_1661_);
v___x_1663_ = v___x_1613_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v___x_1661_);
lean_ctor_set(v_reuseFailAlloc_1676_, 1, v_k_1103_);
lean_ctor_set(v_reuseFailAlloc_1676_, 2, v_v_1104_);
lean_ctor_set(v_reuseFailAlloc_1676_, 3, v_r_1603_);
lean_ctor_set(v_reuseFailAlloc_1676_, 4, v_impl_1596_);
v___x_1663_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1670_; 
v_isSharedCheck_1670_ = !lean_is_exclusive(v_impl_1596_);
if (v_isSharedCheck_1670_ == 0)
{
lean_object* v_unused_1671_; lean_object* v_unused_1672_; lean_object* v_unused_1673_; lean_object* v_unused_1674_; lean_object* v_unused_1675_; 
v_unused_1671_ = lean_ctor_get(v_impl_1596_, 4);
lean_dec(v_unused_1671_);
v_unused_1672_ = lean_ctor_get(v_impl_1596_, 3);
lean_dec(v_unused_1672_);
v_unused_1673_ = lean_ctor_get(v_impl_1596_, 2);
lean_dec(v_unused_1673_);
v_unused_1674_ = lean_ctor_get(v_impl_1596_, 1);
lean_dec(v_unused_1674_);
v_unused_1675_ = lean_ctor_get(v_impl_1596_, 0);
lean_dec(v_unused_1675_);
v___x_1665_ = v_impl_1596_;
v_isShared_1666_ = v_isSharedCheck_1670_;
goto v_resetjp_1664_;
}
else
{
lean_dec(v_impl_1596_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1670_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
lean_object* v___x_1668_; 
if (v_isShared_1666_ == 0)
{
lean_ctor_set(v___x_1665_, 4, v___x_1663_);
lean_ctor_set(v___x_1665_, 3, v_l_1602_);
lean_ctor_set(v___x_1665_, 2, v_v_1601_);
lean_ctor_set(v___x_1665_, 1, v_k_1600_);
lean_ctor_set(v___x_1665_, 0, v___x_1659_);
v___x_1668_ = v___x_1665_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v___x_1659_);
lean_ctor_set(v_reuseFailAlloc_1669_, 1, v_k_1600_);
lean_ctor_set(v_reuseFailAlloc_1669_, 2, v_v_1601_);
lean_ctor_set(v_reuseFailAlloc_1669_, 3, v_l_1602_);
lean_ctor_set(v_reuseFailAlloc_1669_, 4, v___x_1663_);
v___x_1668_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
return v___x_1668_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1683_; lean_object* v___x_1684_; lean_object* v___x_1686_; 
v_size_1683_ = lean_ctor_get(v_impl_1596_, 0);
lean_inc(v_size_1683_);
v___x_1684_ = lean_nat_add(v___x_1597_, v_size_1683_);
lean_dec(v_size_1683_);
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 4, v_impl_1596_);
lean_ctor_set(v___x_1108_, 0, v___x_1684_);
v___x_1686_ = v___x_1108_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v___x_1684_);
lean_ctor_set(v_reuseFailAlloc_1687_, 1, v_k_1103_);
lean_ctor_set(v_reuseFailAlloc_1687_, 2, v_v_1104_);
lean_ctor_set(v_reuseFailAlloc_1687_, 3, v_l_1105_);
lean_ctor_set(v_reuseFailAlloc_1687_, 4, v_impl_1596_);
v___x_1686_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
return v___x_1686_;
}
}
}
else
{
if (lean_obj_tag(v_l_1105_) == 0)
{
lean_object* v_l_1688_; 
v_l_1688_ = lean_ctor_get(v_l_1105_, 3);
if (lean_obj_tag(v_l_1688_) == 0)
{
lean_object* v_r_1689_; 
lean_inc_ref(v_l_1688_);
v_r_1689_ = lean_ctor_get(v_l_1105_, 4);
lean_inc(v_r_1689_);
if (lean_obj_tag(v_r_1689_) == 0)
{
lean_object* v_size_1690_; lean_object* v_k_1691_; lean_object* v_v_1692_; lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1705_; 
v_size_1690_ = lean_ctor_get(v_l_1105_, 0);
v_k_1691_ = lean_ctor_get(v_l_1105_, 1);
v_v_1692_ = lean_ctor_get(v_l_1105_, 2);
v_isSharedCheck_1705_ = !lean_is_exclusive(v_l_1105_);
if (v_isSharedCheck_1705_ == 0)
{
lean_object* v_unused_1706_; lean_object* v_unused_1707_; 
v_unused_1706_ = lean_ctor_get(v_l_1105_, 4);
lean_dec(v_unused_1706_);
v_unused_1707_ = lean_ctor_get(v_l_1105_, 3);
lean_dec(v_unused_1707_);
v___x_1694_ = v_l_1105_;
v_isShared_1695_ = v_isSharedCheck_1705_;
goto v_resetjp_1693_;
}
else
{
lean_inc(v_v_1692_);
lean_inc(v_k_1691_);
lean_inc(v_size_1690_);
lean_dec(v_l_1105_);
v___x_1694_ = lean_box(0);
v_isShared_1695_ = v_isSharedCheck_1705_;
goto v_resetjp_1693_;
}
v_resetjp_1693_:
{
lean_object* v_size_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1700_; 
v_size_1696_ = lean_ctor_get(v_r_1689_, 0);
v___x_1697_ = lean_nat_add(v___x_1597_, v_size_1690_);
lean_dec(v_size_1690_);
v___x_1698_ = lean_nat_add(v___x_1597_, v_size_1696_);
if (v_isShared_1695_ == 0)
{
lean_ctor_set(v___x_1694_, 4, v_impl_1596_);
lean_ctor_set(v___x_1694_, 3, v_r_1689_);
lean_ctor_set(v___x_1694_, 2, v_v_1104_);
lean_ctor_set(v___x_1694_, 1, v_k_1103_);
lean_ctor_set(v___x_1694_, 0, v___x_1698_);
v___x_1700_ = v___x_1694_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v___x_1698_);
lean_ctor_set(v_reuseFailAlloc_1704_, 1, v_k_1103_);
lean_ctor_set(v_reuseFailAlloc_1704_, 2, v_v_1104_);
lean_ctor_set(v_reuseFailAlloc_1704_, 3, v_r_1689_);
lean_ctor_set(v_reuseFailAlloc_1704_, 4, v_impl_1596_);
v___x_1700_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
lean_object* v___x_1702_; 
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 4, v___x_1700_);
lean_ctor_set(v___x_1108_, 3, v_l_1688_);
lean_ctor_set(v___x_1108_, 2, v_v_1692_);
lean_ctor_set(v___x_1108_, 1, v_k_1691_);
lean_ctor_set(v___x_1108_, 0, v___x_1697_);
v___x_1702_ = v___x_1108_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v___x_1697_);
lean_ctor_set(v_reuseFailAlloc_1703_, 1, v_k_1691_);
lean_ctor_set(v_reuseFailAlloc_1703_, 2, v_v_1692_);
lean_ctor_set(v_reuseFailAlloc_1703_, 3, v_l_1688_);
lean_ctor_set(v_reuseFailAlloc_1703_, 4, v___x_1700_);
v___x_1702_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
return v___x_1702_;
}
}
}
}
else
{
lean_object* v_k_1708_; lean_object* v_v_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1720_; 
v_k_1708_ = lean_ctor_get(v_l_1105_, 1);
v_v_1709_ = lean_ctor_get(v_l_1105_, 2);
v_isSharedCheck_1720_ = !lean_is_exclusive(v_l_1105_);
if (v_isSharedCheck_1720_ == 0)
{
lean_object* v_unused_1721_; lean_object* v_unused_1722_; lean_object* v_unused_1723_; 
v_unused_1721_ = lean_ctor_get(v_l_1105_, 4);
lean_dec(v_unused_1721_);
v_unused_1722_ = lean_ctor_get(v_l_1105_, 3);
lean_dec(v_unused_1722_);
v_unused_1723_ = lean_ctor_get(v_l_1105_, 0);
lean_dec(v_unused_1723_);
v___x_1711_ = v_l_1105_;
v_isShared_1712_ = v_isSharedCheck_1720_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_v_1709_);
lean_inc(v_k_1708_);
lean_dec(v_l_1105_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1720_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v___x_1713_; lean_object* v___x_1715_; 
v___x_1713_ = lean_unsigned_to_nat(3u);
if (v_isShared_1712_ == 0)
{
lean_ctor_set(v___x_1711_, 3, v_r_1689_);
lean_ctor_set(v___x_1711_, 2, v_v_1104_);
lean_ctor_set(v___x_1711_, 1, v_k_1103_);
lean_ctor_set(v___x_1711_, 0, v___x_1597_);
v___x_1715_ = v___x_1711_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v___x_1597_);
lean_ctor_set(v_reuseFailAlloc_1719_, 1, v_k_1103_);
lean_ctor_set(v_reuseFailAlloc_1719_, 2, v_v_1104_);
lean_ctor_set(v_reuseFailAlloc_1719_, 3, v_r_1689_);
lean_ctor_set(v_reuseFailAlloc_1719_, 4, v_r_1689_);
v___x_1715_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
lean_object* v___x_1717_; 
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 4, v___x_1715_);
lean_ctor_set(v___x_1108_, 3, v_l_1688_);
lean_ctor_set(v___x_1108_, 2, v_v_1709_);
lean_ctor_set(v___x_1108_, 1, v_k_1708_);
lean_ctor_set(v___x_1108_, 0, v___x_1713_);
v___x_1717_ = v___x_1108_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v___x_1713_);
lean_ctor_set(v_reuseFailAlloc_1718_, 1, v_k_1708_);
lean_ctor_set(v_reuseFailAlloc_1718_, 2, v_v_1709_);
lean_ctor_set(v_reuseFailAlloc_1718_, 3, v_l_1688_);
lean_ctor_set(v_reuseFailAlloc_1718_, 4, v___x_1715_);
v___x_1717_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
return v___x_1717_;
}
}
}
}
}
else
{
lean_object* v_r_1724_; 
v_r_1724_ = lean_ctor_get(v_l_1105_, 4);
lean_inc(v_r_1724_);
if (lean_obj_tag(v_r_1724_) == 0)
{
lean_object* v_k_1725_; lean_object* v_v_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1749_; 
lean_inc(v_l_1688_);
v_k_1725_ = lean_ctor_get(v_l_1105_, 1);
v_v_1726_ = lean_ctor_get(v_l_1105_, 2);
v_isSharedCheck_1749_ = !lean_is_exclusive(v_l_1105_);
if (v_isSharedCheck_1749_ == 0)
{
lean_object* v_unused_1750_; lean_object* v_unused_1751_; lean_object* v_unused_1752_; 
v_unused_1750_ = lean_ctor_get(v_l_1105_, 4);
lean_dec(v_unused_1750_);
v_unused_1751_ = lean_ctor_get(v_l_1105_, 3);
lean_dec(v_unused_1751_);
v_unused_1752_ = lean_ctor_get(v_l_1105_, 0);
lean_dec(v_unused_1752_);
v___x_1728_ = v_l_1105_;
v_isShared_1729_ = v_isSharedCheck_1749_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_v_1726_);
lean_inc(v_k_1725_);
lean_dec(v_l_1105_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1749_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v_k_1730_; lean_object* v_v_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1745_; 
v_k_1730_ = lean_ctor_get(v_r_1724_, 1);
v_v_1731_ = lean_ctor_get(v_r_1724_, 2);
v_isSharedCheck_1745_ = !lean_is_exclusive(v_r_1724_);
if (v_isSharedCheck_1745_ == 0)
{
lean_object* v_unused_1746_; lean_object* v_unused_1747_; lean_object* v_unused_1748_; 
v_unused_1746_ = lean_ctor_get(v_r_1724_, 4);
lean_dec(v_unused_1746_);
v_unused_1747_ = lean_ctor_get(v_r_1724_, 3);
lean_dec(v_unused_1747_);
v_unused_1748_ = lean_ctor_get(v_r_1724_, 0);
lean_dec(v_unused_1748_);
v___x_1733_ = v_r_1724_;
v_isShared_1734_ = v_isSharedCheck_1745_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_v_1731_);
lean_inc(v_k_1730_);
lean_dec(v_r_1724_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1745_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
lean_object* v___x_1735_; lean_object* v___x_1737_; 
v___x_1735_ = lean_unsigned_to_nat(3u);
if (v_isShared_1734_ == 0)
{
lean_ctor_set(v___x_1733_, 4, v_l_1688_);
lean_ctor_set(v___x_1733_, 3, v_l_1688_);
lean_ctor_set(v___x_1733_, 2, v_v_1726_);
lean_ctor_set(v___x_1733_, 1, v_k_1725_);
lean_ctor_set(v___x_1733_, 0, v___x_1597_);
v___x_1737_ = v___x_1733_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v___x_1597_);
lean_ctor_set(v_reuseFailAlloc_1744_, 1, v_k_1725_);
lean_ctor_set(v_reuseFailAlloc_1744_, 2, v_v_1726_);
lean_ctor_set(v_reuseFailAlloc_1744_, 3, v_l_1688_);
lean_ctor_set(v_reuseFailAlloc_1744_, 4, v_l_1688_);
v___x_1737_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
lean_object* v___x_1739_; 
if (v_isShared_1729_ == 0)
{
lean_ctor_set(v___x_1728_, 4, v_l_1688_);
lean_ctor_set(v___x_1728_, 2, v_v_1104_);
lean_ctor_set(v___x_1728_, 1, v_k_1103_);
lean_ctor_set(v___x_1728_, 0, v___x_1597_);
v___x_1739_ = v___x_1728_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v___x_1597_);
lean_ctor_set(v_reuseFailAlloc_1743_, 1, v_k_1103_);
lean_ctor_set(v_reuseFailAlloc_1743_, 2, v_v_1104_);
lean_ctor_set(v_reuseFailAlloc_1743_, 3, v_l_1688_);
lean_ctor_set(v_reuseFailAlloc_1743_, 4, v_l_1688_);
v___x_1739_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
lean_object* v___x_1741_; 
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 4, v___x_1739_);
lean_ctor_set(v___x_1108_, 3, v___x_1737_);
lean_ctor_set(v___x_1108_, 2, v_v_1731_);
lean_ctor_set(v___x_1108_, 1, v_k_1730_);
lean_ctor_set(v___x_1108_, 0, v___x_1735_);
v___x_1741_ = v___x_1108_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v___x_1735_);
lean_ctor_set(v_reuseFailAlloc_1742_, 1, v_k_1730_);
lean_ctor_set(v_reuseFailAlloc_1742_, 2, v_v_1731_);
lean_ctor_set(v_reuseFailAlloc_1742_, 3, v___x_1737_);
lean_ctor_set(v_reuseFailAlloc_1742_, 4, v___x_1739_);
v___x_1741_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
return v___x_1741_;
}
}
}
}
}
}
else
{
lean_object* v___x_1753_; lean_object* v___x_1755_; 
v___x_1753_ = lean_unsigned_to_nat(2u);
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 4, v_r_1724_);
lean_ctor_set(v___x_1108_, 0, v___x_1753_);
v___x_1755_ = v___x_1108_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v___x_1753_);
lean_ctor_set(v_reuseFailAlloc_1756_, 1, v_k_1103_);
lean_ctor_set(v_reuseFailAlloc_1756_, 2, v_v_1104_);
lean_ctor_set(v_reuseFailAlloc_1756_, 3, v_l_1105_);
lean_ctor_set(v_reuseFailAlloc_1756_, 4, v_r_1724_);
v___x_1755_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
return v___x_1755_;
}
}
}
}
else
{
lean_object* v___x_1758_; 
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 4, v_l_1105_);
lean_ctor_set(v___x_1108_, 0, v___x_1597_);
v___x_1758_ = v___x_1108_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v___x_1597_);
lean_ctor_set(v_reuseFailAlloc_1759_, 1, v_k_1103_);
lean_ctor_set(v_reuseFailAlloc_1759_, 2, v_v_1104_);
lean_ctor_set(v_reuseFailAlloc_1759_, 3, v_l_1105_);
lean_ctor_set(v_reuseFailAlloc_1759_, 4, v_l_1105_);
v___x_1758_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
return v___x_1758_;
}
}
}
}
}
}
}
else
{
return v_t_1102_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg___boxed(lean_object* v_k_1762_, lean_object* v_t_1763_){
_start:
{
lean_object* v_res_1764_; 
v_res_1764_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_k_1762_, v_t_1763_);
lean_dec_ref(v_k_1762_);
return v_res_1764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___lam__0(lean_object* v_val_1765_, lean_object* v_s_1766_){
_start:
{
lean_object* v_toRing_1767_; lean_object* v_invFn_x3f_1768_; lean_object* v_semiringId_x3f_1769_; lean_object* v_commSemiringInst_1770_; lean_object* v_commRingInst_1771_; lean_object* v_noZeroDivInst_x3f_1772_; lean_object* v_fieldInst_x3f_1773_; lean_object* v_powIdentityInst_x3f_1774_; lean_object* v_denoteEntries_1775_; lean_object* v_nextId_1776_; lean_object* v_steps_1777_; lean_object* v_queue_1778_; lean_object* v_basis_1779_; lean_object* v_diseqs_1780_; uint8_t v_recheck_1781_; lean_object* v_invSet_1782_; lean_object* v_powIdentityVarCount_1783_; lean_object* v_numEq0_x3f_1784_; uint8_t v_numEq0Updated_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1793_; 
v_toRing_1767_ = lean_ctor_get(v_s_1766_, 0);
v_invFn_x3f_1768_ = lean_ctor_get(v_s_1766_, 1);
v_semiringId_x3f_1769_ = lean_ctor_get(v_s_1766_, 2);
v_commSemiringInst_1770_ = lean_ctor_get(v_s_1766_, 3);
v_commRingInst_1771_ = lean_ctor_get(v_s_1766_, 4);
v_noZeroDivInst_x3f_1772_ = lean_ctor_get(v_s_1766_, 5);
v_fieldInst_x3f_1773_ = lean_ctor_get(v_s_1766_, 6);
v_powIdentityInst_x3f_1774_ = lean_ctor_get(v_s_1766_, 7);
v_denoteEntries_1775_ = lean_ctor_get(v_s_1766_, 8);
v_nextId_1776_ = lean_ctor_get(v_s_1766_, 9);
v_steps_1777_ = lean_ctor_get(v_s_1766_, 10);
v_queue_1778_ = lean_ctor_get(v_s_1766_, 11);
v_basis_1779_ = lean_ctor_get(v_s_1766_, 12);
v_diseqs_1780_ = lean_ctor_get(v_s_1766_, 13);
v_recheck_1781_ = lean_ctor_get_uint8(v_s_1766_, sizeof(void*)*17);
v_invSet_1782_ = lean_ctor_get(v_s_1766_, 14);
v_powIdentityVarCount_1783_ = lean_ctor_get(v_s_1766_, 15);
v_numEq0_x3f_1784_ = lean_ctor_get(v_s_1766_, 16);
v_numEq0Updated_1785_ = lean_ctor_get_uint8(v_s_1766_, sizeof(void*)*17 + 1);
v_isSharedCheck_1793_ = !lean_is_exclusive(v_s_1766_);
if (v_isSharedCheck_1793_ == 0)
{
v___x_1787_ = v_s_1766_;
v_isShared_1788_ = v_isSharedCheck_1793_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_numEq0_x3f_1784_);
lean_inc(v_powIdentityVarCount_1783_);
lean_inc(v_invSet_1782_);
lean_inc(v_diseqs_1780_);
lean_inc(v_basis_1779_);
lean_inc(v_queue_1778_);
lean_inc(v_steps_1777_);
lean_inc(v_nextId_1776_);
lean_inc(v_denoteEntries_1775_);
lean_inc(v_powIdentityInst_x3f_1774_);
lean_inc(v_fieldInst_x3f_1773_);
lean_inc(v_noZeroDivInst_x3f_1772_);
lean_inc(v_commRingInst_1771_);
lean_inc(v_commSemiringInst_1770_);
lean_inc(v_semiringId_x3f_1769_);
lean_inc(v_invFn_x3f_1768_);
lean_inc(v_toRing_1767_);
lean_dec(v_s_1766_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1793_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
lean_object* v___x_1789_; lean_object* v___x_1791_; 
v___x_1789_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_val_1765_, v_queue_1778_);
if (v_isShared_1788_ == 0)
{
lean_ctor_set(v___x_1787_, 11, v___x_1789_);
v___x_1791_ = v___x_1787_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_toRing_1767_);
lean_ctor_set(v_reuseFailAlloc_1792_, 1, v_invFn_x3f_1768_);
lean_ctor_set(v_reuseFailAlloc_1792_, 2, v_semiringId_x3f_1769_);
lean_ctor_set(v_reuseFailAlloc_1792_, 3, v_commSemiringInst_1770_);
lean_ctor_set(v_reuseFailAlloc_1792_, 4, v_commRingInst_1771_);
lean_ctor_set(v_reuseFailAlloc_1792_, 5, v_noZeroDivInst_x3f_1772_);
lean_ctor_set(v_reuseFailAlloc_1792_, 6, v_fieldInst_x3f_1773_);
lean_ctor_set(v_reuseFailAlloc_1792_, 7, v_powIdentityInst_x3f_1774_);
lean_ctor_set(v_reuseFailAlloc_1792_, 8, v_denoteEntries_1775_);
lean_ctor_set(v_reuseFailAlloc_1792_, 9, v_nextId_1776_);
lean_ctor_set(v_reuseFailAlloc_1792_, 10, v_steps_1777_);
lean_ctor_set(v_reuseFailAlloc_1792_, 11, v___x_1789_);
lean_ctor_set(v_reuseFailAlloc_1792_, 12, v_basis_1779_);
lean_ctor_set(v_reuseFailAlloc_1792_, 13, v_diseqs_1780_);
lean_ctor_set(v_reuseFailAlloc_1792_, 14, v_invSet_1782_);
lean_ctor_set(v_reuseFailAlloc_1792_, 15, v_powIdentityVarCount_1783_);
lean_ctor_set(v_reuseFailAlloc_1792_, 16, v_numEq0_x3f_1784_);
lean_ctor_set_uint8(v_reuseFailAlloc_1792_, sizeof(void*)*17, v_recheck_1781_);
lean_ctor_set_uint8(v_reuseFailAlloc_1792_, sizeof(void*)*17 + 1, v_numEq0Updated_1785_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___lam__0___boxed(lean_object* v_val_1794_, lean_object* v_s_1795_){
_start:
{
lean_object* v_res_1796_; 
v_res_1796_ = l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___lam__0(v_val_1794_, v_s_1795_);
lean_dec_ref(v_val_1794_);
return v_res_1796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f(lean_object* v_a_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_){
_start:
{
lean_object* v___x_1809_; 
v___x_1809_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_, v_a_1805_, v_a_1806_, v_a_1807_);
if (lean_obj_tag(v___x_1809_) == 0)
{
lean_object* v_a_1810_; lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1849_; 
v_a_1810_ = lean_ctor_get(v___x_1809_, 0);
v_isSharedCheck_1849_ = !lean_is_exclusive(v___x_1809_);
if (v_isSharedCheck_1849_ == 0)
{
v___x_1812_ = v___x_1809_;
v_isShared_1813_ = v_isSharedCheck_1849_;
goto v_resetjp_1811_;
}
else
{
lean_inc(v_a_1810_);
lean_dec(v___x_1809_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1849_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
lean_object* v_queue_1814_; lean_object* v___x_1815_; 
v_queue_1814_ = lean_ctor_get(v_a_1810_, 11);
lean_inc(v_queue_1814_);
lean_dec(v_a_1810_);
v___x_1815_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_queue_1814_);
lean_dec(v_queue_1814_);
if (lean_obj_tag(v___x_1815_) == 1)
{
lean_object* v_val_1816_; lean_object* v___f_1817_; lean_object* v___x_1818_; 
lean_del_object(v___x_1812_);
v_val_1816_ = lean_ctor_get(v___x_1815_, 0);
lean_inc(v_val_1816_);
v___f_1817_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1817_, 0, v_val_1816_);
v___x_1818_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_1817_, v_a_1797_, v_a_1798_);
if (lean_obj_tag(v___x_1818_) == 0)
{
lean_object* v___x_1819_; lean_object* v___x_1820_; 
lean_dec_ref(v___x_1818_);
v___x_1819_ = lean_unsigned_to_nat(1u);
v___x_1820_ = l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg(v___x_1819_, v_a_1798_);
if (lean_obj_tag(v___x_1820_) == 0)
{
lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1827_; 
v_isSharedCheck_1827_ = !lean_is_exclusive(v___x_1820_);
if (v_isSharedCheck_1827_ == 0)
{
lean_object* v_unused_1828_; 
v_unused_1828_ = lean_ctor_get(v___x_1820_, 0);
lean_dec(v_unused_1828_);
v___x_1822_ = v___x_1820_;
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
else
{
lean_dec(v___x_1820_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v___x_1825_; 
if (v_isShared_1823_ == 0)
{
lean_ctor_set(v___x_1822_, 0, v___x_1815_);
v___x_1825_ = v___x_1822_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v___x_1815_);
v___x_1825_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
return v___x_1825_;
}
}
}
else
{
lean_object* v_a_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1836_; 
lean_dec_ref(v___x_1815_);
v_a_1829_ = lean_ctor_get(v___x_1820_, 0);
v_isSharedCheck_1836_ = !lean_is_exclusive(v___x_1820_);
if (v_isSharedCheck_1836_ == 0)
{
v___x_1831_ = v___x_1820_;
v_isShared_1832_ = v_isSharedCheck_1836_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_a_1829_);
lean_dec(v___x_1820_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1836_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v___x_1834_; 
if (v_isShared_1832_ == 0)
{
v___x_1834_ = v___x_1831_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v_a_1829_);
v___x_1834_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
return v___x_1834_;
}
}
}
}
else
{
lean_object* v_a_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1844_; 
lean_dec_ref(v___x_1815_);
v_a_1837_ = lean_ctor_get(v___x_1818_, 0);
v_isSharedCheck_1844_ = !lean_is_exclusive(v___x_1818_);
if (v_isSharedCheck_1844_ == 0)
{
v___x_1839_ = v___x_1818_;
v_isShared_1840_ = v_isSharedCheck_1844_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_a_1837_);
lean_dec(v___x_1818_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1844_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
lean_object* v___x_1842_; 
if (v_isShared_1840_ == 0)
{
v___x_1842_ = v___x_1839_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v_a_1837_);
v___x_1842_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
return v___x_1842_;
}
}
}
}
else
{
lean_object* v___x_1845_; lean_object* v___x_1847_; 
lean_dec(v___x_1815_);
v___x_1845_ = lean_box(0);
if (v_isShared_1813_ == 0)
{
lean_ctor_set(v___x_1812_, 0, v___x_1845_);
v___x_1847_ = v___x_1812_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v___x_1845_);
v___x_1847_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
return v___x_1847_;
}
}
}
}
else
{
lean_object* v_a_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1857_; 
v_a_1850_ = lean_ctor_get(v___x_1809_, 0);
v_isSharedCheck_1857_ = !lean_is_exclusive(v___x_1809_);
if (v_isSharedCheck_1857_ == 0)
{
v___x_1852_ = v___x_1809_;
v_isShared_1853_ = v_isSharedCheck_1857_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_a_1850_);
lean_dec(v___x_1809_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1857_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v___x_1855_; 
if (v_isShared_1853_ == 0)
{
v___x_1855_ = v___x_1852_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v_a_1850_);
v___x_1855_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
return v___x_1855_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___boxed(lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_){
_start:
{
lean_object* v_res_1870_; 
v_res_1870_ = l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f(v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_, v_a_1864_, v_a_1865_, v_a_1866_, v_a_1867_, v_a_1868_);
lean_dec(v_a_1868_);
lean_dec_ref(v_a_1867_);
lean_dec(v_a_1866_);
lean_dec_ref(v_a_1865_);
lean_dec(v_a_1864_);
lean_dec_ref(v_a_1863_);
lean_dec(v_a_1862_);
lean_dec_ref(v_a_1861_);
lean_dec(v_a_1860_);
lean_dec(v_a_1859_);
lean_dec_ref(v_a_1858_);
return v_res_1870_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0(lean_object* v_00_u03b2_1871_, lean_object* v_k_1872_, lean_object* v_t_1873_, lean_object* v_h_1874_){
_start:
{
lean_object* v___x_1875_; 
v___x_1875_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_k_1872_, v_t_1873_);
return v___x_1875_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___boxed(lean_object* v_00_u03b2_1876_, lean_object* v_k_1877_, lean_object* v_t_1878_, lean_object* v_h_1879_){
_start:
{
lean_object* v_res_1880_; 
v_res_1880_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0(v_00_u03b2_1876_, v_k_1877_, v_t_1878_, v_h_1879_);
lean_dec_ref(v_k_1877_);
return v_res_1880_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_1881_, lean_object* v_x_1882_, lean_object* v_x_1883_, lean_object* v_x_1884_){
_start:
{
lean_object* v_ks_1885_; lean_object* v_vs_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1910_; 
v_ks_1885_ = lean_ctor_get(v_x_1881_, 0);
v_vs_1886_ = lean_ctor_get(v_x_1881_, 1);
v_isSharedCheck_1910_ = !lean_is_exclusive(v_x_1881_);
if (v_isSharedCheck_1910_ == 0)
{
v___x_1888_ = v_x_1881_;
v_isShared_1889_ = v_isSharedCheck_1910_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_vs_1886_);
lean_inc(v_ks_1885_);
lean_dec(v_x_1881_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1910_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v___x_1890_; uint8_t v___x_1891_; 
v___x_1890_ = lean_array_get_size(v_ks_1885_);
v___x_1891_ = lean_nat_dec_lt(v_x_1882_, v___x_1890_);
if (v___x_1891_ == 0)
{
lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1895_; 
lean_dec(v_x_1882_);
v___x_1892_ = lean_array_push(v_ks_1885_, v_x_1883_);
v___x_1893_ = lean_array_push(v_vs_1886_, v_x_1884_);
if (v_isShared_1889_ == 0)
{
lean_ctor_set(v___x_1888_, 1, v___x_1893_);
lean_ctor_set(v___x_1888_, 0, v___x_1892_);
v___x_1895_ = v___x_1888_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v___x_1892_);
lean_ctor_set(v_reuseFailAlloc_1896_, 1, v___x_1893_);
v___x_1895_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
return v___x_1895_;
}
}
else
{
lean_object* v_k_x27_1897_; uint8_t v___x_1898_; 
v_k_x27_1897_ = lean_array_fget_borrowed(v_ks_1885_, v_x_1882_);
v___x_1898_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_1883_, v_k_x27_1897_);
if (v___x_1898_ == 0)
{
lean_object* v___x_1900_; 
if (v_isShared_1889_ == 0)
{
v___x_1900_ = v___x_1888_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_ks_1885_);
lean_ctor_set(v_reuseFailAlloc_1904_, 1, v_vs_1886_);
v___x_1900_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
lean_object* v___x_1901_; lean_object* v___x_1902_; 
v___x_1901_ = lean_unsigned_to_nat(1u);
v___x_1902_ = lean_nat_add(v_x_1882_, v___x_1901_);
lean_dec(v_x_1882_);
v_x_1881_ = v___x_1900_;
v_x_1882_ = v___x_1902_;
goto _start;
}
}
else
{
lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1908_; 
v___x_1905_ = lean_array_fset(v_ks_1885_, v_x_1882_, v_x_1883_);
v___x_1906_ = lean_array_fset(v_vs_1886_, v_x_1882_, v_x_1884_);
lean_dec(v_x_1882_);
if (v_isShared_1889_ == 0)
{
lean_ctor_set(v___x_1888_, 1, v___x_1906_);
lean_ctor_set(v___x_1888_, 0, v___x_1905_);
v___x_1908_ = v___x_1888_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v___x_1905_);
lean_ctor_set(v_reuseFailAlloc_1909_, 1, v___x_1906_);
v___x_1908_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
return v___x_1908_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1___redArg(lean_object* v_n_1911_, lean_object* v_k_1912_, lean_object* v_v_1913_){
_start:
{
lean_object* v___x_1914_; lean_object* v___x_1915_; 
v___x_1914_ = lean_unsigned_to_nat(0u);
v___x_1915_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1911_, v___x_1914_, v_k_1912_, v_v_1913_);
return v___x_1915_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1916_; 
v___x_1916_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1916_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(lean_object* v_x_1917_, size_t v_x_1918_, size_t v_x_1919_, lean_object* v_x_1920_, lean_object* v_x_1921_){
_start:
{
if (lean_obj_tag(v_x_1917_) == 0)
{
lean_object* v_es_1922_; size_t v___x_1923_; size_t v___x_1924_; size_t v___x_1925_; size_t v___x_1926_; lean_object* v_j_1927_; lean_object* v___x_1928_; uint8_t v___x_1929_; 
v_es_1922_ = lean_ctor_get(v_x_1917_, 0);
v___x_1923_ = ((size_t)5ULL);
v___x_1924_ = ((size_t)1ULL);
v___x_1925_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__1);
v___x_1926_ = lean_usize_land(v_x_1918_, v___x_1925_);
v_j_1927_ = lean_usize_to_nat(v___x_1926_);
v___x_1928_ = lean_array_get_size(v_es_1922_);
v___x_1929_ = lean_nat_dec_lt(v_j_1927_, v___x_1928_);
if (v___x_1929_ == 0)
{
lean_dec(v_j_1927_);
lean_dec(v_x_1921_);
lean_dec_ref(v_x_1920_);
return v_x_1917_;
}
else
{
lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1966_; 
lean_inc_ref(v_es_1922_);
v_isSharedCheck_1966_ = !lean_is_exclusive(v_x_1917_);
if (v_isSharedCheck_1966_ == 0)
{
lean_object* v_unused_1967_; 
v_unused_1967_ = lean_ctor_get(v_x_1917_, 0);
lean_dec(v_unused_1967_);
v___x_1931_ = v_x_1917_;
v_isShared_1932_ = v_isSharedCheck_1966_;
goto v_resetjp_1930_;
}
else
{
lean_dec(v_x_1917_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1966_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v_v_1933_; lean_object* v___x_1934_; lean_object* v_xs_x27_1935_; lean_object* v___y_1937_; 
v_v_1933_ = lean_array_fget(v_es_1922_, v_j_1927_);
v___x_1934_ = lean_box(0);
v_xs_x27_1935_ = lean_array_fset(v_es_1922_, v_j_1927_, v___x_1934_);
switch(lean_obj_tag(v_v_1933_))
{
case 0:
{
lean_object* v_key_1942_; lean_object* v_val_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1953_; 
v_key_1942_ = lean_ctor_get(v_v_1933_, 0);
v_val_1943_ = lean_ctor_get(v_v_1933_, 1);
v_isSharedCheck_1953_ = !lean_is_exclusive(v_v_1933_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1945_ = v_v_1933_;
v_isShared_1946_ = v_isSharedCheck_1953_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_val_1943_);
lean_inc(v_key_1942_);
lean_dec(v_v_1933_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1953_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
uint8_t v___x_1947_; 
v___x_1947_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_1920_, v_key_1942_);
if (v___x_1947_ == 0)
{
lean_object* v___x_1948_; lean_object* v___x_1949_; 
lean_del_object(v___x_1945_);
v___x_1948_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1942_, v_val_1943_, v_x_1920_, v_x_1921_);
v___x_1949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1949_, 0, v___x_1948_);
v___y_1937_ = v___x_1949_;
goto v___jp_1936_;
}
else
{
lean_object* v___x_1951_; 
lean_dec(v_val_1943_);
lean_dec(v_key_1942_);
if (v_isShared_1946_ == 0)
{
lean_ctor_set(v___x_1945_, 1, v_x_1921_);
lean_ctor_set(v___x_1945_, 0, v_x_1920_);
v___x_1951_ = v___x_1945_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v_x_1920_);
lean_ctor_set(v_reuseFailAlloc_1952_, 1, v_x_1921_);
v___x_1951_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
v___y_1937_ = v___x_1951_;
goto v___jp_1936_;
}
}
}
}
case 1:
{
lean_object* v_node_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1964_; 
v_node_1954_ = lean_ctor_get(v_v_1933_, 0);
v_isSharedCheck_1964_ = !lean_is_exclusive(v_v_1933_);
if (v_isSharedCheck_1964_ == 0)
{
v___x_1956_ = v_v_1933_;
v_isShared_1957_ = v_isSharedCheck_1964_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_node_1954_);
lean_dec(v_v_1933_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1964_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
size_t v___x_1958_; size_t v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1962_; 
v___x_1958_ = lean_usize_shift_right(v_x_1918_, v___x_1923_);
v___x_1959_ = lean_usize_add(v_x_1919_, v___x_1924_);
v___x_1960_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_node_1954_, v___x_1958_, v___x_1959_, v_x_1920_, v_x_1921_);
if (v_isShared_1957_ == 0)
{
lean_ctor_set(v___x_1956_, 0, v___x_1960_);
v___x_1962_ = v___x_1956_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v___x_1960_);
v___x_1962_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
v___y_1937_ = v___x_1962_;
goto v___jp_1936_;
}
}
}
default: 
{
lean_object* v___x_1965_; 
v___x_1965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1965_, 0, v_x_1920_);
lean_ctor_set(v___x_1965_, 1, v_x_1921_);
v___y_1937_ = v___x_1965_;
goto v___jp_1936_;
}
}
v___jp_1936_:
{
lean_object* v___x_1938_; lean_object* v___x_1940_; 
v___x_1938_ = lean_array_fset(v_xs_x27_1935_, v_j_1927_, v___y_1937_);
lean_dec(v_j_1927_);
if (v_isShared_1932_ == 0)
{
lean_ctor_set(v___x_1931_, 0, v___x_1938_);
v___x_1940_ = v___x_1931_;
goto v_reusejp_1939_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v___x_1938_);
v___x_1940_ = v_reuseFailAlloc_1941_;
goto v_reusejp_1939_;
}
v_reusejp_1939_:
{
return v___x_1940_;
}
}
}
}
}
else
{
lean_object* v_ks_1968_; lean_object* v_vs_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_1989_; 
v_ks_1968_ = lean_ctor_get(v_x_1917_, 0);
v_vs_1969_ = lean_ctor_get(v_x_1917_, 1);
v_isSharedCheck_1989_ = !lean_is_exclusive(v_x_1917_);
if (v_isSharedCheck_1989_ == 0)
{
v___x_1971_ = v_x_1917_;
v_isShared_1972_ = v_isSharedCheck_1989_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_vs_1969_);
lean_inc(v_ks_1968_);
lean_dec(v_x_1917_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_1989_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
lean_object* v___x_1974_; 
if (v_isShared_1972_ == 0)
{
v___x_1974_ = v___x_1971_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v_ks_1968_);
lean_ctor_set(v_reuseFailAlloc_1988_, 1, v_vs_1969_);
v___x_1974_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1973_;
}
v_reusejp_1973_:
{
lean_object* v_newNode_1975_; uint8_t v___y_1977_; size_t v___x_1983_; uint8_t v___x_1984_; 
v_newNode_1975_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1___redArg(v___x_1974_, v_x_1920_, v_x_1921_);
v___x_1983_ = ((size_t)7ULL);
v___x_1984_ = lean_usize_dec_le(v___x_1983_, v_x_1919_);
if (v___x_1984_ == 0)
{
lean_object* v___x_1985_; lean_object* v___x_1986_; uint8_t v___x_1987_; 
v___x_1985_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1975_);
v___x_1986_ = lean_unsigned_to_nat(4u);
v___x_1987_ = lean_nat_dec_lt(v___x_1985_, v___x_1986_);
lean_dec(v___x_1985_);
v___y_1977_ = v___x_1987_;
goto v___jp_1976_;
}
else
{
v___y_1977_ = v___x_1984_;
goto v___jp_1976_;
}
v___jp_1976_:
{
if (v___y_1977_ == 0)
{
lean_object* v_ks_1978_; lean_object* v_vs_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; 
v_ks_1978_ = lean_ctor_get(v_newNode_1975_, 0);
lean_inc_ref(v_ks_1978_);
v_vs_1979_ = lean_ctor_get(v_newNode_1975_, 1);
lean_inc_ref(v_vs_1979_);
lean_dec_ref(v_newNode_1975_);
v___x_1980_ = lean_unsigned_to_nat(0u);
v___x_1981_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0);
v___x_1982_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg(v_x_1919_, v_ks_1978_, v_vs_1979_, v___x_1980_, v___x_1981_);
lean_dec_ref(v_vs_1979_);
lean_dec_ref(v_ks_1978_);
return v___x_1982_;
}
else
{
return v_newNode_1975_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg(size_t v_depth_1990_, lean_object* v_keys_1991_, lean_object* v_vals_1992_, lean_object* v_i_1993_, lean_object* v_entries_1994_){
_start:
{
lean_object* v___x_1995_; uint8_t v___x_1996_; 
v___x_1995_ = lean_array_get_size(v_keys_1991_);
v___x_1996_ = lean_nat_dec_lt(v_i_1993_, v___x_1995_);
if (v___x_1996_ == 0)
{
lean_dec(v_i_1993_);
return v_entries_1994_;
}
else
{
lean_object* v_k_1997_; lean_object* v_v_1998_; uint64_t v___x_1999_; size_t v_h_2000_; size_t v___x_2001_; lean_object* v___x_2002_; size_t v___x_2003_; size_t v___x_2004_; size_t v___x_2005_; size_t v_h_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; 
v_k_1997_ = lean_array_fget_borrowed(v_keys_1991_, v_i_1993_);
v_v_1998_ = lean_array_fget_borrowed(v_vals_1992_, v_i_1993_);
v___x_1999_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_1997_);
v_h_2000_ = lean_uint64_to_usize(v___x_1999_);
v___x_2001_ = ((size_t)5ULL);
v___x_2002_ = lean_unsigned_to_nat(1u);
v___x_2003_ = ((size_t)1ULL);
v___x_2004_ = lean_usize_sub(v_depth_1990_, v___x_2003_);
v___x_2005_ = lean_usize_mul(v___x_2001_, v___x_2004_);
v_h_2006_ = lean_usize_shift_right(v_h_2000_, v___x_2005_);
v___x_2007_ = lean_nat_add(v_i_1993_, v___x_2002_);
lean_dec(v_i_1993_);
lean_inc(v_v_1998_);
lean_inc(v_k_1997_);
v___x_2008_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_entries_1994_, v_h_2006_, v_depth_1990_, v_k_1997_, v_v_1998_);
v_i_1993_ = v___x_2007_;
v_entries_1994_ = v___x_2008_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_2010_, lean_object* v_keys_2011_, lean_object* v_vals_2012_, lean_object* v_i_2013_, lean_object* v_entries_2014_){
_start:
{
size_t v_depth_boxed_2015_; lean_object* v_res_2016_; 
v_depth_boxed_2015_ = lean_unbox_usize(v_depth_2010_);
lean_dec(v_depth_2010_);
v_res_2016_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg(v_depth_boxed_2015_, v_keys_2011_, v_vals_2012_, v_i_2013_, v_entries_2014_);
lean_dec_ref(v_vals_2012_);
lean_dec_ref(v_keys_2011_);
return v_res_2016_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___boxed(lean_object* v_x_2017_, lean_object* v_x_2018_, lean_object* v_x_2019_, lean_object* v_x_2020_, lean_object* v_x_2021_){
_start:
{
size_t v_x_7187__boxed_2022_; size_t v_x_7188__boxed_2023_; lean_object* v_res_2024_; 
v_x_7187__boxed_2022_ = lean_unbox_usize(v_x_2018_);
lean_dec(v_x_2018_);
v_x_7188__boxed_2023_ = lean_unbox_usize(v_x_2019_);
lean_dec(v_x_2019_);
v_res_2024_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_x_2017_, v_x_7187__boxed_2022_, v_x_7188__boxed_2023_, v_x_2020_, v_x_2021_);
return v_res_2024_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0___redArg(lean_object* v_x_2025_, lean_object* v_x_2026_, lean_object* v_x_2027_){
_start:
{
uint64_t v___x_2028_; size_t v___x_2029_; size_t v___x_2030_; lean_object* v___x_2031_; 
v___x_2028_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_2026_);
v___x_2029_ = lean_uint64_to_usize(v___x_2028_);
v___x_2030_ = ((size_t)1ULL);
v___x_2031_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_x_2025_, v___x_2029_, v___x_2030_, v_x_2026_, v_x_2027_);
return v___x_2031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___lam__0(lean_object* v_e_2032_, lean_object* v_ringId_2033_, lean_object* v_s_2034_){
_start:
{
lean_object* v_rings_2035_; lean_object* v_typeIdOf_2036_; lean_object* v_exprToRingId_2037_; lean_object* v_semirings_2038_; lean_object* v_stypeIdOf_2039_; lean_object* v_exprToSemiringId_2040_; lean_object* v_ncRings_2041_; lean_object* v_exprToNCRingId_2042_; lean_object* v_nctypeIdOf_2043_; lean_object* v_ncSemirings_2044_; lean_object* v_exprToNCSemiringId_2045_; lean_object* v_ncstypeIdOf_2046_; lean_object* v_steps_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2055_; 
v_rings_2035_ = lean_ctor_get(v_s_2034_, 0);
v_typeIdOf_2036_ = lean_ctor_get(v_s_2034_, 1);
v_exprToRingId_2037_ = lean_ctor_get(v_s_2034_, 2);
v_semirings_2038_ = lean_ctor_get(v_s_2034_, 3);
v_stypeIdOf_2039_ = lean_ctor_get(v_s_2034_, 4);
v_exprToSemiringId_2040_ = lean_ctor_get(v_s_2034_, 5);
v_ncRings_2041_ = lean_ctor_get(v_s_2034_, 6);
v_exprToNCRingId_2042_ = lean_ctor_get(v_s_2034_, 7);
v_nctypeIdOf_2043_ = lean_ctor_get(v_s_2034_, 8);
v_ncSemirings_2044_ = lean_ctor_get(v_s_2034_, 9);
v_exprToNCSemiringId_2045_ = lean_ctor_get(v_s_2034_, 10);
v_ncstypeIdOf_2046_ = lean_ctor_get(v_s_2034_, 11);
v_steps_2047_ = lean_ctor_get(v_s_2034_, 12);
v_isSharedCheck_2055_ = !lean_is_exclusive(v_s_2034_);
if (v_isSharedCheck_2055_ == 0)
{
v___x_2049_ = v_s_2034_;
v_isShared_2050_ = v_isSharedCheck_2055_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_steps_2047_);
lean_inc(v_ncstypeIdOf_2046_);
lean_inc(v_exprToNCSemiringId_2045_);
lean_inc(v_ncSemirings_2044_);
lean_inc(v_nctypeIdOf_2043_);
lean_inc(v_exprToNCRingId_2042_);
lean_inc(v_ncRings_2041_);
lean_inc(v_exprToSemiringId_2040_);
lean_inc(v_stypeIdOf_2039_);
lean_inc(v_semirings_2038_);
lean_inc(v_exprToRingId_2037_);
lean_inc(v_typeIdOf_2036_);
lean_inc(v_rings_2035_);
lean_dec(v_s_2034_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2055_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v___x_2051_; lean_object* v___x_2053_; 
v___x_2051_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0___redArg(v_exprToRingId_2037_, v_e_2032_, v_ringId_2033_);
if (v_isShared_2050_ == 0)
{
lean_ctor_set(v___x_2049_, 2, v___x_2051_);
v___x_2053_ = v___x_2049_;
goto v_reusejp_2052_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v_rings_2035_);
lean_ctor_set(v_reuseFailAlloc_2054_, 1, v_typeIdOf_2036_);
lean_ctor_set(v_reuseFailAlloc_2054_, 2, v___x_2051_);
lean_ctor_set(v_reuseFailAlloc_2054_, 3, v_semirings_2038_);
lean_ctor_set(v_reuseFailAlloc_2054_, 4, v_stypeIdOf_2039_);
lean_ctor_set(v_reuseFailAlloc_2054_, 5, v_exprToSemiringId_2040_);
lean_ctor_set(v_reuseFailAlloc_2054_, 6, v_ncRings_2041_);
lean_ctor_set(v_reuseFailAlloc_2054_, 7, v_exprToNCRingId_2042_);
lean_ctor_set(v_reuseFailAlloc_2054_, 8, v_nctypeIdOf_2043_);
lean_ctor_set(v_reuseFailAlloc_2054_, 9, v_ncSemirings_2044_);
lean_ctor_set(v_reuseFailAlloc_2054_, 10, v_exprToNCSemiringId_2045_);
lean_ctor_set(v_reuseFailAlloc_2054_, 11, v_ncstypeIdOf_2046_);
lean_ctor_set(v_reuseFailAlloc_2054_, 12, v_steps_2047_);
v___x_2053_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2052_;
}
v_reusejp_2052_:
{
return v___x_2053_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__1(void){
_start:
{
lean_object* v___x_2057_; lean_object* v___x_2058_; 
v___x_2057_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__0));
v___x_2058_ = l_Lean_stringToMessageData(v___x_2057_);
return v___x_2058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(lean_object* v_e_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_){
_start:
{
lean_object* v___x_2072_; 
v___x_2072_ = l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg(v_e_2059_, v_a_2061_, v_a_2066_);
if (lean_obj_tag(v___x_2072_) == 0)
{
lean_object* v_a_2073_; 
v_a_2073_ = lean_ctor_get(v___x_2072_, 0);
lean_inc(v_a_2073_);
lean_dec_ref(v___x_2072_);
if (lean_obj_tag(v_a_2073_) == 1)
{
lean_object* v_ringId_2074_; lean_object* v_val_2075_; uint8_t v___x_2076_; 
v_ringId_2074_ = lean_ctor_get(v_a_2060_, 0);
v_val_2075_ = lean_ctor_get(v_a_2073_, 0);
lean_inc(v_val_2075_);
lean_dec_ref(v_a_2073_);
v___x_2076_ = lean_nat_dec_eq(v_val_2075_, v_ringId_2074_);
lean_dec(v_val_2075_);
if (v___x_2076_ == 0)
{
lean_object* v___x_2077_; 
v___x_2077_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_2062_);
if (lean_obj_tag(v___x_2077_) == 0)
{
lean_object* v_a_2078_; uint8_t v___x_2079_; 
v_a_2078_ = lean_ctor_get(v___x_2077_, 0);
lean_inc(v_a_2078_);
lean_dec_ref(v___x_2077_);
v___x_2079_ = lean_unbox(v_a_2078_);
lean_dec(v_a_2078_);
if (v___x_2079_ == 0)
{
lean_dec_ref(v_e_2059_);
goto v___jp_2069_;
}
else
{
lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; 
v___x_2080_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__1);
v___x_2081_ = l_Lean_indentExpr(v_e_2059_);
v___x_2082_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2082_, 0, v___x_2080_);
lean_ctor_set(v___x_2082_, 1, v___x_2081_);
v___x_2083_ = l_Lean_Meta_Sym_reportIssue(v___x_2082_, v_a_2062_, v_a_2063_, v_a_2064_, v_a_2065_, v_a_2066_, v_a_2067_);
if (lean_obj_tag(v___x_2083_) == 0)
{
lean_dec_ref(v___x_2083_);
goto v___jp_2069_;
}
else
{
return v___x_2083_;
}
}
}
else
{
lean_object* v_a_2084_; lean_object* v___x_2086_; uint8_t v_isShared_2087_; uint8_t v_isSharedCheck_2091_; 
lean_dec_ref(v_e_2059_);
v_a_2084_ = lean_ctor_get(v___x_2077_, 0);
v_isSharedCheck_2091_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2091_ == 0)
{
v___x_2086_ = v___x_2077_;
v_isShared_2087_ = v_isSharedCheck_2091_;
goto v_resetjp_2085_;
}
else
{
lean_inc(v_a_2084_);
lean_dec(v___x_2077_);
v___x_2086_ = lean_box(0);
v_isShared_2087_ = v_isSharedCheck_2091_;
goto v_resetjp_2085_;
}
v_resetjp_2085_:
{
lean_object* v___x_2089_; 
if (v_isShared_2087_ == 0)
{
v___x_2089_ = v___x_2086_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v_a_2084_);
v___x_2089_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
return v___x_2089_;
}
}
}
}
else
{
lean_dec_ref(v_e_2059_);
goto v___jp_2069_;
}
}
else
{
lean_object* v_ringId_2092_; lean_object* v___f_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; 
lean_dec(v_a_2073_);
v_ringId_2092_ = lean_ctor_get(v_a_2060_, 0);
lean_inc(v_ringId_2092_);
v___f_2093_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2093_, 0, v_e_2059_);
lean_closure_set(v___f_2093_, 1, v_ringId_2092_);
v___x_2094_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_2095_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2094_, v___f_2093_, v_a_2061_);
return v___x_2095_;
}
}
else
{
lean_object* v_a_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2103_; 
lean_dec_ref(v_e_2059_);
v_a_2096_ = lean_ctor_get(v___x_2072_, 0);
v_isSharedCheck_2103_ = !lean_is_exclusive(v___x_2072_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_2098_ = v___x_2072_;
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_a_2096_);
lean_dec(v___x_2072_);
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
v___jp_2069_:
{
lean_object* v___x_2070_; lean_object* v___x_2071_; 
v___x_2070_ = lean_box(0);
v___x_2071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2070_);
return v___x_2071_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___boxed(lean_object* v_e_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_){
_start:
{
lean_object* v_res_2114_; 
v_res_2114_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(v_e_2104_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_, v_a_2109_, v_a_2110_, v_a_2111_, v_a_2112_);
lean_dec(v_a_2112_);
lean_dec_ref(v_a_2111_);
lean_dec(v_a_2110_);
lean_dec_ref(v_a_2109_);
lean_dec(v_a_2108_);
lean_dec_ref(v_a_2107_);
lean_dec(v_a_2106_);
lean_dec_ref(v_a_2105_);
return v_res_2114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId(lean_object* v_e_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_){
_start:
{
lean_object* v___x_2128_; 
v___x_2128_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(v_e_2115_, v_a_2116_, v_a_2117_, v_a_2121_, v_a_2122_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_);
return v___x_2128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___boxed(lean_object* v_e_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_){
_start:
{
lean_object* v_res_2142_; 
v_res_2142_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId(v_e_2129_, v_a_2130_, v_a_2131_, v_a_2132_, v_a_2133_, v_a_2134_, v_a_2135_, v_a_2136_, v_a_2137_, v_a_2138_, v_a_2139_, v_a_2140_);
lean_dec(v_a_2140_);
lean_dec_ref(v_a_2139_);
lean_dec(v_a_2138_);
lean_dec_ref(v_a_2137_);
lean_dec(v_a_2136_);
lean_dec_ref(v_a_2135_);
lean_dec(v_a_2134_);
lean_dec_ref(v_a_2133_);
lean_dec(v_a_2132_);
lean_dec(v_a_2131_);
lean_dec_ref(v_a_2130_);
return v_res_2142_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0(lean_object* v_00_u03b2_2143_, lean_object* v_x_2144_, lean_object* v_x_2145_, lean_object* v_x_2146_){
_start:
{
lean_object* v___x_2147_; 
v___x_2147_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0___redArg(v_x_2144_, v_x_2145_, v_x_2146_);
return v___x_2147_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0(lean_object* v_00_u03b2_2148_, lean_object* v_x_2149_, size_t v_x_2150_, size_t v_x_2151_, lean_object* v_x_2152_, lean_object* v_x_2153_){
_start:
{
lean_object* v___x_2154_; 
v___x_2154_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_x_2149_, v_x_2150_, v_x_2151_, v_x_2152_, v_x_2153_);
return v___x_2154_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2155_, lean_object* v_x_2156_, lean_object* v_x_2157_, lean_object* v_x_2158_, lean_object* v_x_2159_, lean_object* v_x_2160_){
_start:
{
size_t v_x_7466__boxed_2161_; size_t v_x_7467__boxed_2162_; lean_object* v_res_2163_; 
v_x_7466__boxed_2161_ = lean_unbox_usize(v_x_2157_);
lean_dec(v_x_2157_);
v_x_7467__boxed_2162_ = lean_unbox_usize(v_x_2158_);
lean_dec(v_x_2158_);
v_res_2163_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0(v_00_u03b2_2155_, v_x_2156_, v_x_7466__boxed_2161_, v_x_7467__boxed_2162_, v_x_2159_, v_x_2160_);
return v_res_2163_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2164_, lean_object* v_n_2165_, lean_object* v_k_2166_, lean_object* v_v_2167_){
_start:
{
lean_object* v___x_2168_; 
v___x_2168_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1___redArg(v_n_2165_, v_k_2166_, v_v_2167_);
return v___x_2168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_2169_, size_t v_depth_2170_, lean_object* v_keys_2171_, lean_object* v_vals_2172_, lean_object* v_heq_2173_, lean_object* v_i_2174_, lean_object* v_entries_2175_){
_start:
{
lean_object* v___x_2176_; 
v___x_2176_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg(v_depth_2170_, v_keys_2171_, v_vals_2172_, v_i_2174_, v_entries_2175_);
return v___x_2176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2177_, lean_object* v_depth_2178_, lean_object* v_keys_2179_, lean_object* v_vals_2180_, lean_object* v_heq_2181_, lean_object* v_i_2182_, lean_object* v_entries_2183_){
_start:
{
size_t v_depth_boxed_2184_; lean_object* v_res_2185_; 
v_depth_boxed_2184_ = lean_unbox_usize(v_depth_2178_);
lean_dec(v_depth_2178_);
v_res_2185_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2(v_00_u03b2_2177_, v_depth_boxed_2184_, v_keys_2179_, v_vals_2180_, v_heq_2181_, v_i_2182_, v_entries_2183_);
lean_dec_ref(v_vals_2180_);
lean_dec_ref(v_keys_2179_);
return v_res_2185_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2186_, lean_object* v_x_2187_, lean_object* v_x_2188_, lean_object* v_x_2189_, lean_object* v_x_2190_){
_start:
{
lean_object* v___x_2191_; 
v___x_2191_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1_spec__2___redArg(v_x_2187_, v_x_2188_, v_x_2189_, v_x_2190_);
return v___x_2191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__0(lean_object* v_e_2192_, lean_object* v___f_2193_, lean_object* v___f_2194_, lean_object* v_size_2195_, lean_object* v_s_2196_){
_start:
{
lean_object* v_id_2197_; lean_object* v_type_2198_; lean_object* v_u_2199_; lean_object* v_ringInst_2200_; lean_object* v_semiringInst_2201_; lean_object* v_charInst_x3f_2202_; lean_object* v_addFn_x3f_2203_; lean_object* v_mulFn_x3f_2204_; lean_object* v_subFn_x3f_2205_; lean_object* v_negFn_x3f_2206_; lean_object* v_powFn_x3f_2207_; lean_object* v_intCastFn_x3f_2208_; lean_object* v_natCastFn_x3f_2209_; lean_object* v_one_x3f_2210_; lean_object* v_vars_2211_; lean_object* v_varMap_2212_; lean_object* v_denote_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2222_; 
v_id_2197_ = lean_ctor_get(v_s_2196_, 0);
v_type_2198_ = lean_ctor_get(v_s_2196_, 1);
v_u_2199_ = lean_ctor_get(v_s_2196_, 2);
v_ringInst_2200_ = lean_ctor_get(v_s_2196_, 3);
v_semiringInst_2201_ = lean_ctor_get(v_s_2196_, 4);
v_charInst_x3f_2202_ = lean_ctor_get(v_s_2196_, 5);
v_addFn_x3f_2203_ = lean_ctor_get(v_s_2196_, 6);
v_mulFn_x3f_2204_ = lean_ctor_get(v_s_2196_, 7);
v_subFn_x3f_2205_ = lean_ctor_get(v_s_2196_, 8);
v_negFn_x3f_2206_ = lean_ctor_get(v_s_2196_, 9);
v_powFn_x3f_2207_ = lean_ctor_get(v_s_2196_, 10);
v_intCastFn_x3f_2208_ = lean_ctor_get(v_s_2196_, 11);
v_natCastFn_x3f_2209_ = lean_ctor_get(v_s_2196_, 12);
v_one_x3f_2210_ = lean_ctor_get(v_s_2196_, 13);
v_vars_2211_ = lean_ctor_get(v_s_2196_, 14);
v_varMap_2212_ = lean_ctor_get(v_s_2196_, 15);
v_denote_2213_ = lean_ctor_get(v_s_2196_, 16);
v_isSharedCheck_2222_ = !lean_is_exclusive(v_s_2196_);
if (v_isSharedCheck_2222_ == 0)
{
v___x_2215_ = v_s_2196_;
v_isShared_2216_ = v_isSharedCheck_2222_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_denote_2213_);
lean_inc(v_varMap_2212_);
lean_inc(v_vars_2211_);
lean_inc(v_one_x3f_2210_);
lean_inc(v_natCastFn_x3f_2209_);
lean_inc(v_intCastFn_x3f_2208_);
lean_inc(v_powFn_x3f_2207_);
lean_inc(v_negFn_x3f_2206_);
lean_inc(v_subFn_x3f_2205_);
lean_inc(v_mulFn_x3f_2204_);
lean_inc(v_addFn_x3f_2203_);
lean_inc(v_charInst_x3f_2202_);
lean_inc(v_semiringInst_2201_);
lean_inc(v_ringInst_2200_);
lean_inc(v_u_2199_);
lean_inc(v_type_2198_);
lean_inc(v_id_2197_);
lean_dec(v_s_2196_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2222_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2220_; 
lean_inc_ref(v_e_2192_);
v___x_2217_ = l_Lean_PersistentArray_push___redArg(v_vars_2211_, v_e_2192_);
v___x_2218_ = l_Lean_PersistentHashMap_insert___redArg(v___f_2193_, v___f_2194_, v_varMap_2212_, v_e_2192_, v_size_2195_);
if (v_isShared_2216_ == 0)
{
lean_ctor_set(v___x_2215_, 15, v___x_2218_);
lean_ctor_set(v___x_2215_, 14, v___x_2217_);
v___x_2220_ = v___x_2215_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v_id_2197_);
lean_ctor_set(v_reuseFailAlloc_2221_, 1, v_type_2198_);
lean_ctor_set(v_reuseFailAlloc_2221_, 2, v_u_2199_);
lean_ctor_set(v_reuseFailAlloc_2221_, 3, v_ringInst_2200_);
lean_ctor_set(v_reuseFailAlloc_2221_, 4, v_semiringInst_2201_);
lean_ctor_set(v_reuseFailAlloc_2221_, 5, v_charInst_x3f_2202_);
lean_ctor_set(v_reuseFailAlloc_2221_, 6, v_addFn_x3f_2203_);
lean_ctor_set(v_reuseFailAlloc_2221_, 7, v_mulFn_x3f_2204_);
lean_ctor_set(v_reuseFailAlloc_2221_, 8, v_subFn_x3f_2205_);
lean_ctor_set(v_reuseFailAlloc_2221_, 9, v_negFn_x3f_2206_);
lean_ctor_set(v_reuseFailAlloc_2221_, 10, v_powFn_x3f_2207_);
lean_ctor_set(v_reuseFailAlloc_2221_, 11, v_intCastFn_x3f_2208_);
lean_ctor_set(v_reuseFailAlloc_2221_, 12, v_natCastFn_x3f_2209_);
lean_ctor_set(v_reuseFailAlloc_2221_, 13, v_one_x3f_2210_);
lean_ctor_set(v_reuseFailAlloc_2221_, 14, v___x_2217_);
lean_ctor_set(v_reuseFailAlloc_2221_, 15, v___x_2218_);
lean_ctor_set(v_reuseFailAlloc_2221_, 16, v_denote_2213_);
v___x_2220_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
return v___x_2220_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__1(lean_object* v_toPure_2223_, lean_object* v_size_2224_, lean_object* v_____r_2225_){
_start:
{
lean_object* v___x_2226_; 
v___x_2226_ = lean_apply_2(v_toPure_2223_, lean_box(0), v_size_2224_);
return v___x_2226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__2(lean_object* v_e_2227_, lean_object* v_inst_2228_, lean_object* v_toBind_2229_, lean_object* v___f_2230_, lean_object* v_____r_2231_){
_start:
{
lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; 
v___x_2232_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_2233_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_SolverExtension_markTerm___boxed), 14, 3);
lean_closure_set(v___x_2233_, 0, lean_box(0));
lean_closure_set(v___x_2233_, 1, v___x_2232_);
lean_closure_set(v___x_2233_, 2, v_e_2227_);
v___x_2234_ = lean_apply_2(v_inst_2228_, lean_box(0), v___x_2233_);
v___x_2235_ = lean_apply_4(v_toBind_2229_, lean_box(0), lean_box(0), v___x_2234_, v___f_2230_);
return v___x_2235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__3(lean_object* v_inst_2236_, lean_object* v_e_2237_, lean_object* v_toBind_2238_, lean_object* v___f_2239_, lean_object* v_____r_2240_){
_start:
{
lean_object* v___x_2241_; lean_object* v___x_2242_; 
v___x_2241_ = lean_apply_1(v_inst_2236_, v_e_2237_);
v___x_2242_ = lean_apply_4(v_toBind_2238_, lean_box(0), lean_box(0), v___x_2241_, v___f_2239_);
return v___x_2242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__4(lean_object* v___f_2243_, lean_object* v___f_2244_, lean_object* v_e_2245_, lean_object* v_toPure_2246_, lean_object* v_inst_2247_, lean_object* v_toBind_2248_, lean_object* v_inst_2249_, lean_object* v_modifyRing_2250_, lean_object* v_s_2251_){
_start:
{
lean_object* v_vars_2252_; lean_object* v_varMap_2253_; lean_object* v___x_2254_; 
v_vars_2252_ = lean_ctor_get(v_s_2251_, 14);
lean_inc_ref(v_vars_2252_);
v_varMap_2253_ = lean_ctor_get(v_s_2251_, 15);
lean_inc_ref(v_varMap_2253_);
lean_dec_ref(v_s_2251_);
lean_inc_ref(v_e_2245_);
lean_inc_ref(v___f_2244_);
lean_inc_ref(v___f_2243_);
v___x_2254_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_2243_, v___f_2244_, v_varMap_2253_, v_e_2245_);
lean_dec_ref(v_varMap_2253_);
if (lean_obj_tag(v___x_2254_) == 1)
{
lean_object* v_val_2255_; lean_object* v___x_2256_; 
lean_dec_ref(v_vars_2252_);
lean_dec(v_modifyRing_2250_);
lean_dec(v_inst_2249_);
lean_dec(v_toBind_2248_);
lean_dec(v_inst_2247_);
lean_dec_ref(v_e_2245_);
lean_dec_ref(v___f_2244_);
lean_dec_ref(v___f_2243_);
v_val_2255_ = lean_ctor_get(v___x_2254_, 0);
lean_inc(v_val_2255_);
lean_dec_ref(v___x_2254_);
v___x_2256_ = lean_apply_2(v_toPure_2246_, lean_box(0), v_val_2255_);
return v___x_2256_;
}
else
{
lean_object* v_size_2257_; lean_object* v___f_2258_; lean_object* v___f_2259_; lean_object* v___f_2260_; lean_object* v___f_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; 
lean_dec(v___x_2254_);
v_size_2257_ = lean_ctor_get(v_vars_2252_, 2);
lean_inc_n(v_size_2257_, 2);
lean_dec_ref(v_vars_2252_);
lean_inc_ref_n(v_e_2245_, 2);
v___f_2258_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2258_, 0, v_e_2245_);
lean_closure_set(v___f_2258_, 1, v___f_2243_);
lean_closure_set(v___f_2258_, 2, v___f_2244_);
lean_closure_set(v___f_2258_, 3, v_size_2257_);
v___f_2259_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2259_, 0, v_toPure_2246_);
lean_closure_set(v___f_2259_, 1, v_size_2257_);
lean_inc_n(v_toBind_2248_, 2);
v___f_2260_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2260_, 0, v_e_2245_);
lean_closure_set(v___f_2260_, 1, v_inst_2247_);
lean_closure_set(v___f_2260_, 2, v_toBind_2248_);
lean_closure_set(v___f_2260_, 3, v___f_2259_);
v___f_2261_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__3), 5, 4);
lean_closure_set(v___f_2261_, 0, v_inst_2249_);
lean_closure_set(v___f_2261_, 1, v_e_2245_);
lean_closure_set(v___f_2261_, 2, v_toBind_2248_);
lean_closure_set(v___f_2261_, 3, v___f_2260_);
v___x_2262_ = lean_apply_1(v_modifyRing_2250_, v___f_2258_);
v___x_2263_ = lean_apply_4(v_toBind_2248_, lean_box(0), lean_box(0), v___x_2262_, v___f_2261_);
return v___x_2263_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg(lean_object* v_inst_2266_, lean_object* v_inst_2267_, lean_object* v_inst_2268_, lean_object* v_inst_2269_, lean_object* v_e_2270_){
_start:
{
lean_object* v_toApplicative_2271_; lean_object* v_toBind_2272_; lean_object* v_getRing_2273_; lean_object* v_modifyRing_2274_; lean_object* v_toPure_2275_; lean_object* v___f_2276_; lean_object* v___f_2277_; lean_object* v___f_2278_; lean_object* v___x_2279_; 
v_toApplicative_2271_ = lean_ctor_get(v_inst_2267_, 0);
lean_inc_ref(v_toApplicative_2271_);
v_toBind_2272_ = lean_ctor_get(v_inst_2267_, 1);
lean_inc_n(v_toBind_2272_, 2);
lean_dec_ref(v_inst_2267_);
v_getRing_2273_ = lean_ctor_get(v_inst_2268_, 0);
lean_inc(v_getRing_2273_);
v_modifyRing_2274_ = lean_ctor_get(v_inst_2268_, 1);
lean_inc(v_modifyRing_2274_);
lean_dec_ref(v_inst_2268_);
v_toPure_2275_ = lean_ctor_get(v_toApplicative_2271_, 1);
lean_inc(v_toPure_2275_);
lean_dec_ref(v_toApplicative_2271_);
v___f_2276_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___closed__0));
v___f_2277_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___closed__1));
v___f_2278_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__4), 9, 8);
lean_closure_set(v___f_2278_, 0, v___f_2276_);
lean_closure_set(v___f_2278_, 1, v___f_2277_);
lean_closure_set(v___f_2278_, 2, v_e_2270_);
lean_closure_set(v___f_2278_, 3, v_toPure_2275_);
lean_closure_set(v___f_2278_, 4, v_inst_2266_);
lean_closure_set(v___f_2278_, 5, v_toBind_2272_);
lean_closure_set(v___f_2278_, 6, v_inst_2269_);
lean_closure_set(v___f_2278_, 7, v_modifyRing_2274_);
v___x_2279_ = lean_apply_4(v_toBind_2272_, lean_box(0), lean_box(0), v_getRing_2273_, v___f_2278_);
return v___x_2279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore(lean_object* v_m_2280_, lean_object* v_inst_2281_, lean_object* v_inst_2282_, lean_object* v_inst_2283_, lean_object* v_inst_2284_, lean_object* v_e_2285_){
_start:
{
lean_object* v___x_2286_; 
v___x_2286_ = l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg(v_inst_2281_, v_inst_2282_, v_inst_2283_, v_inst_2284_, v_e_2285_);
return v___x_2286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___lam__0(lean_object* v_e_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_){
_start:
{
lean_object* v___x_2300_; 
v___x_2300_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(v_e_2287_, v___y_2288_, v___y_2289_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_);
return v___x_2300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___lam__0___boxed(lean_object* v_e_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_){
_start:
{
lean_object* v_res_2314_; 
v_res_2314_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___lam__0(v_e_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_);
lean_dec(v___y_2312_);
lean_dec_ref(v___y_2311_);
lean_dec(v___y_2310_);
lean_dec_ref(v___y_2309_);
lean_dec(v___y_2308_);
lean_dec_ref(v___y_2307_);
lean_dec(v___y_2306_);
lean_dec_ref(v___y_2305_);
lean_dec(v___y_2304_);
lean_dec(v___y_2303_);
lean_dec_ref(v___y_2302_);
return v_res_2314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkVar_spec__0___lam__0(lean_object* v_e_2317_, lean_object* v_size_2318_, lean_object* v_s_2319_){
_start:
{
lean_object* v_toRing_2320_; lean_object* v_invFn_x3f_2321_; lean_object* v_semiringId_x3f_2322_; lean_object* v_commSemiringInst_2323_; lean_object* v_commRingInst_2324_; lean_object* v_noZeroDivInst_x3f_2325_; lean_object* v_fieldInst_x3f_2326_; lean_object* v_powIdentityInst_x3f_2327_; lean_object* v_denoteEntries_2328_; lean_object* v_nextId_2329_; lean_object* v_steps_2330_; lean_object* v_queue_2331_; lean_object* v_basis_2332_; lean_object* v_diseqs_2333_; uint8_t v_recheck_2334_; lean_object* v_invSet_2335_; lean_object* v_powIdentityVarCount_2336_; lean_object* v_numEq0_x3f_2337_; uint8_t v_numEq0Updated_2338_; lean_object* v___x_2340_; uint8_t v_isShared_2341_; uint8_t v_isSharedCheck_2371_; 
v_toRing_2320_ = lean_ctor_get(v_s_2319_, 0);
v_invFn_x3f_2321_ = lean_ctor_get(v_s_2319_, 1);
v_semiringId_x3f_2322_ = lean_ctor_get(v_s_2319_, 2);
v_commSemiringInst_2323_ = lean_ctor_get(v_s_2319_, 3);
v_commRingInst_2324_ = lean_ctor_get(v_s_2319_, 4);
v_noZeroDivInst_x3f_2325_ = lean_ctor_get(v_s_2319_, 5);
v_fieldInst_x3f_2326_ = lean_ctor_get(v_s_2319_, 6);
v_powIdentityInst_x3f_2327_ = lean_ctor_get(v_s_2319_, 7);
v_denoteEntries_2328_ = lean_ctor_get(v_s_2319_, 8);
v_nextId_2329_ = lean_ctor_get(v_s_2319_, 9);
v_steps_2330_ = lean_ctor_get(v_s_2319_, 10);
v_queue_2331_ = lean_ctor_get(v_s_2319_, 11);
v_basis_2332_ = lean_ctor_get(v_s_2319_, 12);
v_diseqs_2333_ = lean_ctor_get(v_s_2319_, 13);
v_recheck_2334_ = lean_ctor_get_uint8(v_s_2319_, sizeof(void*)*17);
v_invSet_2335_ = lean_ctor_get(v_s_2319_, 14);
v_powIdentityVarCount_2336_ = lean_ctor_get(v_s_2319_, 15);
v_numEq0_x3f_2337_ = lean_ctor_get(v_s_2319_, 16);
v_numEq0Updated_2338_ = lean_ctor_get_uint8(v_s_2319_, sizeof(void*)*17 + 1);
v_isSharedCheck_2371_ = !lean_is_exclusive(v_s_2319_);
if (v_isSharedCheck_2371_ == 0)
{
v___x_2340_ = v_s_2319_;
v_isShared_2341_ = v_isSharedCheck_2371_;
goto v_resetjp_2339_;
}
else
{
lean_inc(v_numEq0_x3f_2337_);
lean_inc(v_powIdentityVarCount_2336_);
lean_inc(v_invSet_2335_);
lean_inc(v_diseqs_2333_);
lean_inc(v_basis_2332_);
lean_inc(v_queue_2331_);
lean_inc(v_steps_2330_);
lean_inc(v_nextId_2329_);
lean_inc(v_denoteEntries_2328_);
lean_inc(v_powIdentityInst_x3f_2327_);
lean_inc(v_fieldInst_x3f_2326_);
lean_inc(v_noZeroDivInst_x3f_2325_);
lean_inc(v_commRingInst_2324_);
lean_inc(v_commSemiringInst_2323_);
lean_inc(v_semiringId_x3f_2322_);
lean_inc(v_invFn_x3f_2321_);
lean_inc(v_toRing_2320_);
lean_dec(v_s_2319_);
v___x_2340_ = lean_box(0);
v_isShared_2341_ = v_isSharedCheck_2371_;
goto v_resetjp_2339_;
}
v_resetjp_2339_:
{
lean_object* v_id_2342_; lean_object* v_type_2343_; lean_object* v_u_2344_; lean_object* v_ringInst_2345_; lean_object* v_semiringInst_2346_; lean_object* v_charInst_x3f_2347_; lean_object* v_addFn_x3f_2348_; lean_object* v_mulFn_x3f_2349_; lean_object* v_subFn_x3f_2350_; lean_object* v_negFn_x3f_2351_; lean_object* v_powFn_x3f_2352_; lean_object* v_intCastFn_x3f_2353_; lean_object* v_natCastFn_x3f_2354_; lean_object* v_one_x3f_2355_; lean_object* v_vars_2356_; lean_object* v_varMap_2357_; lean_object* v_denote_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2370_; 
v_id_2342_ = lean_ctor_get(v_toRing_2320_, 0);
v_type_2343_ = lean_ctor_get(v_toRing_2320_, 1);
v_u_2344_ = lean_ctor_get(v_toRing_2320_, 2);
v_ringInst_2345_ = lean_ctor_get(v_toRing_2320_, 3);
v_semiringInst_2346_ = lean_ctor_get(v_toRing_2320_, 4);
v_charInst_x3f_2347_ = lean_ctor_get(v_toRing_2320_, 5);
v_addFn_x3f_2348_ = lean_ctor_get(v_toRing_2320_, 6);
v_mulFn_x3f_2349_ = lean_ctor_get(v_toRing_2320_, 7);
v_subFn_x3f_2350_ = lean_ctor_get(v_toRing_2320_, 8);
v_negFn_x3f_2351_ = lean_ctor_get(v_toRing_2320_, 9);
v_powFn_x3f_2352_ = lean_ctor_get(v_toRing_2320_, 10);
v_intCastFn_x3f_2353_ = lean_ctor_get(v_toRing_2320_, 11);
v_natCastFn_x3f_2354_ = lean_ctor_get(v_toRing_2320_, 12);
v_one_x3f_2355_ = lean_ctor_get(v_toRing_2320_, 13);
v_vars_2356_ = lean_ctor_get(v_toRing_2320_, 14);
v_varMap_2357_ = lean_ctor_get(v_toRing_2320_, 15);
v_denote_2358_ = lean_ctor_get(v_toRing_2320_, 16);
v_isSharedCheck_2370_ = !lean_is_exclusive(v_toRing_2320_);
if (v_isSharedCheck_2370_ == 0)
{
v___x_2360_ = v_toRing_2320_;
v_isShared_2361_ = v_isSharedCheck_2370_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_denote_2358_);
lean_inc(v_varMap_2357_);
lean_inc(v_vars_2356_);
lean_inc(v_one_x3f_2355_);
lean_inc(v_natCastFn_x3f_2354_);
lean_inc(v_intCastFn_x3f_2353_);
lean_inc(v_powFn_x3f_2352_);
lean_inc(v_negFn_x3f_2351_);
lean_inc(v_subFn_x3f_2350_);
lean_inc(v_mulFn_x3f_2349_);
lean_inc(v_addFn_x3f_2348_);
lean_inc(v_charInst_x3f_2347_);
lean_inc(v_semiringInst_2346_);
lean_inc(v_ringInst_2345_);
lean_inc(v_u_2344_);
lean_inc(v_type_2343_);
lean_inc(v_id_2342_);
lean_dec(v_toRing_2320_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2370_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2365_; 
lean_inc_ref(v_e_2317_);
v___x_2362_ = l_Lean_PersistentArray_push___redArg(v_vars_2356_, v_e_2317_);
v___x_2363_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0___redArg(v_varMap_2357_, v_e_2317_, v_size_2318_);
if (v_isShared_2361_ == 0)
{
lean_ctor_set(v___x_2360_, 15, v___x_2363_);
lean_ctor_set(v___x_2360_, 14, v___x_2362_);
v___x_2365_ = v___x_2360_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v_id_2342_);
lean_ctor_set(v_reuseFailAlloc_2369_, 1, v_type_2343_);
lean_ctor_set(v_reuseFailAlloc_2369_, 2, v_u_2344_);
lean_ctor_set(v_reuseFailAlloc_2369_, 3, v_ringInst_2345_);
lean_ctor_set(v_reuseFailAlloc_2369_, 4, v_semiringInst_2346_);
lean_ctor_set(v_reuseFailAlloc_2369_, 5, v_charInst_x3f_2347_);
lean_ctor_set(v_reuseFailAlloc_2369_, 6, v_addFn_x3f_2348_);
lean_ctor_set(v_reuseFailAlloc_2369_, 7, v_mulFn_x3f_2349_);
lean_ctor_set(v_reuseFailAlloc_2369_, 8, v_subFn_x3f_2350_);
lean_ctor_set(v_reuseFailAlloc_2369_, 9, v_negFn_x3f_2351_);
lean_ctor_set(v_reuseFailAlloc_2369_, 10, v_powFn_x3f_2352_);
lean_ctor_set(v_reuseFailAlloc_2369_, 11, v_intCastFn_x3f_2353_);
lean_ctor_set(v_reuseFailAlloc_2369_, 12, v_natCastFn_x3f_2354_);
lean_ctor_set(v_reuseFailAlloc_2369_, 13, v_one_x3f_2355_);
lean_ctor_set(v_reuseFailAlloc_2369_, 14, v___x_2362_);
lean_ctor_set(v_reuseFailAlloc_2369_, 15, v___x_2363_);
lean_ctor_set(v_reuseFailAlloc_2369_, 16, v_denote_2358_);
v___x_2365_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
lean_object* v___x_2367_; 
if (v_isShared_2341_ == 0)
{
lean_ctor_set(v___x_2340_, 0, v___x_2365_);
v___x_2367_ = v___x_2340_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v___x_2365_);
lean_ctor_set(v_reuseFailAlloc_2368_, 1, v_invFn_x3f_2321_);
lean_ctor_set(v_reuseFailAlloc_2368_, 2, v_semiringId_x3f_2322_);
lean_ctor_set(v_reuseFailAlloc_2368_, 3, v_commSemiringInst_2323_);
lean_ctor_set(v_reuseFailAlloc_2368_, 4, v_commRingInst_2324_);
lean_ctor_set(v_reuseFailAlloc_2368_, 5, v_noZeroDivInst_x3f_2325_);
lean_ctor_set(v_reuseFailAlloc_2368_, 6, v_fieldInst_x3f_2326_);
lean_ctor_set(v_reuseFailAlloc_2368_, 7, v_powIdentityInst_x3f_2327_);
lean_ctor_set(v_reuseFailAlloc_2368_, 8, v_denoteEntries_2328_);
lean_ctor_set(v_reuseFailAlloc_2368_, 9, v_nextId_2329_);
lean_ctor_set(v_reuseFailAlloc_2368_, 10, v_steps_2330_);
lean_ctor_set(v_reuseFailAlloc_2368_, 11, v_queue_2331_);
lean_ctor_set(v_reuseFailAlloc_2368_, 12, v_basis_2332_);
lean_ctor_set(v_reuseFailAlloc_2368_, 13, v_diseqs_2333_);
lean_ctor_set(v_reuseFailAlloc_2368_, 14, v_invSet_2335_);
lean_ctor_set(v_reuseFailAlloc_2368_, 15, v_powIdentityVarCount_2336_);
lean_ctor_set(v_reuseFailAlloc_2368_, 16, v_numEq0_x3f_2337_);
lean_ctor_set_uint8(v_reuseFailAlloc_2368_, sizeof(void*)*17, v_recheck_2334_);
lean_ctor_set_uint8(v_reuseFailAlloc_2368_, sizeof(void*)*17 + 1, v_numEq0Updated_2338_);
v___x_2367_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
return v___x_2367_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkVar_spec__0(lean_object* v_e_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_){
_start:
{
lean_object* v___x_2385_; 
v___x_2385_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_);
if (lean_obj_tag(v___x_2385_) == 0)
{
lean_object* v_a_2386_; lean_object* v___x_2388_; uint8_t v_isShared_2389_; uint8_t v_isSharedCheck_2436_; 
v_a_2386_ = lean_ctor_get(v___x_2385_, 0);
v_isSharedCheck_2436_ = !lean_is_exclusive(v___x_2385_);
if (v_isSharedCheck_2436_ == 0)
{
v___x_2388_ = v___x_2385_;
v_isShared_2389_ = v_isSharedCheck_2436_;
goto v_resetjp_2387_;
}
else
{
lean_inc(v_a_2386_);
lean_dec(v___x_2385_);
v___x_2388_ = lean_box(0);
v_isShared_2389_ = v_isSharedCheck_2436_;
goto v_resetjp_2387_;
}
v_resetjp_2387_:
{
lean_object* v_toRing_2390_; lean_object* v_vars_2391_; lean_object* v_varMap_2392_; lean_object* v___x_2393_; 
v_toRing_2390_ = lean_ctor_get(v_a_2386_, 0);
lean_inc_ref(v_toRing_2390_);
lean_dec(v_a_2386_);
v_vars_2391_ = lean_ctor_get(v_toRing_2390_, 14);
lean_inc_ref(v_vars_2391_);
v_varMap_2392_ = lean_ctor_get(v_toRing_2390_, 15);
lean_inc_ref(v_varMap_2392_);
lean_dec_ref(v_toRing_2390_);
v___x_2393_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(v_varMap_2392_, v_e_2372_);
lean_dec_ref(v_varMap_2392_);
if (lean_obj_tag(v___x_2393_) == 1)
{
lean_object* v_val_2394_; lean_object* v___x_2396_; 
lean_dec_ref(v_vars_2391_);
lean_dec_ref(v_e_2372_);
v_val_2394_ = lean_ctor_get(v___x_2393_, 0);
lean_inc(v_val_2394_);
lean_dec_ref(v___x_2393_);
if (v_isShared_2389_ == 0)
{
lean_ctor_set(v___x_2388_, 0, v_val_2394_);
v___x_2396_ = v___x_2388_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v_val_2394_);
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
lean_object* v_size_2398_; lean_object* v___f_2399_; lean_object* v___x_2400_; 
lean_dec(v___x_2393_);
lean_del_object(v___x_2388_);
v_size_2398_ = lean_ctor_get(v_vars_2391_, 2);
lean_inc_n(v_size_2398_, 2);
lean_dec_ref(v_vars_2391_);
lean_inc_ref(v_e_2372_);
v___f_2399_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkVar_spec__0___lam__0), 3, 2);
lean_closure_set(v___f_2399_, 0, v_e_2372_);
lean_closure_set(v___f_2399_, 1, v_size_2398_);
v___x_2400_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_2399_, v___y_2373_, v___y_2374_);
if (lean_obj_tag(v___x_2400_) == 0)
{
lean_object* v___x_2401_; 
lean_dec_ref(v___x_2400_);
lean_inc_ref(v_e_2372_);
v___x_2401_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(v_e_2372_, v___y_2373_, v___y_2374_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_);
if (lean_obj_tag(v___x_2401_) == 0)
{
lean_object* v___x_2402_; lean_object* v___x_2403_; 
lean_dec_ref(v___x_2401_);
v___x_2402_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_2403_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_2402_, v_e_2372_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_);
if (lean_obj_tag(v___x_2403_) == 0)
{
lean_object* v___x_2405_; uint8_t v_isShared_2406_; uint8_t v_isSharedCheck_2410_; 
v_isSharedCheck_2410_ = !lean_is_exclusive(v___x_2403_);
if (v_isSharedCheck_2410_ == 0)
{
lean_object* v_unused_2411_; 
v_unused_2411_ = lean_ctor_get(v___x_2403_, 0);
lean_dec(v_unused_2411_);
v___x_2405_ = v___x_2403_;
v_isShared_2406_ = v_isSharedCheck_2410_;
goto v_resetjp_2404_;
}
else
{
lean_dec(v___x_2403_);
v___x_2405_ = lean_box(0);
v_isShared_2406_ = v_isSharedCheck_2410_;
goto v_resetjp_2404_;
}
v_resetjp_2404_:
{
lean_object* v___x_2408_; 
if (v_isShared_2406_ == 0)
{
lean_ctor_set(v___x_2405_, 0, v_size_2398_);
v___x_2408_ = v___x_2405_;
goto v_reusejp_2407_;
}
else
{
lean_object* v_reuseFailAlloc_2409_; 
v_reuseFailAlloc_2409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2409_, 0, v_size_2398_);
v___x_2408_ = v_reuseFailAlloc_2409_;
goto v_reusejp_2407_;
}
v_reusejp_2407_:
{
return v___x_2408_;
}
}
}
else
{
lean_object* v_a_2412_; lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2419_; 
lean_dec(v_size_2398_);
v_a_2412_ = lean_ctor_get(v___x_2403_, 0);
v_isSharedCheck_2419_ = !lean_is_exclusive(v___x_2403_);
if (v_isSharedCheck_2419_ == 0)
{
v___x_2414_ = v___x_2403_;
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
else
{
lean_inc(v_a_2412_);
lean_dec(v___x_2403_);
v___x_2414_ = lean_box(0);
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
v_resetjp_2413_:
{
lean_object* v___x_2417_; 
if (v_isShared_2415_ == 0)
{
v___x_2417_ = v___x_2414_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v_a_2412_);
v___x_2417_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
return v___x_2417_;
}
}
}
}
else
{
lean_object* v_a_2420_; lean_object* v___x_2422_; uint8_t v_isShared_2423_; uint8_t v_isSharedCheck_2427_; 
lean_dec(v_size_2398_);
lean_dec_ref(v_e_2372_);
v_a_2420_ = lean_ctor_get(v___x_2401_, 0);
v_isSharedCheck_2427_ = !lean_is_exclusive(v___x_2401_);
if (v_isSharedCheck_2427_ == 0)
{
v___x_2422_ = v___x_2401_;
v_isShared_2423_ = v_isSharedCheck_2427_;
goto v_resetjp_2421_;
}
else
{
lean_inc(v_a_2420_);
lean_dec(v___x_2401_);
v___x_2422_ = lean_box(0);
v_isShared_2423_ = v_isSharedCheck_2427_;
goto v_resetjp_2421_;
}
v_resetjp_2421_:
{
lean_object* v___x_2425_; 
if (v_isShared_2423_ == 0)
{
v___x_2425_ = v___x_2422_;
goto v_reusejp_2424_;
}
else
{
lean_object* v_reuseFailAlloc_2426_; 
v_reuseFailAlloc_2426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2426_, 0, v_a_2420_);
v___x_2425_ = v_reuseFailAlloc_2426_;
goto v_reusejp_2424_;
}
v_reusejp_2424_:
{
return v___x_2425_;
}
}
}
}
else
{
lean_object* v_a_2428_; lean_object* v___x_2430_; uint8_t v_isShared_2431_; uint8_t v_isSharedCheck_2435_; 
lean_dec(v_size_2398_);
lean_dec_ref(v_e_2372_);
v_a_2428_ = lean_ctor_get(v___x_2400_, 0);
v_isSharedCheck_2435_ = !lean_is_exclusive(v___x_2400_);
if (v_isSharedCheck_2435_ == 0)
{
v___x_2430_ = v___x_2400_;
v_isShared_2431_ = v_isSharedCheck_2435_;
goto v_resetjp_2429_;
}
else
{
lean_inc(v_a_2428_);
lean_dec(v___x_2400_);
v___x_2430_ = lean_box(0);
v_isShared_2431_ = v_isSharedCheck_2435_;
goto v_resetjp_2429_;
}
v_resetjp_2429_:
{
lean_object* v___x_2433_; 
if (v_isShared_2431_ == 0)
{
v___x_2433_ = v___x_2430_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v_a_2428_);
v___x_2433_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
return v___x_2433_;
}
}
}
}
}
}
else
{
lean_object* v_a_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2444_; 
lean_dec_ref(v_e_2372_);
v_a_2437_ = lean_ctor_get(v___x_2385_, 0);
v_isSharedCheck_2444_ = !lean_is_exclusive(v___x_2385_);
if (v_isSharedCheck_2444_ == 0)
{
v___x_2439_ = v___x_2385_;
v_isShared_2440_ = v_isSharedCheck_2444_;
goto v_resetjp_2438_;
}
else
{
lean_inc(v_a_2437_);
lean_dec(v___x_2385_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2444_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v___x_2442_; 
if (v_isShared_2440_ == 0)
{
v___x_2442_ = v___x_2439_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2443_; 
v_reuseFailAlloc_2443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2443_, 0, v_a_2437_);
v___x_2442_ = v_reuseFailAlloc_2443_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
return v___x_2442_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkVar_spec__0___boxed(lean_object* v_e_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_){
_start:
{
lean_object* v_res_2458_; 
v_res_2458_ = l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkVar_spec__0(v_e_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_);
lean_dec(v___y_2456_);
lean_dec_ref(v___y_2455_);
lean_dec(v___y_2454_);
lean_dec_ref(v___y_2453_);
lean_dec(v___y_2452_);
lean_dec_ref(v___y_2451_);
lean_dec(v___y_2450_);
lean_dec_ref(v___y_2449_);
lean_dec(v___y_2448_);
lean_dec(v___y_2447_);
lean_dec_ref(v___y_2446_);
return v_res_2458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVar(lean_object* v_e_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_){
_start:
{
lean_object* v___x_2472_; 
v___x_2472_ = l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkVar_spec__0(v_e_2459_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_);
return v___x_2472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVar___boxed(lean_object* v_e_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_){
_start:
{
lean_object* v_res_2486_; 
v_res_2486_ = l_Lean_Meta_Grind_Arith_CommRing_mkVar(v_e_2473_, v_a_2474_, v_a_2475_, v_a_2476_, v_a_2477_, v_a_2478_, v_a_2479_, v_a_2480_, v_a_2481_, v_a_2482_, v_a_2483_, v_a_2484_);
lean_dec(v_a_2484_);
lean_dec_ref(v_a_2483_);
lean_dec(v_a_2482_);
lean_dec_ref(v_a_2481_);
lean_dec(v_a_2480_);
lean_dec_ref(v_a_2479_);
lean_dec(v_a_2478_);
lean_dec_ref(v_a_2477_);
lean_dec(v_a_2476_);
lean_dec(v_a_2475_);
lean_dec_ref(v_a_2474_);
return v_res_2486_;
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
