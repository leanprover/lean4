// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.CommRing.RingM
// Imports: public import Lean.Meta.Tactic.Grind.SynthInstance public import Lean.Meta.Tactic.Grind.Arith.CommRing.MonadRing import Lean.Meta.Sym.Arith.Poly
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
lean_object* l_Lean_Grind_CommRing_Poly_degree(lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_CommRing_ringExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Meta_Sym_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_canon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_SolverExtension_markTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
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
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "ring polynomial degree "};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__1;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = " exceeds threshold `(ringMaxDegree := "};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__3;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ")`"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref_known(v___x_5_, 1);
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
v_ringSteps_12_ = lean_ctor_get(v_a_8_, 6);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___lam__0(uint8_t v___x_65_, lean_object* v_s_66_){
_start:
{
lean_object* v_rings_67_; lean_object* v_typeIdOf_68_; lean_object* v_exprToRingId_69_; lean_object* v_semirings_70_; lean_object* v_stypeIdOf_71_; lean_object* v_exprToSemiringId_72_; lean_object* v_ncRings_73_; lean_object* v_exprToNCRingId_74_; lean_object* v_nctypeIdOf_75_; lean_object* v_ncSemirings_76_; lean_object* v_exprToNCSemiringId_77_; lean_object* v_ncstypeIdOf_78_; lean_object* v_steps_79_; lean_object* v___x_81_; uint8_t v_isShared_82_; uint8_t v_isSharedCheck_86_; 
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
v_isSharedCheck_86_ = !lean_is_exclusive(v_s_66_);
if (v_isSharedCheck_86_ == 0)
{
v___x_81_ = v_s_66_;
v_isShared_82_ = v_isSharedCheck_86_;
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
v_isShared_82_ = v_isSharedCheck_86_;
goto v_resetjp_80_;
}
v_resetjp_80_:
{
lean_object* v___x_84_; 
if (v_isShared_82_ == 0)
{
v___x_84_ = v___x_81_;
goto v_reusejp_83_;
}
else
{
lean_object* v_reuseFailAlloc_85_; 
v_reuseFailAlloc_85_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_85_, 0, v_rings_67_);
lean_ctor_set(v_reuseFailAlloc_85_, 1, v_typeIdOf_68_);
lean_ctor_set(v_reuseFailAlloc_85_, 2, v_exprToRingId_69_);
lean_ctor_set(v_reuseFailAlloc_85_, 3, v_semirings_70_);
lean_ctor_set(v_reuseFailAlloc_85_, 4, v_stypeIdOf_71_);
lean_ctor_set(v_reuseFailAlloc_85_, 5, v_exprToSemiringId_72_);
lean_ctor_set(v_reuseFailAlloc_85_, 6, v_ncRings_73_);
lean_ctor_set(v_reuseFailAlloc_85_, 7, v_exprToNCRingId_74_);
lean_ctor_set(v_reuseFailAlloc_85_, 8, v_nctypeIdOf_75_);
lean_ctor_set(v_reuseFailAlloc_85_, 9, v_ncSemirings_76_);
lean_ctor_set(v_reuseFailAlloc_85_, 10, v_exprToNCSemiringId_77_);
lean_ctor_set(v_reuseFailAlloc_85_, 11, v_ncstypeIdOf_78_);
lean_ctor_set(v_reuseFailAlloc_85_, 12, v_steps_79_);
v___x_84_ = v_reuseFailAlloc_85_;
goto v_reusejp_83_;
}
v_reusejp_83_:
{
lean_ctor_set_uint8(v___x_84_, sizeof(void*)*13, v___x_65_);
return v___x_84_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___lam__0___boxed(lean_object* v___x_87_, lean_object* v_s_88_){
_start:
{
uint8_t v___x_7553__boxed_89_; lean_object* v_res_90_; 
v___x_7553__boxed_89_ = lean_unbox(v___x_87_);
v_res_90_ = l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___lam__0(v___x_7553__boxed_89_, v_s_88_);
return v_res_90_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__1(void){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_92_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__0));
v___x_93_ = l_Lean_stringToMessageData(v___x_92_);
return v___x_93_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__3(void){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_95_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__2));
v___x_96_ = l_Lean_stringToMessageData(v___x_95_);
return v___x_96_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__5(void){
_start:
{
lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_98_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__4));
v___x_99_ = l_Lean_stringToMessageData(v___x_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg(lean_object* v_p_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_102_);
if (lean_obj_tag(v___x_110_) == 0)
{
lean_object* v_a_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_200_; 
v_a_111_ = lean_ctor_get(v___x_110_, 0);
v_isSharedCheck_200_ = !lean_is_exclusive(v___x_110_);
if (v_isSharedCheck_200_ == 0)
{
v___x_113_ = v___x_110_;
v_isShared_114_ = v_isSharedCheck_200_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_a_111_);
lean_dec(v___x_110_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_200_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
lean_object* v_ringMaxDegree_115_; lean_object* v___x_116_; uint8_t v___x_117_; 
v_ringMaxDegree_115_ = lean_ctor_get(v_a_111_, 7);
lean_inc(v_ringMaxDegree_115_);
lean_dec(v_a_111_);
v___x_116_ = l_Lean_Grind_CommRing_Poly_degree(v_p_100_);
v___x_117_ = lean_nat_dec_le(v_ringMaxDegree_115_, v___x_116_);
lean_dec(v_ringMaxDegree_115_);
if (v___x_117_ == 0)
{
lean_object* v___x_118_; lean_object* v___x_120_; 
lean_dec(v___x_116_);
v___x_118_ = lean_box(v___x_117_);
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 0, v___x_118_);
v___x_120_ = v___x_113_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v___x_118_);
v___x_120_ = v_reuseFailAlloc_121_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
return v___x_120_;
}
}
else
{
lean_object* v___x_122_; 
lean_del_object(v___x_113_);
v___x_122_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_101_, v_a_107_);
if (lean_obj_tag(v___x_122_) == 0)
{
lean_object* v_a_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_191_; 
v_a_123_ = lean_ctor_get(v___x_122_, 0);
v_isSharedCheck_191_ = !lean_is_exclusive(v___x_122_);
if (v_isSharedCheck_191_ == 0)
{
v___x_125_ = v___x_122_;
v_isShared_126_ = v_isSharedCheck_191_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_a_123_);
lean_dec(v___x_122_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_191_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
uint8_t v_reportedMaxDegreeIssue_127_; 
v_reportedMaxDegreeIssue_127_ = lean_ctor_get_uint8(v_a_123_, sizeof(void*)*13);
lean_dec(v_a_123_);
if (v_reportedMaxDegreeIssue_127_ == 0)
{
lean_object* v___x_128_; lean_object* v___f_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
lean_del_object(v___x_125_);
v___x_128_ = lean_box(v___x_117_);
v___f_129_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_129_, 0, v___x_128_);
v___x_130_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_131_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_130_, v___f_129_, v_a_101_);
if (lean_obj_tag(v___x_131_) == 0)
{
lean_object* v___x_132_; 
lean_dec_ref_known(v___x_131_, 1);
v___x_132_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_103_);
if (lean_obj_tag(v___x_132_) == 0)
{
lean_object* v_a_133_; lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_170_; 
v_a_133_ = lean_ctor_get(v___x_132_, 0);
v_isSharedCheck_170_ = !lean_is_exclusive(v___x_132_);
if (v_isSharedCheck_170_ == 0)
{
v___x_135_ = v___x_132_;
v_isShared_136_ = v_isSharedCheck_170_;
goto v_resetjp_134_;
}
else
{
lean_inc(v_a_133_);
lean_dec(v___x_132_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_170_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
uint8_t v___x_137_; 
v___x_137_ = lean_unbox(v_a_133_);
lean_dec(v_a_133_);
if (v___x_137_ == 0)
{
lean_object* v___x_138_; lean_object* v___x_140_; 
lean_dec(v___x_116_);
v___x_138_ = lean_box(v___x_117_);
if (v_isShared_136_ == 0)
{
lean_ctor_set(v___x_135_, 0, v___x_138_);
v___x_140_ = v___x_135_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v___x_138_);
v___x_140_ = v_reuseFailAlloc_141_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
return v___x_140_;
}
}
else
{
lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
lean_del_object(v___x_135_);
v___x_142_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__1);
v___x_143_ = l_Nat_reprFast(v___x_116_);
v___x_144_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_144_, 0, v___x_143_);
v___x_145_ = l_Lean_MessageData_ofFormat(v___x_144_);
lean_inc_ref(v___x_145_);
v___x_146_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_146_, 0, v___x_142_);
lean_ctor_set(v___x_146_, 1, v___x_145_);
v___x_147_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__3, &l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__3_once, _init_l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__3);
v___x_148_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_148_, 0, v___x_146_);
lean_ctor_set(v___x_148_, 1, v___x_147_);
v___x_149_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_149_, 0, v___x_148_);
lean_ctor_set(v___x_149_, 1, v___x_145_);
v___x_150_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__5, &l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__5_once, _init_l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___closed__5);
v___x_151_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_151_, 0, v___x_149_);
lean_ctor_set(v___x_151_, 1, v___x_150_);
v___x_152_ = l_Lean_Meta_Sym_reportIssue(v___x_151_, v_a_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_);
if (lean_obj_tag(v___x_152_) == 0)
{
lean_object* v___x_154_; uint8_t v_isShared_155_; uint8_t v_isSharedCheck_160_; 
v_isSharedCheck_160_ = !lean_is_exclusive(v___x_152_);
if (v_isSharedCheck_160_ == 0)
{
lean_object* v_unused_161_; 
v_unused_161_ = lean_ctor_get(v___x_152_, 0);
lean_dec(v_unused_161_);
v___x_154_ = v___x_152_;
v_isShared_155_ = v_isSharedCheck_160_;
goto v_resetjp_153_;
}
else
{
lean_dec(v___x_152_);
v___x_154_ = lean_box(0);
v_isShared_155_ = v_isSharedCheck_160_;
goto v_resetjp_153_;
}
v_resetjp_153_:
{
lean_object* v___x_156_; lean_object* v___x_158_; 
v___x_156_ = lean_box(v___x_117_);
if (v_isShared_155_ == 0)
{
lean_ctor_set(v___x_154_, 0, v___x_156_);
v___x_158_ = v___x_154_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v___x_156_);
v___x_158_ = v_reuseFailAlloc_159_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
return v___x_158_;
}
}
}
else
{
lean_object* v_a_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_169_; 
v_a_162_ = lean_ctor_get(v___x_152_, 0);
v_isSharedCheck_169_ = !lean_is_exclusive(v___x_152_);
if (v_isSharedCheck_169_ == 0)
{
v___x_164_ = v___x_152_;
v_isShared_165_ = v_isSharedCheck_169_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_a_162_);
lean_dec(v___x_152_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_169_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v___x_167_; 
if (v_isShared_165_ == 0)
{
v___x_167_ = v___x_164_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v_a_162_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
}
}
}
}
}
}
else
{
lean_object* v_a_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_178_; 
lean_dec(v___x_116_);
v_a_171_ = lean_ctor_get(v___x_132_, 0);
v_isSharedCheck_178_ = !lean_is_exclusive(v___x_132_);
if (v_isSharedCheck_178_ == 0)
{
v___x_173_ = v___x_132_;
v_isShared_174_ = v_isSharedCheck_178_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_a_171_);
lean_dec(v___x_132_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_178_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v___x_176_; 
if (v_isShared_174_ == 0)
{
v___x_176_ = v___x_173_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v_a_171_);
v___x_176_ = v_reuseFailAlloc_177_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
return v___x_176_;
}
}
}
}
else
{
lean_object* v_a_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_186_; 
lean_dec(v___x_116_);
v_a_179_ = lean_ctor_get(v___x_131_, 0);
v_isSharedCheck_186_ = !lean_is_exclusive(v___x_131_);
if (v_isSharedCheck_186_ == 0)
{
v___x_181_ = v___x_131_;
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_a_179_);
lean_dec(v___x_131_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_184_; 
if (v_isShared_182_ == 0)
{
v___x_184_ = v___x_181_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v_a_179_);
v___x_184_ = v_reuseFailAlloc_185_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
return v___x_184_;
}
}
}
}
else
{
lean_object* v___x_187_; lean_object* v___x_189_; 
lean_dec(v___x_116_);
v___x_187_ = lean_box(v___x_117_);
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 0, v___x_187_);
v___x_189_ = v___x_125_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v___x_187_);
v___x_189_ = v_reuseFailAlloc_190_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
return v___x_189_;
}
}
}
}
else
{
lean_object* v_a_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_199_; 
lean_dec(v___x_116_);
v_a_192_ = lean_ctor_get(v___x_122_, 0);
v_isSharedCheck_199_ = !lean_is_exclusive(v___x_122_);
if (v_isSharedCheck_199_ == 0)
{
v___x_194_ = v___x_122_;
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_a_192_);
lean_dec(v___x_122_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
lean_object* v___x_197_; 
if (v_isShared_195_ == 0)
{
v___x_197_ = v___x_194_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v_a_192_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
}
}
}
}
else
{
lean_object* v_a_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_208_; 
v_a_201_ = lean_ctor_get(v___x_110_, 0);
v_isSharedCheck_208_ = !lean_is_exclusive(v___x_110_);
if (v_isSharedCheck_208_ == 0)
{
v___x_203_ = v___x_110_;
v_isShared_204_ = v_isSharedCheck_208_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_a_201_);
lean_dec(v___x_110_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_208_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_206_; 
if (v_isShared_204_ == 0)
{
v___x_206_ = v___x_203_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v_a_201_);
v___x_206_ = v_reuseFailAlloc_207_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
return v___x_206_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg___boxed(lean_object* v_p_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg(v_p_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_);
lean_dec(v_a_217_);
lean_dec_ref(v_a_216_);
lean_dec(v_a_215_);
lean_dec_ref(v_a_214_);
lean_dec(v_a_213_);
lean_dec_ref(v_a_212_);
lean_dec_ref(v_a_211_);
lean_dec(v_a_210_);
lean_dec_ref(v_p_209_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree(lean_object* v_p_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___redArg(v_p_220_, v_a_221_, v_a_223_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree___boxed(lean_object* v_p_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Lean_Meta_Grind_Arith_CommRing_checkMaxDegree(v_p_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_);
lean_dec(v_a_243_);
lean_dec_ref(v_a_242_);
lean_dec(v_a_241_);
lean_dec_ref(v_a_240_);
lean_dec(v_a_239_);
lean_dec_ref(v_a_238_);
lean_dec(v_a_237_);
lean_dec_ref(v_a_236_);
lean_dec(v_a_235_);
lean_dec(v_a_234_);
lean_dec_ref(v_p_233_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg___lam__0(lean_object* v_n_246_, lean_object* v_s_247_){
_start:
{
lean_object* v_rings_248_; lean_object* v_typeIdOf_249_; lean_object* v_exprToRingId_250_; lean_object* v_semirings_251_; lean_object* v_stypeIdOf_252_; lean_object* v_exprToSemiringId_253_; lean_object* v_ncRings_254_; lean_object* v_exprToNCRingId_255_; lean_object* v_nctypeIdOf_256_; lean_object* v_ncSemirings_257_; lean_object* v_exprToNCSemiringId_258_; lean_object* v_ncstypeIdOf_259_; lean_object* v_steps_260_; uint8_t v_reportedMaxDegreeIssue_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_269_; 
v_rings_248_ = lean_ctor_get(v_s_247_, 0);
v_typeIdOf_249_ = lean_ctor_get(v_s_247_, 1);
v_exprToRingId_250_ = lean_ctor_get(v_s_247_, 2);
v_semirings_251_ = lean_ctor_get(v_s_247_, 3);
v_stypeIdOf_252_ = lean_ctor_get(v_s_247_, 4);
v_exprToSemiringId_253_ = lean_ctor_get(v_s_247_, 5);
v_ncRings_254_ = lean_ctor_get(v_s_247_, 6);
v_exprToNCRingId_255_ = lean_ctor_get(v_s_247_, 7);
v_nctypeIdOf_256_ = lean_ctor_get(v_s_247_, 8);
v_ncSemirings_257_ = lean_ctor_get(v_s_247_, 9);
v_exprToNCSemiringId_258_ = lean_ctor_get(v_s_247_, 10);
v_ncstypeIdOf_259_ = lean_ctor_get(v_s_247_, 11);
v_steps_260_ = lean_ctor_get(v_s_247_, 12);
v_reportedMaxDegreeIssue_261_ = lean_ctor_get_uint8(v_s_247_, sizeof(void*)*13);
v_isSharedCheck_269_ = !lean_is_exclusive(v_s_247_);
if (v_isSharedCheck_269_ == 0)
{
v___x_263_ = v_s_247_;
v_isShared_264_ = v_isSharedCheck_269_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_steps_260_);
lean_inc(v_ncstypeIdOf_259_);
lean_inc(v_exprToNCSemiringId_258_);
lean_inc(v_ncSemirings_257_);
lean_inc(v_nctypeIdOf_256_);
lean_inc(v_exprToNCRingId_255_);
lean_inc(v_ncRings_254_);
lean_inc(v_exprToSemiringId_253_);
lean_inc(v_stypeIdOf_252_);
lean_inc(v_semirings_251_);
lean_inc(v_exprToRingId_250_);
lean_inc(v_typeIdOf_249_);
lean_inc(v_rings_248_);
lean_dec(v_s_247_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_269_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v___x_265_; lean_object* v___x_267_; 
v___x_265_ = lean_nat_add(v_steps_260_, v_n_246_);
lean_dec(v_steps_260_);
if (v_isShared_264_ == 0)
{
lean_ctor_set(v___x_263_, 12, v___x_265_);
v___x_267_ = v___x_263_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v_rings_248_);
lean_ctor_set(v_reuseFailAlloc_268_, 1, v_typeIdOf_249_);
lean_ctor_set(v_reuseFailAlloc_268_, 2, v_exprToRingId_250_);
lean_ctor_set(v_reuseFailAlloc_268_, 3, v_semirings_251_);
lean_ctor_set(v_reuseFailAlloc_268_, 4, v_stypeIdOf_252_);
lean_ctor_set(v_reuseFailAlloc_268_, 5, v_exprToSemiringId_253_);
lean_ctor_set(v_reuseFailAlloc_268_, 6, v_ncRings_254_);
lean_ctor_set(v_reuseFailAlloc_268_, 7, v_exprToNCRingId_255_);
lean_ctor_set(v_reuseFailAlloc_268_, 8, v_nctypeIdOf_256_);
lean_ctor_set(v_reuseFailAlloc_268_, 9, v_ncSemirings_257_);
lean_ctor_set(v_reuseFailAlloc_268_, 10, v_exprToNCSemiringId_258_);
lean_ctor_set(v_reuseFailAlloc_268_, 11, v_ncstypeIdOf_259_);
lean_ctor_set(v_reuseFailAlloc_268_, 12, v___x_265_);
lean_ctor_set_uint8(v_reuseFailAlloc_268_, sizeof(void*)*13, v_reportedMaxDegreeIssue_261_);
v___x_267_ = v_reuseFailAlloc_268_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
return v___x_267_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg___lam__0___boxed(lean_object* v_n_270_, lean_object* v_s_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg___lam__0(v_n_270_, v_s_271_);
lean_dec(v_n_270_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg(lean_object* v_n_273_, lean_object* v_a_274_){
_start:
{
lean_object* v___f_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v___f_276_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_276_, 0, v_n_273_);
v___x_277_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_278_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_277_, v___f_276_, v_a_274_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg___boxed(lean_object* v_n_279_, lean_object* v_a_280_, lean_object* v_a_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg(v_n_279_, v_a_280_);
lean_dec(v_a_280_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_incSteps(lean_object* v_n_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_){
_start:
{
lean_object* v___x_295_; 
v___x_295_ = l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg(v_n_283_, v_a_284_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_incSteps___boxed(lean_object* v_n_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = l_Lean_Meta_Grind_Arith_CommRing_incSteps(v_n_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_, v_a_304_, v_a_305_, v_a_306_);
lean_dec(v_a_306_);
lean_dec_ref(v_a_305_);
lean_dec(v_a_304_);
lean_dec_ref(v_a_303_);
lean_dec(v_a_302_);
lean_dec_ref(v_a_301_);
lean_dec(v_a_300_);
lean_dec_ref(v_a_299_);
lean_dec(v_a_298_);
lean_dec(v_a_297_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_run___redArg(lean_object* v_ringId_309_, lean_object* v_x_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_){
_start:
{
uint8_t v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_322_ = 0;
v___x_323_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_323_, 0, v_ringId_309_);
lean_ctor_set_uint8(v___x_323_, sizeof(void*)*1, v___x_322_);
lean_inc(v_a_320_);
lean_inc_ref(v_a_319_);
lean_inc(v_a_318_);
lean_inc_ref(v_a_317_);
lean_inc(v_a_316_);
lean_inc_ref(v_a_315_);
lean_inc(v_a_314_);
lean_inc_ref(v_a_313_);
lean_inc(v_a_312_);
lean_inc(v_a_311_);
v___x_324_ = lean_apply_12(v_x_310_, v___x_323_, v_a_311_, v_a_312_, v_a_313_, v_a_314_, v_a_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_, v_a_320_, lean_box(0));
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_run___redArg___boxed(lean_object* v_ringId_325_, lean_object* v_x_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_run___redArg(v_ringId_325_, v_x_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_);
lean_dec(v_a_336_);
lean_dec_ref(v_a_335_);
lean_dec(v_a_334_);
lean_dec_ref(v_a_333_);
lean_dec(v_a_332_);
lean_dec_ref(v_a_331_);
lean_dec(v_a_330_);
lean_dec_ref(v_a_329_);
lean_dec(v_a_328_);
lean_dec(v_a_327_);
return v_res_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_run(lean_object* v_00_u03b1_339_, lean_object* v_ringId_340_, lean_object* v_x_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_){
_start:
{
uint8_t v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_353_ = 0;
v___x_354_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_354_, 0, v_ringId_340_);
lean_ctor_set_uint8(v___x_354_, sizeof(void*)*1, v___x_353_);
lean_inc(v_a_351_);
lean_inc_ref(v_a_350_);
lean_inc(v_a_349_);
lean_inc_ref(v_a_348_);
lean_inc(v_a_347_);
lean_inc_ref(v_a_346_);
lean_inc(v_a_345_);
lean_inc_ref(v_a_344_);
lean_inc(v_a_343_);
lean_inc(v_a_342_);
v___x_355_ = lean_apply_12(v_x_341_, v___x_354_, v_a_342_, v_a_343_, v_a_344_, v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_, lean_box(0));
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_run___boxed(lean_object* v_00_u03b1_356_, lean_object* v_ringId_357_, lean_object* v_x_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_run(v_00_u03b1_356_, v_ringId_357_, v_x_358_, v_a_359_, v_a_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_);
lean_dec(v_a_368_);
lean_dec_ref(v_a_367_);
lean_dec(v_a_366_);
lean_dec_ref(v_a_365_);
lean_dec(v_a_364_);
lean_dec_ref(v_a_363_);
lean_dec(v_a_362_);
lean_dec_ref(v_a_361_);
lean_dec(v_a_360_);
lean_dec(v_a_359_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getRingId___redArg(lean_object* v_a_371_){
_start:
{
lean_object* v_ringId_373_; lean_object* v___x_374_; 
v_ringId_373_ = lean_ctor_get(v_a_371_, 0);
lean_inc(v_ringId_373_);
v___x_374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_374_, 0, v_ringId_373_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getRingId___redArg___boxed(lean_object* v_a_375_, lean_object* v_a_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l_Lean_Meta_Grind_Arith_CommRing_getRingId___redArg(v_a_375_);
lean_dec_ref(v_a_375_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getRingId(lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_){
_start:
{
lean_object* v_ringId_390_; lean_object* v___x_391_; 
v_ringId_390_ = lean_ctor_get(v_a_378_, 0);
lean_inc(v_ringId_390_);
v___x_391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_391_, 0, v_ringId_390_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getRingId___boxed(lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l_Lean_Meta_Grind_Arith_CommRing_getRingId(v_a_392_, v_a_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_);
lean_dec(v_a_402_);
lean_dec_ref(v_a_401_);
lean_dec(v_a_400_);
lean_dec_ref(v_a_399_);
lean_dec(v_a_398_);
lean_dec_ref(v_a_397_);
lean_dec(v_a_396_);
lean_dec_ref(v_a_395_);
lean_dec(v_a_394_);
lean_dec(v_a_393_);
lean_dec_ref(v_a_392_);
return v_res_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__0(lean_object* v_e_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = l_Lean_Meta_Sym_canon(v_e_405_, v___y_411_, v___y_412_, v___y_413_, v___y_414_, v___y_415_, v___y_416_);
if (lean_obj_tag(v___x_418_) == 0)
{
lean_object* v_a_419_; lean_object* v___x_420_; 
v_a_419_ = lean_ctor_get(v___x_418_, 0);
lean_inc(v_a_419_);
lean_dec_ref_known(v___x_418_, 1);
v___x_420_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_419_, v___y_412_);
return v___x_420_;
}
else
{
return v___x_418_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__0___boxed(lean_object* v_e_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__0(v_e_421_, v___y_422_, v___y_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_);
lean_dec(v___y_432_);
lean_dec_ref(v___y_431_);
lean_dec(v___y_430_);
lean_dec_ref(v___y_429_);
lean_dec(v___y_428_);
lean_dec_ref(v___y_427_);
lean_dec(v___y_426_);
lean_dec_ref(v___y_425_);
lean_dec(v___y_424_);
lean_dec(v___y_423_);
lean_dec_ref(v___y_422_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__1(lean_object* v_e_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_){
_start:
{
lean_object* v___x_448_; 
v___x_448_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(v_e_435_, v___y_443_, v___y_444_, v___y_445_, v___y_446_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__1___boxed(lean_object* v_e_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonRingM___lam__1(v_e_449_, v___y_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_);
lean_dec(v___y_460_);
lean_dec_ref(v___y_459_);
lean_dec(v___y_458_);
lean_dec_ref(v___y_457_);
lean_dec(v___y_456_);
lean_dec_ref(v___y_455_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
lean_dec(v___y_452_);
lean_dec(v___y_451_);
lean_dec_ref(v___y_450_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0_spec__0(lean_object* v_msgData_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_){
_start:
{
lean_object* v___x_475_; lean_object* v_env_476_; lean_object* v___x_477_; lean_object* v_mctx_478_; lean_object* v_lctx_479_; lean_object* v_options_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_475_ = lean_st_ref_get(v___y_473_);
v_env_476_ = lean_ctor_get(v___x_475_, 0);
lean_inc_ref(v_env_476_);
lean_dec(v___x_475_);
v___x_477_ = lean_st_ref_get(v___y_471_);
v_mctx_478_ = lean_ctor_get(v___x_477_, 0);
lean_inc_ref(v_mctx_478_);
lean_dec(v___x_477_);
v_lctx_479_ = lean_ctor_get(v___y_470_, 2);
v_options_480_ = lean_ctor_get(v___y_472_, 2);
lean_inc_ref(v_options_480_);
lean_inc_ref(v_lctx_479_);
v___x_481_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_481_, 0, v_env_476_);
lean_ctor_set(v___x_481_, 1, v_mctx_478_);
lean_ctor_set(v___x_481_, 2, v_lctx_479_);
lean_ctor_set(v___x_481_, 3, v_options_480_);
v___x_482_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_482_, 0, v___x_481_);
lean_ctor_set(v___x_482_, 1, v_msgData_469_);
v___x_483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_483_, 0, v___x_482_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0_spec__0___boxed(lean_object* v_msgData_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0_spec__0(v_msgData_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_);
lean_dec(v___y_488_);
lean_dec_ref(v___y_487_);
lean_dec(v___y_486_);
lean_dec_ref(v___y_485_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg(lean_object* v_msg_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_){
_start:
{
lean_object* v_ref_497_; lean_object* v___x_498_; lean_object* v_a_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_507_; 
v_ref_497_ = lean_ctor_get(v___y_494_, 5);
v___x_498_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0_spec__0(v_msg_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_);
v_a_499_ = lean_ctor_get(v___x_498_, 0);
v_isSharedCheck_507_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_507_ == 0)
{
v___x_501_ = v___x_498_;
v_isShared_502_ = v_isSharedCheck_507_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_a_499_);
lean_dec(v___x_498_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_507_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_503_; lean_object* v___x_505_; 
lean_inc(v_ref_497_);
v___x_503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_503_, 0, v_ref_497_);
lean_ctor_set(v___x_503_, 1, v_a_499_);
if (v_isShared_502_ == 0)
{
lean_ctor_set_tag(v___x_501_, 1);
lean_ctor_set(v___x_501_, 0, v___x_503_);
v___x_505_ = v___x_501_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v___x_503_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg___boxed(lean_object* v_msg_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg(v_msg_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
return v_res_514_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__1(void){
_start:
{
lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_516_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__0));
v___x_517_ = l_Lean_stringToMessageData(v___x_516_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_){
_start:
{
lean_object* v___x_530_; 
v___x_530_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_519_, v_a_527_);
if (lean_obj_tag(v___x_530_) == 0)
{
lean_object* v_a_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_545_; 
v_a_531_ = lean_ctor_get(v___x_530_, 0);
v_isSharedCheck_545_ = !lean_is_exclusive(v___x_530_);
if (v_isSharedCheck_545_ == 0)
{
v___x_533_ = v___x_530_;
v_isShared_534_ = v_isSharedCheck_545_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_a_531_);
lean_dec(v___x_530_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_545_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v_ringId_535_; lean_object* v_rings_536_; lean_object* v___x_537_; uint8_t v___x_538_; 
v_ringId_535_ = lean_ctor_get(v_a_518_, 0);
v_rings_536_ = lean_ctor_get(v_a_531_, 0);
lean_inc_ref(v_rings_536_);
lean_dec(v_a_531_);
v___x_537_ = lean_array_get_size(v_rings_536_);
v___x_538_ = lean_nat_dec_lt(v_ringId_535_, v___x_537_);
if (v___x_538_ == 0)
{
lean_object* v___x_539_; lean_object* v___x_540_; 
lean_dec_ref(v_rings_536_);
lean_del_object(v___x_533_);
v___x_539_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___closed__1);
v___x_540_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg(v___x_539_, v_a_525_, v_a_526_, v_a_527_, v_a_528_);
return v___x_540_;
}
else
{
lean_object* v___x_541_; lean_object* v___x_543_; 
v___x_541_ = lean_array_fget(v_rings_536_, v_ringId_535_);
lean_dec_ref(v_rings_536_);
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 0, v___x_541_);
v___x_543_ = v___x_533_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v___x_541_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
}
}
else
{
lean_object* v_a_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_553_; 
v_a_546_ = lean_ctor_get(v___x_530_, 0);
v_isSharedCheck_553_ = !lean_is_exclusive(v___x_530_);
if (v_isSharedCheck_553_ == 0)
{
v___x_548_ = v___x_530_;
v_isShared_549_ = v_isSharedCheck_553_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_a_546_);
lean_dec(v___x_530_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_553_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v___x_551_; 
if (v_isShared_549_ == 0)
{
v___x_551_ = v___x_548_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v_a_546_);
v___x_551_ = v_reuseFailAlloc_552_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
return v___x_551_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___boxed(lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_554_, v_a_555_, v_a_556_, v_a_557_, v_a_558_, v_a_559_, v_a_560_, v_a_561_, v_a_562_, v_a_563_, v_a_564_);
lean_dec(v_a_564_);
lean_dec_ref(v_a_563_);
lean_dec(v_a_562_);
lean_dec_ref(v_a_561_);
lean_dec(v_a_560_);
lean_dec_ref(v_a_559_);
lean_dec(v_a_558_);
lean_dec_ref(v_a_557_);
lean_dec(v_a_556_);
lean_dec(v_a_555_);
lean_dec_ref(v_a_554_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0(lean_object* v_00_u03b1_567_, lean_object* v_msg_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_){
_start:
{
lean_object* v___x_581_; 
v___x_581_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg(v_msg_568_, v___y_576_, v___y_577_, v___y_578_, v___y_579_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___boxed(lean_object* v_00_u03b1_582_, lean_object* v_msg_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0(v_00_u03b1_582_, v_msg_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_);
lean_dec(v___y_594_);
lean_dec_ref(v___y_593_);
lean_dec(v___y_592_);
lean_dec_ref(v___y_591_);
lean_dec(v___y_590_);
lean_dec_ref(v___y_589_);
lean_dec(v___y_588_);
lean_dec_ref(v___y_587_);
lean_dec(v___y_586_);
lean_dec(v___y_585_);
lean_dec_ref(v___y_584_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg___lam__0(lean_object* v_ringId_597_, lean_object* v_f_598_, lean_object* v_s_599_){
_start:
{
lean_object* v_rings_600_; lean_object* v_typeIdOf_601_; lean_object* v_exprToRingId_602_; lean_object* v_semirings_603_; lean_object* v_stypeIdOf_604_; lean_object* v_exprToSemiringId_605_; lean_object* v_ncRings_606_; lean_object* v_exprToNCRingId_607_; lean_object* v_nctypeIdOf_608_; lean_object* v_ncSemirings_609_; lean_object* v_exprToNCSemiringId_610_; lean_object* v_ncstypeIdOf_611_; lean_object* v_steps_612_; uint8_t v_reportedMaxDegreeIssue_613_; lean_object* v___x_614_; uint8_t v___x_615_; 
v_rings_600_ = lean_ctor_get(v_s_599_, 0);
v_typeIdOf_601_ = lean_ctor_get(v_s_599_, 1);
v_exprToRingId_602_ = lean_ctor_get(v_s_599_, 2);
v_semirings_603_ = lean_ctor_get(v_s_599_, 3);
v_stypeIdOf_604_ = lean_ctor_get(v_s_599_, 4);
v_exprToSemiringId_605_ = lean_ctor_get(v_s_599_, 5);
v_ncRings_606_ = lean_ctor_get(v_s_599_, 6);
v_exprToNCRingId_607_ = lean_ctor_get(v_s_599_, 7);
v_nctypeIdOf_608_ = lean_ctor_get(v_s_599_, 8);
v_ncSemirings_609_ = lean_ctor_get(v_s_599_, 9);
v_exprToNCSemiringId_610_ = lean_ctor_get(v_s_599_, 10);
v_ncstypeIdOf_611_ = lean_ctor_get(v_s_599_, 11);
v_steps_612_ = lean_ctor_get(v_s_599_, 12);
v_reportedMaxDegreeIssue_613_ = lean_ctor_get_uint8(v_s_599_, sizeof(void*)*13);
v___x_614_ = lean_array_get_size(v_rings_600_);
v___x_615_ = lean_nat_dec_lt(v_ringId_597_, v___x_614_);
if (v___x_615_ == 0)
{
lean_dec_ref(v_f_598_);
return v_s_599_;
}
else
{
lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_627_; 
lean_inc(v_steps_612_);
lean_inc_ref(v_ncstypeIdOf_611_);
lean_inc_ref(v_exprToNCSemiringId_610_);
lean_inc_ref(v_ncSemirings_609_);
lean_inc_ref(v_nctypeIdOf_608_);
lean_inc_ref(v_exprToNCRingId_607_);
lean_inc_ref(v_ncRings_606_);
lean_inc_ref(v_exprToSemiringId_605_);
lean_inc_ref(v_stypeIdOf_604_);
lean_inc_ref(v_semirings_603_);
lean_inc_ref(v_exprToRingId_602_);
lean_inc_ref(v_typeIdOf_601_);
lean_inc_ref(v_rings_600_);
v_isSharedCheck_627_ = !lean_is_exclusive(v_s_599_);
if (v_isSharedCheck_627_ == 0)
{
lean_object* v_unused_628_; lean_object* v_unused_629_; lean_object* v_unused_630_; lean_object* v_unused_631_; lean_object* v_unused_632_; lean_object* v_unused_633_; lean_object* v_unused_634_; lean_object* v_unused_635_; lean_object* v_unused_636_; lean_object* v_unused_637_; lean_object* v_unused_638_; lean_object* v_unused_639_; lean_object* v_unused_640_; 
v_unused_628_ = lean_ctor_get(v_s_599_, 12);
lean_dec(v_unused_628_);
v_unused_629_ = lean_ctor_get(v_s_599_, 11);
lean_dec(v_unused_629_);
v_unused_630_ = lean_ctor_get(v_s_599_, 10);
lean_dec(v_unused_630_);
v_unused_631_ = lean_ctor_get(v_s_599_, 9);
lean_dec(v_unused_631_);
v_unused_632_ = lean_ctor_get(v_s_599_, 8);
lean_dec(v_unused_632_);
v_unused_633_ = lean_ctor_get(v_s_599_, 7);
lean_dec(v_unused_633_);
v_unused_634_ = lean_ctor_get(v_s_599_, 6);
lean_dec(v_unused_634_);
v_unused_635_ = lean_ctor_get(v_s_599_, 5);
lean_dec(v_unused_635_);
v_unused_636_ = lean_ctor_get(v_s_599_, 4);
lean_dec(v_unused_636_);
v_unused_637_ = lean_ctor_get(v_s_599_, 3);
lean_dec(v_unused_637_);
v_unused_638_ = lean_ctor_get(v_s_599_, 2);
lean_dec(v_unused_638_);
v_unused_639_ = lean_ctor_get(v_s_599_, 1);
lean_dec(v_unused_639_);
v_unused_640_ = lean_ctor_get(v_s_599_, 0);
lean_dec(v_unused_640_);
v___x_617_ = v_s_599_;
v_isShared_618_ = v_isSharedCheck_627_;
goto v_resetjp_616_;
}
else
{
lean_dec(v_s_599_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_627_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v_v_619_; lean_object* v___x_620_; lean_object* v_xs_x27_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_625_; 
v_v_619_ = lean_array_fget(v_rings_600_, v_ringId_597_);
v___x_620_ = lean_box(0);
v_xs_x27_621_ = lean_array_fset(v_rings_600_, v_ringId_597_, v___x_620_);
v___x_622_ = lean_apply_1(v_f_598_, v_v_619_);
v___x_623_ = lean_array_fset(v_xs_x27_621_, v_ringId_597_, v___x_622_);
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 0, v___x_623_);
v___x_625_ = v___x_617_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v___x_623_);
lean_ctor_set(v_reuseFailAlloc_626_, 1, v_typeIdOf_601_);
lean_ctor_set(v_reuseFailAlloc_626_, 2, v_exprToRingId_602_);
lean_ctor_set(v_reuseFailAlloc_626_, 3, v_semirings_603_);
lean_ctor_set(v_reuseFailAlloc_626_, 4, v_stypeIdOf_604_);
lean_ctor_set(v_reuseFailAlloc_626_, 5, v_exprToSemiringId_605_);
lean_ctor_set(v_reuseFailAlloc_626_, 6, v_ncRings_606_);
lean_ctor_set(v_reuseFailAlloc_626_, 7, v_exprToNCRingId_607_);
lean_ctor_set(v_reuseFailAlloc_626_, 8, v_nctypeIdOf_608_);
lean_ctor_set(v_reuseFailAlloc_626_, 9, v_ncSemirings_609_);
lean_ctor_set(v_reuseFailAlloc_626_, 10, v_exprToNCSemiringId_610_);
lean_ctor_set(v_reuseFailAlloc_626_, 11, v_ncstypeIdOf_611_);
lean_ctor_set(v_reuseFailAlloc_626_, 12, v_steps_612_);
lean_ctor_set_uint8(v_reuseFailAlloc_626_, sizeof(void*)*13, v_reportedMaxDegreeIssue_613_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg___lam__0___boxed(lean_object* v_ringId_641_, lean_object* v_f_642_, lean_object* v_s_643_){
_start:
{
lean_object* v_res_644_; 
v_res_644_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg___lam__0(v_ringId_641_, v_f_642_, v_s_643_);
lean_dec(v_ringId_641_);
return v_res_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(lean_object* v_f_645_, lean_object* v_a_646_, lean_object* v_a_647_){
_start:
{
lean_object* v_ringId_649_; lean_object* v___f_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v_ringId_649_ = lean_ctor_get(v_a_646_, 0);
lean_inc(v_ringId_649_);
v___f_650_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_650_, 0, v_ringId_649_);
lean_closure_set(v___f_650_, 1, v_f_645_);
v___x_651_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_652_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_651_, v___f_650_, v_a_647_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg___boxed(lean_object* v_f_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v_f_653_, v_a_654_, v_a_655_);
lean_dec(v_a_655_);
lean_dec_ref(v_a_654_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing(lean_object* v_f_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_){
_start:
{
lean_object* v___x_671_; 
v___x_671_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v_f_658_, v_a_659_, v_a_660_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___boxed(lean_object* v_f_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing(v_f_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_, v_a_682_, v_a_683_);
lean_dec(v_a_683_);
lean_dec_ref(v_a_682_);
lean_dec(v_a_681_);
lean_dec_ref(v_a_680_);
lean_dec(v_a_679_);
lean_dec_ref(v_a_678_);
lean_dec(v_a_677_);
lean_dec_ref(v_a_676_);
lean_dec(v_a_675_);
lean_dec(v_a_674_);
lean_dec_ref(v_a_673_);
return v_res_685_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__1(void){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_687_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__0));
v___x_688_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing___boxed), 12, 0);
v___x_689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_689_, 0, v___x_688_);
lean_ctor_set(v___x_689_, 1, v___x_687_);
return v___x_689_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM(void){
_start:
{
lean_object* v___x_690_; 
v___x_690_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingRingM___closed__1);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd___redArg(lean_object* v_x_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_){
_start:
{
lean_object* v_ringId_704_; uint8_t v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
v_ringId_704_ = lean_ctor_get(v_a_692_, 0);
v___x_705_ = 1;
lean_inc(v_ringId_704_);
v___x_706_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_706_, 0, v_ringId_704_);
lean_ctor_set_uint8(v___x_706_, sizeof(void*)*1, v___x_705_);
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
v___x_707_ = lean_apply_12(v_x_691_, v___x_706_, v_a_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_, v_a_699_, v_a_700_, v_a_701_, v_a_702_, lean_box(0));
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd___redArg___boxed(lean_object* v_x_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd___redArg(v_x_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_);
lean_dec(v_a_719_);
lean_dec_ref(v_a_718_);
lean_dec(v_a_717_);
lean_dec_ref(v_a_716_);
lean_dec(v_a_715_);
lean_dec_ref(v_a_714_);
lean_dec(v_a_713_);
lean_dec_ref(v_a_712_);
lean_dec(v_a_711_);
lean_dec(v_a_710_);
lean_dec_ref(v_a_709_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd(lean_object* v_00_u03b1_722_, lean_object* v_x_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_){
_start:
{
lean_object* v_ringId_736_; uint8_t v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
v_ringId_736_ = lean_ctor_get(v_a_724_, 0);
v___x_737_ = 1;
lean_inc(v_ringId_736_);
v___x_738_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_738_, 0, v_ringId_736_);
lean_ctor_set_uint8(v___x_738_, sizeof(void*)*1, v___x_737_);
lean_inc(v_a_734_);
lean_inc_ref(v_a_733_);
lean_inc(v_a_732_);
lean_inc_ref(v_a_731_);
lean_inc(v_a_730_);
lean_inc_ref(v_a_729_);
lean_inc(v_a_728_);
lean_inc_ref(v_a_727_);
lean_inc(v_a_726_);
lean_inc(v_a_725_);
v___x_739_ = lean_apply_12(v_x_723_, v___x_738_, v_a_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_, lean_box(0));
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd___boxed(lean_object* v_00_u03b1_740_, lean_object* v_x_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l_Lean_Meta_Grind_Arith_CommRing_withCheckCoeffDvd(v_00_u03b1_740_, v_x_741_, v_a_742_, v_a_743_, v_a_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_);
lean_dec(v_a_752_);
lean_dec_ref(v_a_751_);
lean_dec(v_a_750_);
lean_dec_ref(v_a_749_);
lean_dec(v_a_748_);
lean_dec_ref(v_a_747_);
lean_dec(v_a_746_);
lean_dec_ref(v_a_745_);
lean_dec(v_a_744_);
lean_dec(v_a_743_);
lean_dec_ref(v_a_742_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___redArg(lean_object* v_a_755_){
_start:
{
uint8_t v_checkCoeffDvd_757_; lean_object* v___x_758_; lean_object* v___x_759_; 
v_checkCoeffDvd_757_ = lean_ctor_get_uint8(v_a_755_, sizeof(void*)*1);
v___x_758_ = lean_box(v_checkCoeffDvd_757_);
v___x_759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_759_, 0, v___x_758_);
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___redArg___boxed(lean_object* v_a_760_, lean_object* v_a_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___redArg(v_a_760_);
lean_dec_ref(v_a_760_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd(lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_){
_start:
{
lean_object* v___x_775_; 
v___x_775_ = l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___redArg(v_a_763_);
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd___boxed(lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_Lean_Meta_Grind_Arith_CommRing_checkCoeffDvd(v_a_776_, v_a_777_, v_a_778_, v_a_779_, v_a_780_, v_a_781_, v_a_782_, v_a_783_, v_a_784_, v_a_785_, v_a_786_);
lean_dec(v_a_786_);
lean_dec_ref(v_a_785_);
lean_dec(v_a_784_);
lean_dec_ref(v_a_783_);
lean_dec(v_a_782_);
lean_dec_ref(v_a_781_);
lean_dec(v_a_780_);
lean_dec_ref(v_a_779_);
lean_dec(v_a_778_);
lean_dec(v_a_777_);
lean_dec_ref(v_a_776_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_789_, lean_object* v_vals_790_, lean_object* v_i_791_, lean_object* v_k_792_){
_start:
{
lean_object* v___x_793_; uint8_t v___x_794_; 
v___x_793_ = lean_array_get_size(v_keys_789_);
v___x_794_ = lean_nat_dec_lt(v_i_791_, v___x_793_);
if (v___x_794_ == 0)
{
lean_object* v___x_795_; 
lean_dec(v_i_791_);
v___x_795_ = lean_box(0);
return v___x_795_;
}
else
{
lean_object* v_k_x27_796_; uint8_t v___x_797_; 
v_k_x27_796_ = lean_array_fget_borrowed(v_keys_789_, v_i_791_);
v___x_797_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_792_, v_k_x27_796_);
if (v___x_797_ == 0)
{
lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_798_ = lean_unsigned_to_nat(1u);
v___x_799_ = lean_nat_add(v_i_791_, v___x_798_);
lean_dec(v_i_791_);
v_i_791_ = v___x_799_;
goto _start;
}
else
{
lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_801_ = lean_array_fget_borrowed(v_vals_790_, v_i_791_);
lean_dec(v_i_791_);
lean_inc(v___x_801_);
v___x_802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_802_, 0, v___x_801_);
return v___x_802_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_803_, lean_object* v_vals_804_, lean_object* v_i_805_, lean_object* v_k_806_){
_start:
{
lean_object* v_res_807_; 
v_res_807_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_803_, v_vals_804_, v_i_805_, v_k_806_);
lean_dec_ref(v_k_806_);
lean_dec_ref(v_vals_804_);
lean_dec_ref(v_keys_803_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg(lean_object* v_x_808_, size_t v_x_809_, lean_object* v_x_810_){
_start:
{
if (lean_obj_tag(v_x_808_) == 0)
{
lean_object* v_es_811_; lean_object* v___x_812_; size_t v___x_813_; size_t v___x_814_; lean_object* v_j_815_; lean_object* v___x_816_; 
v_es_811_ = lean_ctor_get(v_x_808_, 0);
v___x_812_ = lean_box(2);
v___x_813_ = ((size_t)31ULL);
v___x_814_ = lean_usize_land(v_x_809_, v___x_813_);
v_j_815_ = lean_usize_to_nat(v___x_814_);
v___x_816_ = lean_array_get_borrowed(v___x_812_, v_es_811_, v_j_815_);
lean_dec(v_j_815_);
switch(lean_obj_tag(v___x_816_))
{
case 0:
{
lean_object* v_key_817_; lean_object* v_val_818_; uint8_t v___x_819_; 
v_key_817_ = lean_ctor_get(v___x_816_, 0);
v_val_818_ = lean_ctor_get(v___x_816_, 1);
v___x_819_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_810_, v_key_817_);
if (v___x_819_ == 0)
{
lean_object* v___x_820_; 
v___x_820_ = lean_box(0);
return v___x_820_;
}
else
{
lean_object* v___x_821_; 
lean_inc(v_val_818_);
v___x_821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_821_, 0, v_val_818_);
return v___x_821_;
}
}
case 1:
{
lean_object* v_node_822_; size_t v___x_823_; size_t v___x_824_; 
v_node_822_ = lean_ctor_get(v___x_816_, 0);
v___x_823_ = ((size_t)5ULL);
v___x_824_ = lean_usize_shift_right(v_x_809_, v___x_823_);
v_x_808_ = v_node_822_;
v_x_809_ = v___x_824_;
goto _start;
}
default: 
{
lean_object* v___x_826_; 
v___x_826_ = lean_box(0);
return v___x_826_;
}
}
}
else
{
lean_object* v_ks_827_; lean_object* v_vs_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
v_ks_827_ = lean_ctor_get(v_x_808_, 0);
v_vs_828_ = lean_ctor_get(v_x_808_, 1);
v___x_829_ = lean_unsigned_to_nat(0u);
v___x_830_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_827_, v_vs_828_, v___x_829_, v_x_810_);
return v___x_830_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_831_, lean_object* v_x_832_, lean_object* v_x_833_){
_start:
{
size_t v_x_851__boxed_834_; lean_object* v_res_835_; 
v_x_851__boxed_834_ = lean_unbox_usize(v_x_832_);
lean_dec(v_x_832_);
v_res_835_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg(v_x_831_, v_x_851__boxed_834_, v_x_833_);
lean_dec_ref(v_x_833_);
lean_dec_ref(v_x_831_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(lean_object* v_x_836_, lean_object* v_x_837_){
_start:
{
uint64_t v___x_838_; size_t v___x_839_; lean_object* v___x_840_; 
v___x_838_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_837_);
v___x_839_ = lean_uint64_to_usize(v___x_838_);
v___x_840_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg(v_x_836_, v___x_839_, v_x_837_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg___boxed(lean_object* v_x_841_, lean_object* v_x_842_){
_start:
{
lean_object* v_res_843_; 
v_res_843_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(v_x_841_, v_x_842_);
lean_dec_ref(v_x_842_);
lean_dec_ref(v_x_841_);
return v_res_843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg(lean_object* v_e_844_, lean_object* v_a_845_, lean_object* v_a_846_){
_start:
{
lean_object* v___x_848_; 
v___x_848_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_845_, v_a_846_);
if (lean_obj_tag(v___x_848_) == 0)
{
lean_object* v_a_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_858_; 
v_a_849_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_858_ == 0)
{
v___x_851_ = v___x_848_;
v_isShared_852_ = v_isSharedCheck_858_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_a_849_);
lean_dec(v___x_848_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_858_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v_exprToRingId_853_; lean_object* v___x_854_; lean_object* v___x_856_; 
v_exprToRingId_853_ = lean_ctor_get(v_a_849_, 2);
lean_inc_ref(v_exprToRingId_853_);
lean_dec(v_a_849_);
v___x_854_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(v_exprToRingId_853_, v_e_844_);
lean_dec_ref(v_exprToRingId_853_);
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 0, v___x_854_);
v___x_856_ = v___x_851_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v___x_854_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
}
else
{
lean_object* v_a_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_866_; 
v_a_859_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_866_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_866_ == 0)
{
v___x_861_ = v___x_848_;
v_isShared_862_ = v_isSharedCheck_866_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_a_859_);
lean_dec(v___x_848_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_866_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v___x_864_; 
if (v_isShared_862_ == 0)
{
v___x_864_ = v___x_861_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v_a_859_);
v___x_864_ = v_reuseFailAlloc_865_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
return v___x_864_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg___boxed(lean_object* v_e_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg(v_e_867_, v_a_868_, v_a_869_);
lean_dec_ref(v_a_869_);
lean_dec(v_a_868_);
lean_dec_ref(v_e_867_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f(lean_object* v_e_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_){
_start:
{
lean_object* v___x_884_; 
v___x_884_ = l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg(v_e_872_, v_a_873_, v_a_881_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___boxed(lean_object* v_e_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_){
_start:
{
lean_object* v_res_897_; 
v_res_897_ = l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f(v_e_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_);
lean_dec(v_a_895_);
lean_dec_ref(v_a_894_);
lean_dec(v_a_893_);
lean_dec_ref(v_a_892_);
lean_dec(v_a_891_);
lean_dec_ref(v_a_890_);
lean_dec(v_a_889_);
lean_dec_ref(v_a_888_);
lean_dec(v_a_887_);
lean_dec(v_a_886_);
lean_dec_ref(v_e_885_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0(lean_object* v_00_u03b2_898_, lean_object* v_x_899_, lean_object* v_x_900_){
_start:
{
lean_object* v___x_901_; 
v___x_901_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(v_x_899_, v_x_900_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___boxed(lean_object* v_00_u03b2_902_, lean_object* v_x_903_, lean_object* v_x_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0(v_00_u03b2_902_, v_x_903_, v_x_904_);
lean_dec_ref(v_x_904_);
lean_dec_ref(v_x_903_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_906_, lean_object* v_x_907_, size_t v_x_908_, lean_object* v_x_909_){
_start:
{
lean_object* v___x_910_; 
v___x_910_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg(v_x_907_, v_x_908_, v_x_909_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_911_, lean_object* v_x_912_, lean_object* v_x_913_, lean_object* v_x_914_){
_start:
{
size_t v_x_962__boxed_915_; lean_object* v_res_916_; 
v_x_962__boxed_915_ = lean_unbox_usize(v_x_913_);
lean_dec(v_x_913_);
v_res_916_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0(v_00_u03b2_911_, v_x_912_, v_x_962__boxed_915_, v_x_914_);
lean_dec_ref(v_x_914_);
lean_dec_ref(v_x_912_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_917_, lean_object* v_keys_918_, lean_object* v_vals_919_, lean_object* v_heq_920_, lean_object* v_i_921_, lean_object* v_k_922_){
_start:
{
lean_object* v___x_923_; 
v___x_923_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_918_, v_vals_919_, v_i_921_, v_k_922_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_924_, lean_object* v_keys_925_, lean_object* v_vals_926_, lean_object* v_heq_927_, lean_object* v_i_928_, lean_object* v_k_929_){
_start:
{
lean_object* v_res_930_; 
v_res_930_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_924_, v_keys_925_, v_vals_926_, v_heq_927_, v_i_928_, v_k_929_);
lean_dec_ref(v_k_929_);
lean_dec_ref(v_vals_926_);
lean_dec_ref(v_keys_925_);
return v_res_930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg___lam__0(lean_object* v_toPure_931_, lean_object* v_____do__lift_932_){
_start:
{
lean_object* v_charInst_x3f_936_; 
v_charInst_x3f_936_ = lean_ctor_get(v_____do__lift_932_, 5);
lean_inc(v_charInst_x3f_936_);
lean_dec_ref(v_____do__lift_932_);
if (lean_obj_tag(v_charInst_x3f_936_) == 1)
{
lean_object* v_val_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_948_; 
v_val_937_ = lean_ctor_get(v_charInst_x3f_936_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v_charInst_x3f_936_);
if (v_isSharedCheck_948_ == 0)
{
v___x_939_ = v_charInst_x3f_936_;
v_isShared_940_ = v_isSharedCheck_948_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_val_937_);
lean_dec(v_charInst_x3f_936_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_948_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v_snd_941_; lean_object* v___x_942_; uint8_t v___x_943_; 
v_snd_941_ = lean_ctor_get(v_val_937_, 1);
lean_inc(v_snd_941_);
lean_dec(v_val_937_);
v___x_942_ = lean_unsigned_to_nat(0u);
v___x_943_ = lean_nat_dec_eq(v_snd_941_, v___x_942_);
if (v___x_943_ == 0)
{
lean_object* v___x_945_; 
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 0, v_snd_941_);
v___x_945_ = v___x_939_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_snd_941_);
v___x_945_ = v_reuseFailAlloc_947_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
lean_object* v___x_946_; 
v___x_946_ = lean_apply_2(v_toPure_931_, lean_box(0), v___x_945_);
return v___x_946_;
}
}
else
{
lean_dec(v_snd_941_);
lean_del_object(v___x_939_);
goto v___jp_933_;
}
}
}
else
{
lean_dec(v_charInst_x3f_936_);
goto v___jp_933_;
}
v___jp_933_:
{
lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_934_ = lean_box(0);
v___x_935_ = lean_apply_2(v_toPure_931_, lean_box(0), v___x_934_);
return v___x_935_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg(lean_object* v_inst_949_, lean_object* v_inst_950_){
_start:
{
lean_object* v_toApplicative_951_; lean_object* v_toBind_952_; lean_object* v_getRing_953_; lean_object* v_toPure_954_; lean_object* v___f_955_; lean_object* v___x_956_; 
v_toApplicative_951_ = lean_ctor_get(v_inst_949_, 0);
lean_inc_ref(v_toApplicative_951_);
v_toBind_952_ = lean_ctor_get(v_inst_949_, 1);
lean_inc(v_toBind_952_);
lean_dec_ref(v_inst_949_);
v_getRing_953_ = lean_ctor_get(v_inst_950_, 0);
lean_inc(v_getRing_953_);
lean_dec_ref(v_inst_950_);
v_toPure_954_ = lean_ctor_get(v_toApplicative_951_, 1);
lean_inc(v_toPure_954_);
lean_dec_ref(v_toApplicative_951_);
v___f_955_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_955_, 0, v_toPure_954_);
v___x_956_ = lean_apply_4(v_toBind_952_, lean_box(0), lean_box(0), v_getRing_953_, v___f_955_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f(lean_object* v_m_957_, lean_object* v_inst_958_, lean_object* v_inst_959_){
_start:
{
lean_object* v___x_960_; 
v___x_960_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg(v_inst_958_, v_inst_959_);
return v___x_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f___redArg___lam__0(lean_object* v_toPure_961_, lean_object* v_____do__lift_962_){
_start:
{
lean_object* v_charInst_x3f_966_; 
v_charInst_x3f_966_ = lean_ctor_get(v_____do__lift_962_, 5);
lean_inc(v_charInst_x3f_966_);
lean_dec_ref(v_____do__lift_962_);
if (lean_obj_tag(v_charInst_x3f_966_) == 1)
{
lean_object* v_val_967_; lean_object* v_snd_968_; lean_object* v___x_969_; uint8_t v___x_970_; 
v_val_967_ = lean_ctor_get(v_charInst_x3f_966_, 0);
v_snd_968_ = lean_ctor_get(v_val_967_, 1);
v___x_969_ = lean_unsigned_to_nat(0u);
v___x_970_ = lean_nat_dec_eq(v_snd_968_, v___x_969_);
if (v___x_970_ == 0)
{
lean_object* v___x_971_; 
v___x_971_ = lean_apply_2(v_toPure_961_, lean_box(0), v_charInst_x3f_966_);
return v___x_971_;
}
else
{
lean_dec_ref_known(v_charInst_x3f_966_, 1);
goto v___jp_963_;
}
}
else
{
lean_dec(v_charInst_x3f_966_);
goto v___jp_963_;
}
v___jp_963_:
{
lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_964_ = lean_box(0);
v___x_965_ = lean_apply_2(v_toPure_961_, lean_box(0), v___x_964_);
return v___x_965_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f___redArg(lean_object* v_inst_972_, lean_object* v_inst_973_){
_start:
{
lean_object* v_toApplicative_974_; lean_object* v_toBind_975_; lean_object* v_getRing_976_; lean_object* v_toPure_977_; lean_object* v___f_978_; lean_object* v___x_979_; 
v_toApplicative_974_ = lean_ctor_get(v_inst_972_, 0);
lean_inc_ref(v_toApplicative_974_);
v_toBind_975_ = lean_ctor_get(v_inst_972_, 1);
lean_inc(v_toBind_975_);
lean_dec_ref(v_inst_972_);
v_getRing_976_ = lean_ctor_get(v_inst_973_, 0);
lean_inc(v_getRing_976_);
lean_dec_ref(v_inst_973_);
v_toPure_977_ = lean_ctor_get(v_toApplicative_974_, 1);
lean_inc(v_toPure_977_);
lean_dec_ref(v_toApplicative_974_);
v___f_978_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_978_, 0, v_toPure_977_);
v___x_979_ = lean_apply_4(v_toBind_975_, lean_box(0), lean_box(0), v_getRing_976_, v___f_978_);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f(lean_object* v_m_980_, lean_object* v_inst_981_, lean_object* v_inst_982_){
_start:
{
lean_object* v___x_983_; 
v___x_983_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f___redArg(v_inst_981_, v_inst_982_);
return v___x_983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisorsInst_x3f(lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_){
_start:
{
lean_object* v___x_996_; 
v___x_996_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_);
if (lean_obj_tag(v___x_996_) == 0)
{
lean_object* v_a_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1005_; 
v_a_997_ = lean_ctor_get(v___x_996_, 0);
v_isSharedCheck_1005_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1005_ == 0)
{
v___x_999_ = v___x_996_;
v_isShared_1000_ = v_isSharedCheck_1005_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_a_997_);
lean_dec(v___x_996_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1005_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v_noZeroDivInst_x3f_1001_; lean_object* v___x_1003_; 
v_noZeroDivInst_x3f_1001_ = lean_ctor_get(v_a_997_, 5);
lean_inc(v_noZeroDivInst_x3f_1001_);
lean_dec(v_a_997_);
if (v_isShared_1000_ == 0)
{
lean_ctor_set(v___x_999_, 0, v_noZeroDivInst_x3f_1001_);
v___x_1003_ = v___x_999_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v_noZeroDivInst_x3f_1001_);
v___x_1003_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
return v___x_1003_;
}
}
}
else
{
lean_object* v_a_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1013_; 
v_a_1006_ = lean_ctor_get(v___x_996_, 0);
v_isSharedCheck_1013_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_1008_ = v___x_996_;
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_a_1006_);
lean_dec(v___x_996_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1013_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1011_; 
if (v_isShared_1009_ == 0)
{
v___x_1011_ = v___x_1008_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v_a_1006_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisorsInst_x3f___boxed(lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_){
_start:
{
lean_object* v_res_1026_; 
v_res_1026_ = l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisorsInst_x3f(v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_);
lean_dec(v_a_1024_);
lean_dec_ref(v_a_1023_);
lean_dec(v_a_1022_);
lean_dec_ref(v_a_1021_);
lean_dec(v_a_1020_);
lean_dec_ref(v_a_1019_);
lean_dec(v_a_1018_);
lean_dec_ref(v_a_1017_);
lean_dec(v_a_1016_);
lean_dec(v_a_1015_);
lean_dec_ref(v_a_1014_);
return v_res_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisors(lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_){
_start:
{
lean_object* v___x_1039_; 
v___x_1039_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_);
if (lean_obj_tag(v___x_1039_) == 0)
{
lean_object* v_a_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1055_; 
v_a_1040_ = lean_ctor_get(v___x_1039_, 0);
v_isSharedCheck_1055_ = !lean_is_exclusive(v___x_1039_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1042_ = v___x_1039_;
v_isShared_1043_ = v_isSharedCheck_1055_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_a_1040_);
lean_dec(v___x_1039_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1055_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v_noZeroDivInst_x3f_1044_; 
v_noZeroDivInst_x3f_1044_ = lean_ctor_get(v_a_1040_, 5);
lean_inc(v_noZeroDivInst_x3f_1044_);
lean_dec(v_a_1040_);
if (lean_obj_tag(v_noZeroDivInst_x3f_1044_) == 0)
{
uint8_t v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1048_; 
v___x_1045_ = 0;
v___x_1046_ = lean_box(v___x_1045_);
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 0, v___x_1046_);
v___x_1048_ = v___x_1042_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v___x_1046_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
return v___x_1048_;
}
}
else
{
uint8_t v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1053_; 
lean_dec_ref_known(v_noZeroDivInst_x3f_1044_, 1);
v___x_1050_ = 1;
v___x_1051_ = lean_box(v___x_1050_);
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 0, v___x_1051_);
v___x_1053_ = v___x_1042_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v___x_1051_);
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
else
{
lean_object* v_a_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1063_; 
v_a_1056_ = lean_ctor_get(v___x_1039_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1039_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1058_ = v___x_1039_;
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_a_1056_);
lean_dec(v___x_1039_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1061_; 
if (v_isShared_1059_ == 0)
{
v___x_1061_ = v___x_1058_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_a_1056_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisors___boxed(lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_){
_start:
{
lean_object* v_res_1076_; 
v_res_1076_ = l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisors(v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_);
lean_dec(v_a_1074_);
lean_dec_ref(v_a_1073_);
lean_dec(v_a_1072_);
lean_dec_ref(v_a_1071_);
lean_dec(v_a_1070_);
lean_dec_ref(v_a_1069_);
lean_dec(v_a_1068_);
lean_dec_ref(v_a_1067_);
lean_dec(v_a_1066_);
lean_dec(v_a_1065_);
lean_dec_ref(v_a_1064_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_hasChar(lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_){
_start:
{
lean_object* v___x_1089_; 
v___x_1089_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_);
if (lean_obj_tag(v___x_1089_) == 0)
{
lean_object* v_a_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1106_; 
v_a_1090_ = lean_ctor_get(v___x_1089_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1092_ = v___x_1089_;
v_isShared_1093_ = v_isSharedCheck_1106_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_a_1090_);
lean_dec(v___x_1089_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1106_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v_toRing_1094_; lean_object* v_charInst_x3f_1095_; 
v_toRing_1094_ = lean_ctor_get(v_a_1090_, 0);
lean_inc_ref(v_toRing_1094_);
lean_dec(v_a_1090_);
v_charInst_x3f_1095_ = lean_ctor_get(v_toRing_1094_, 5);
lean_inc(v_charInst_x3f_1095_);
lean_dec_ref(v_toRing_1094_);
if (lean_obj_tag(v_charInst_x3f_1095_) == 0)
{
uint8_t v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1099_; 
v___x_1096_ = 0;
v___x_1097_ = lean_box(v___x_1096_);
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 0, v___x_1097_);
v___x_1099_ = v___x_1092_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v___x_1097_);
v___x_1099_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
return v___x_1099_;
}
}
else
{
uint8_t v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1104_; 
lean_dec_ref_known(v_charInst_x3f_1095_, 1);
v___x_1101_ = 1;
v___x_1102_ = lean_box(v___x_1101_);
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 0, v___x_1102_);
v___x_1104_ = v___x_1092_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v___x_1102_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
return v___x_1104_;
}
}
}
}
else
{
lean_object* v_a_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1114_; 
v_a_1107_ = lean_ctor_get(v___x_1089_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1109_ = v___x_1089_;
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_a_1107_);
lean_dec(v___x_1089_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1112_; 
if (v_isShared_1110_ == 0)
{
v___x_1112_ = v___x_1109_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_a_1107_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_hasChar___boxed(lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_){
_start:
{
lean_object* v_res_1127_; 
v_res_1127_ = l_Lean_Meta_Grind_Arith_CommRing_hasChar(v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_);
lean_dec(v_a_1125_);
lean_dec_ref(v_a_1124_);
lean_dec(v_a_1123_);
lean_dec_ref(v_a_1122_);
lean_dec(v_a_1121_);
lean_dec_ref(v_a_1120_);
lean_dec(v_a_1119_);
lean_dec_ref(v_a_1118_);
lean_dec(v_a_1117_);
lean_dec(v_a_1116_);
lean_dec_ref(v_a_1115_);
return v_res_1127_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__1(void){
_start:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1129_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__0));
v___x_1130_ = l_Lean_stringToMessageData(v___x_1129_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCharInst(lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_){
_start:
{
lean_object* v___x_1143_; 
v___x_1143_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1131_, v_a_1132_, v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_);
if (lean_obj_tag(v___x_1143_) == 0)
{
lean_object* v_a_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1156_; 
v_a_1144_ = lean_ctor_get(v___x_1143_, 0);
v_isSharedCheck_1156_ = !lean_is_exclusive(v___x_1143_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1146_ = v___x_1143_;
v_isShared_1147_ = v_isSharedCheck_1156_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_a_1144_);
lean_dec(v___x_1143_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1156_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v_toRing_1148_; lean_object* v_charInst_x3f_1149_; 
v_toRing_1148_ = lean_ctor_get(v_a_1144_, 0);
lean_inc_ref(v_toRing_1148_);
lean_dec(v_a_1144_);
v_charInst_x3f_1149_ = lean_ctor_get(v_toRing_1148_, 5);
lean_inc(v_charInst_x3f_1149_);
lean_dec_ref(v_toRing_1148_);
if (lean_obj_tag(v_charInst_x3f_1149_) == 1)
{
lean_object* v_val_1150_; lean_object* v___x_1152_; 
v_val_1150_ = lean_ctor_get(v_charInst_x3f_1149_, 0);
lean_inc(v_val_1150_);
lean_dec_ref_known(v_charInst_x3f_1149_, 1);
if (v_isShared_1147_ == 0)
{
lean_ctor_set(v___x_1146_, 0, v_val_1150_);
v___x_1152_ = v___x_1146_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_val_1150_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
else
{
lean_object* v___x_1154_; lean_object* v___x_1155_; 
lean_dec(v_charInst_x3f_1149_);
lean_del_object(v___x_1146_);
v___x_1154_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__1);
v___x_1155_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg(v___x_1154_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_);
return v___x_1155_;
}
}
}
else
{
lean_object* v_a_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1164_; 
v_a_1157_ = lean_ctor_get(v___x_1143_, 0);
v_isSharedCheck_1164_ = !lean_is_exclusive(v___x_1143_);
if (v_isSharedCheck_1164_ == 0)
{
v___x_1159_ = v___x_1143_;
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_a_1157_);
lean_dec(v___x_1143_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1162_; 
if (v_isShared_1160_ == 0)
{
v___x_1162_ = v___x_1159_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v_a_1157_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCharInst___boxed(lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_){
_start:
{
lean_object* v_res_1177_; 
v_res_1177_ = l_Lean_Meta_Grind_Arith_CommRing_getCharInst(v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_);
lean_dec(v_a_1175_);
lean_dec_ref(v_a_1174_);
lean_dec(v_a_1173_);
lean_dec_ref(v_a_1172_);
lean_dec(v_a_1171_);
lean_dec_ref(v_a_1170_);
lean_dec(v_a_1169_);
lean_dec_ref(v_a_1168_);
lean_dec(v_a_1167_);
lean_dec(v_a_1166_);
lean_dec_ref(v_a_1165_);
return v_res_1177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isField(lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_){
_start:
{
lean_object* v___x_1190_; 
v___x_1190_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_);
if (lean_obj_tag(v___x_1190_) == 0)
{
lean_object* v_a_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1206_; 
v_a_1191_ = lean_ctor_get(v___x_1190_, 0);
v_isSharedCheck_1206_ = !lean_is_exclusive(v___x_1190_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1193_ = v___x_1190_;
v_isShared_1194_ = v_isSharedCheck_1206_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_a_1191_);
lean_dec(v___x_1190_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1206_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v_fieldInst_x3f_1195_; 
v_fieldInst_x3f_1195_ = lean_ctor_get(v_a_1191_, 6);
lean_inc(v_fieldInst_x3f_1195_);
lean_dec(v_a_1191_);
if (lean_obj_tag(v_fieldInst_x3f_1195_) == 0)
{
uint8_t v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1199_; 
v___x_1196_ = 0;
v___x_1197_ = lean_box(v___x_1196_);
if (v_isShared_1194_ == 0)
{
lean_ctor_set(v___x_1193_, 0, v___x_1197_);
v___x_1199_ = v___x_1193_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v___x_1197_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
else
{
uint8_t v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1204_; 
lean_dec_ref_known(v_fieldInst_x3f_1195_, 1);
v___x_1201_ = 1;
v___x_1202_ = lean_box(v___x_1201_);
if (v_isShared_1194_ == 0)
{
lean_ctor_set(v___x_1193_, 0, v___x_1202_);
v___x_1204_ = v___x_1193_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v___x_1202_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
return v___x_1204_;
}
}
}
}
else
{
lean_object* v_a_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1214_; 
v_a_1207_ = lean_ctor_get(v___x_1190_, 0);
v_isSharedCheck_1214_ = !lean_is_exclusive(v___x_1190_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1209_ = v___x_1190_;
v_isShared_1210_ = v_isSharedCheck_1214_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_a_1207_);
lean_dec(v___x_1190_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1214_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v___x_1212_; 
if (v_isShared_1210_ == 0)
{
v___x_1212_ = v___x_1209_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_a_1207_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isField___boxed(lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_){
_start:
{
lean_object* v_res_1227_; 
v_res_1227_ = l_Lean_Meta_Grind_Arith_CommRing_isField(v_a_1215_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_, v_a_1221_, v_a_1222_, v_a_1223_, v_a_1224_, v_a_1225_);
lean_dec(v_a_1225_);
lean_dec_ref(v_a_1224_);
lean_dec(v_a_1223_);
lean_dec_ref(v_a_1222_);
lean_dec(v_a_1221_);
lean_dec_ref(v_a_1220_);
lean_dec(v_a_1219_);
lean_dec_ref(v_a_1218_);
lean_dec(v_a_1217_);
lean_dec(v_a_1216_);
lean_dec_ref(v_a_1215_);
return v_res_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty(lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_){
_start:
{
lean_object* v___x_1240_; 
v___x_1240_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_, v_a_1232_, v_a_1233_, v_a_1234_, v_a_1235_, v_a_1236_, v_a_1237_, v_a_1238_);
if (lean_obj_tag(v___x_1240_) == 0)
{
lean_object* v_a_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1256_; 
v_a_1241_ = lean_ctor_get(v___x_1240_, 0);
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1243_ = v___x_1240_;
v_isShared_1244_ = v_isSharedCheck_1256_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_a_1241_);
lean_dec(v___x_1240_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1256_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v_queue_1245_; 
v_queue_1245_ = lean_ctor_get(v_a_1241_, 11);
lean_inc(v_queue_1245_);
lean_dec(v_a_1241_);
if (lean_obj_tag(v_queue_1245_) == 0)
{
uint8_t v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1249_; 
lean_dec_ref_known(v_queue_1245_, 5);
v___x_1246_ = 0;
v___x_1247_ = lean_box(v___x_1246_);
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 0, v___x_1247_);
v___x_1249_ = v___x_1243_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v___x_1247_);
v___x_1249_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
return v___x_1249_;
}
}
else
{
uint8_t v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1254_; 
v___x_1251_ = 1;
v___x_1252_ = lean_box(v___x_1251_);
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 0, v___x_1252_);
v___x_1254_ = v___x_1243_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v___x_1252_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
}
}
}
}
else
{
lean_object* v_a_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1264_; 
v_a_1257_ = lean_ctor_get(v___x_1240_, 0);
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1259_ = v___x_1240_;
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_a_1257_);
lean_dec(v___x_1240_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1262_; 
if (v_isShared_1260_ == 0)
{
v___x_1262_ = v___x_1259_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v_a_1257_);
v___x_1262_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
return v___x_1262_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty___boxed(lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_){
_start:
{
lean_object* v_res_1277_; 
v_res_1277_ = l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty(v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_);
lean_dec(v_a_1275_);
lean_dec_ref(v_a_1274_);
lean_dec(v_a_1273_);
lean_dec_ref(v_a_1272_);
lean_dec(v_a_1271_);
lean_dec_ref(v_a_1270_);
lean_dec(v_a_1269_);
lean_dec_ref(v_a_1268_);
lean_dec(v_a_1267_);
lean_dec(v_a_1266_);
lean_dec_ref(v_a_1265_);
return v_res_1277_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(lean_object* v_k_1278_, lean_object* v_t_1279_){
_start:
{
if (lean_obj_tag(v_t_1279_) == 0)
{
lean_object* v_k_1280_; lean_object* v_v_1281_; lean_object* v_l_1282_; lean_object* v_r_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1937_; 
v_k_1280_ = lean_ctor_get(v_t_1279_, 1);
v_v_1281_ = lean_ctor_get(v_t_1279_, 2);
v_l_1282_ = lean_ctor_get(v_t_1279_, 3);
v_r_1283_ = lean_ctor_get(v_t_1279_, 4);
v_isSharedCheck_1937_ = !lean_is_exclusive(v_t_1279_);
if (v_isSharedCheck_1937_ == 0)
{
lean_object* v_unused_1938_; 
v_unused_1938_ = lean_ctor_get(v_t_1279_, 0);
lean_dec(v_unused_1938_);
v___x_1285_ = v_t_1279_;
v_isShared_1286_ = v_isSharedCheck_1937_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_r_1283_);
lean_inc(v_l_1282_);
lean_inc(v_v_1281_);
lean_inc(v_k_1280_);
lean_dec(v_t_1279_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1937_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
uint8_t v___x_1287_; 
v___x_1287_ = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_compare(v_k_1278_, v_k_1280_);
switch(v___x_1287_)
{
case 0:
{
lean_object* v_impl_1288_; lean_object* v___x_1289_; 
v_impl_1288_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_k_1278_, v_l_1282_);
v___x_1289_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1288_) == 0)
{
if (lean_obj_tag(v_r_1283_) == 0)
{
lean_object* v_size_1290_; lean_object* v_size_1291_; lean_object* v_k_1292_; lean_object* v_v_1293_; lean_object* v_l_1294_; lean_object* v_r_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; uint8_t v___x_1298_; 
v_size_1290_ = lean_ctor_get(v_impl_1288_, 0);
lean_inc(v_size_1290_);
v_size_1291_ = lean_ctor_get(v_r_1283_, 0);
v_k_1292_ = lean_ctor_get(v_r_1283_, 1);
v_v_1293_ = lean_ctor_get(v_r_1283_, 2);
v_l_1294_ = lean_ctor_get(v_r_1283_, 3);
lean_inc(v_l_1294_);
v_r_1295_ = lean_ctor_get(v_r_1283_, 4);
v___x_1296_ = lean_unsigned_to_nat(3u);
v___x_1297_ = lean_nat_mul(v___x_1296_, v_size_1290_);
v___x_1298_ = lean_nat_dec_lt(v___x_1297_, v_size_1291_);
lean_dec(v___x_1297_);
if (v___x_1298_ == 0)
{
lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1302_; 
lean_dec(v_l_1294_);
v___x_1299_ = lean_nat_add(v___x_1289_, v_size_1290_);
lean_dec(v_size_1290_);
v___x_1300_ = lean_nat_add(v___x_1299_, v_size_1291_);
lean_dec(v___x_1299_);
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 3, v_impl_1288_);
lean_ctor_set(v___x_1285_, 0, v___x_1300_);
v___x_1302_ = v___x_1285_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v___x_1300_);
lean_ctor_set(v_reuseFailAlloc_1303_, 1, v_k_1280_);
lean_ctor_set(v_reuseFailAlloc_1303_, 2, v_v_1281_);
lean_ctor_set(v_reuseFailAlloc_1303_, 3, v_impl_1288_);
lean_ctor_set(v_reuseFailAlloc_1303_, 4, v_r_1283_);
v___x_1302_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
return v___x_1302_;
}
}
else
{
lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1367_; 
lean_inc(v_r_1295_);
lean_inc(v_v_1293_);
lean_inc(v_k_1292_);
lean_inc(v_size_1291_);
v_isSharedCheck_1367_ = !lean_is_exclusive(v_r_1283_);
if (v_isSharedCheck_1367_ == 0)
{
lean_object* v_unused_1368_; lean_object* v_unused_1369_; lean_object* v_unused_1370_; lean_object* v_unused_1371_; lean_object* v_unused_1372_; 
v_unused_1368_ = lean_ctor_get(v_r_1283_, 4);
lean_dec(v_unused_1368_);
v_unused_1369_ = lean_ctor_get(v_r_1283_, 3);
lean_dec(v_unused_1369_);
v_unused_1370_ = lean_ctor_get(v_r_1283_, 2);
lean_dec(v_unused_1370_);
v_unused_1371_ = lean_ctor_get(v_r_1283_, 1);
lean_dec(v_unused_1371_);
v_unused_1372_ = lean_ctor_get(v_r_1283_, 0);
lean_dec(v_unused_1372_);
v___x_1305_ = v_r_1283_;
v_isShared_1306_ = v_isSharedCheck_1367_;
goto v_resetjp_1304_;
}
else
{
lean_dec(v_r_1283_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1367_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v_size_1307_; lean_object* v_k_1308_; lean_object* v_v_1309_; lean_object* v_l_1310_; lean_object* v_r_1311_; lean_object* v_size_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; uint8_t v___x_1315_; 
v_size_1307_ = lean_ctor_get(v_l_1294_, 0);
v_k_1308_ = lean_ctor_get(v_l_1294_, 1);
v_v_1309_ = lean_ctor_get(v_l_1294_, 2);
v_l_1310_ = lean_ctor_get(v_l_1294_, 3);
v_r_1311_ = lean_ctor_get(v_l_1294_, 4);
v_size_1312_ = lean_ctor_get(v_r_1295_, 0);
v___x_1313_ = lean_unsigned_to_nat(2u);
v___x_1314_ = lean_nat_mul(v___x_1313_, v_size_1312_);
v___x_1315_ = lean_nat_dec_lt(v_size_1307_, v___x_1314_);
lean_dec(v___x_1314_);
if (v___x_1315_ == 0)
{
lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1343_; 
lean_inc(v_r_1311_);
lean_inc(v_l_1310_);
lean_inc(v_v_1309_);
lean_inc(v_k_1308_);
v_isSharedCheck_1343_ = !lean_is_exclusive(v_l_1294_);
if (v_isSharedCheck_1343_ == 0)
{
lean_object* v_unused_1344_; lean_object* v_unused_1345_; lean_object* v_unused_1346_; lean_object* v_unused_1347_; lean_object* v_unused_1348_; 
v_unused_1344_ = lean_ctor_get(v_l_1294_, 4);
lean_dec(v_unused_1344_);
v_unused_1345_ = lean_ctor_get(v_l_1294_, 3);
lean_dec(v_unused_1345_);
v_unused_1346_ = lean_ctor_get(v_l_1294_, 2);
lean_dec(v_unused_1346_);
v_unused_1347_ = lean_ctor_get(v_l_1294_, 1);
lean_dec(v_unused_1347_);
v_unused_1348_ = lean_ctor_get(v_l_1294_, 0);
lean_dec(v_unused_1348_);
v___x_1317_ = v_l_1294_;
v_isShared_1318_ = v_isSharedCheck_1343_;
goto v_resetjp_1316_;
}
else
{
lean_dec(v_l_1294_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1343_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___y_1322_; lean_object* v___y_1323_; lean_object* v___y_1324_; lean_object* v___y_1333_; 
v___x_1319_ = lean_nat_add(v___x_1289_, v_size_1290_);
lean_dec(v_size_1290_);
v___x_1320_ = lean_nat_add(v___x_1319_, v_size_1291_);
lean_dec(v_size_1291_);
if (lean_obj_tag(v_l_1310_) == 0)
{
lean_object* v_size_1341_; 
v_size_1341_ = lean_ctor_get(v_l_1310_, 0);
lean_inc(v_size_1341_);
v___y_1333_ = v_size_1341_;
goto v___jp_1332_;
}
else
{
lean_object* v___x_1342_; 
v___x_1342_ = lean_unsigned_to_nat(0u);
v___y_1333_ = v___x_1342_;
goto v___jp_1332_;
}
v___jp_1321_:
{
lean_object* v___x_1325_; lean_object* v___x_1327_; 
v___x_1325_ = lean_nat_add(v___y_1323_, v___y_1324_);
lean_dec(v___y_1324_);
lean_dec(v___y_1323_);
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 4, v_r_1295_);
lean_ctor_set(v___x_1317_, 3, v_r_1311_);
lean_ctor_set(v___x_1317_, 2, v_v_1293_);
lean_ctor_set(v___x_1317_, 1, v_k_1292_);
lean_ctor_set(v___x_1317_, 0, v___x_1325_);
v___x_1327_ = v___x_1317_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v___x_1325_);
lean_ctor_set(v_reuseFailAlloc_1331_, 1, v_k_1292_);
lean_ctor_set(v_reuseFailAlloc_1331_, 2, v_v_1293_);
lean_ctor_set(v_reuseFailAlloc_1331_, 3, v_r_1311_);
lean_ctor_set(v_reuseFailAlloc_1331_, 4, v_r_1295_);
v___x_1327_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
lean_object* v___x_1329_; 
if (v_isShared_1306_ == 0)
{
lean_ctor_set(v___x_1305_, 4, v___x_1327_);
lean_ctor_set(v___x_1305_, 3, v___y_1322_);
lean_ctor_set(v___x_1305_, 2, v_v_1309_);
lean_ctor_set(v___x_1305_, 1, v_k_1308_);
lean_ctor_set(v___x_1305_, 0, v___x_1320_);
v___x_1329_ = v___x_1305_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v___x_1320_);
lean_ctor_set(v_reuseFailAlloc_1330_, 1, v_k_1308_);
lean_ctor_set(v_reuseFailAlloc_1330_, 2, v_v_1309_);
lean_ctor_set(v_reuseFailAlloc_1330_, 3, v___y_1322_);
lean_ctor_set(v_reuseFailAlloc_1330_, 4, v___x_1327_);
v___x_1329_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
return v___x_1329_;
}
}
}
v___jp_1332_:
{
lean_object* v___x_1334_; lean_object* v___x_1336_; 
v___x_1334_ = lean_nat_add(v___x_1319_, v___y_1333_);
lean_dec(v___y_1333_);
lean_dec(v___x_1319_);
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 4, v_l_1310_);
lean_ctor_set(v___x_1285_, 3, v_impl_1288_);
lean_ctor_set(v___x_1285_, 0, v___x_1334_);
v___x_1336_ = v___x_1285_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v___x_1334_);
lean_ctor_set(v_reuseFailAlloc_1340_, 1, v_k_1280_);
lean_ctor_set(v_reuseFailAlloc_1340_, 2, v_v_1281_);
lean_ctor_set(v_reuseFailAlloc_1340_, 3, v_impl_1288_);
lean_ctor_set(v_reuseFailAlloc_1340_, 4, v_l_1310_);
v___x_1336_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
lean_object* v___x_1337_; 
v___x_1337_ = lean_nat_add(v___x_1289_, v_size_1312_);
if (lean_obj_tag(v_r_1311_) == 0)
{
lean_object* v_size_1338_; 
v_size_1338_ = lean_ctor_get(v_r_1311_, 0);
lean_inc(v_size_1338_);
v___y_1322_ = v___x_1336_;
v___y_1323_ = v___x_1337_;
v___y_1324_ = v_size_1338_;
goto v___jp_1321_;
}
else
{
lean_object* v___x_1339_; 
v___x_1339_ = lean_unsigned_to_nat(0u);
v___y_1322_ = v___x_1336_;
v___y_1323_ = v___x_1337_;
v___y_1324_ = v___x_1339_;
goto v___jp_1321_;
}
}
}
}
}
else
{
lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1353_; 
lean_del_object(v___x_1285_);
v___x_1349_ = lean_nat_add(v___x_1289_, v_size_1290_);
lean_dec(v_size_1290_);
v___x_1350_ = lean_nat_add(v___x_1349_, v_size_1291_);
lean_dec(v_size_1291_);
v___x_1351_ = lean_nat_add(v___x_1349_, v_size_1307_);
lean_dec(v___x_1349_);
lean_inc_ref(v_impl_1288_);
if (v_isShared_1306_ == 0)
{
lean_ctor_set(v___x_1305_, 4, v_l_1294_);
lean_ctor_set(v___x_1305_, 3, v_impl_1288_);
lean_ctor_set(v___x_1305_, 2, v_v_1281_);
lean_ctor_set(v___x_1305_, 1, v_k_1280_);
lean_ctor_set(v___x_1305_, 0, v___x_1351_);
v___x_1353_ = v___x_1305_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v___x_1351_);
lean_ctor_set(v_reuseFailAlloc_1366_, 1, v_k_1280_);
lean_ctor_set(v_reuseFailAlloc_1366_, 2, v_v_1281_);
lean_ctor_set(v_reuseFailAlloc_1366_, 3, v_impl_1288_);
lean_ctor_set(v_reuseFailAlloc_1366_, 4, v_l_1294_);
v___x_1353_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1360_; 
v_isSharedCheck_1360_ = !lean_is_exclusive(v_impl_1288_);
if (v_isSharedCheck_1360_ == 0)
{
lean_object* v_unused_1361_; lean_object* v_unused_1362_; lean_object* v_unused_1363_; lean_object* v_unused_1364_; lean_object* v_unused_1365_; 
v_unused_1361_ = lean_ctor_get(v_impl_1288_, 4);
lean_dec(v_unused_1361_);
v_unused_1362_ = lean_ctor_get(v_impl_1288_, 3);
lean_dec(v_unused_1362_);
v_unused_1363_ = lean_ctor_get(v_impl_1288_, 2);
lean_dec(v_unused_1363_);
v_unused_1364_ = lean_ctor_get(v_impl_1288_, 1);
lean_dec(v_unused_1364_);
v_unused_1365_ = lean_ctor_get(v_impl_1288_, 0);
lean_dec(v_unused_1365_);
v___x_1355_ = v_impl_1288_;
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
else
{
lean_dec(v_impl_1288_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1360_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1358_; 
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 4, v_r_1295_);
lean_ctor_set(v___x_1355_, 3, v___x_1353_);
lean_ctor_set(v___x_1355_, 2, v_v_1293_);
lean_ctor_set(v___x_1355_, 1, v_k_1292_);
lean_ctor_set(v___x_1355_, 0, v___x_1350_);
v___x_1358_ = v___x_1355_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v___x_1350_);
lean_ctor_set(v_reuseFailAlloc_1359_, 1, v_k_1292_);
lean_ctor_set(v_reuseFailAlloc_1359_, 2, v_v_1293_);
lean_ctor_set(v_reuseFailAlloc_1359_, 3, v___x_1353_);
lean_ctor_set(v_reuseFailAlloc_1359_, 4, v_r_1295_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1373_; lean_object* v___x_1374_; lean_object* v___x_1376_; 
v_size_1373_ = lean_ctor_get(v_impl_1288_, 0);
lean_inc(v_size_1373_);
v___x_1374_ = lean_nat_add(v___x_1289_, v_size_1373_);
lean_dec(v_size_1373_);
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 3, v_impl_1288_);
lean_ctor_set(v___x_1285_, 0, v___x_1374_);
v___x_1376_ = v___x_1285_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v___x_1374_);
lean_ctor_set(v_reuseFailAlloc_1377_, 1, v_k_1280_);
lean_ctor_set(v_reuseFailAlloc_1377_, 2, v_v_1281_);
lean_ctor_set(v_reuseFailAlloc_1377_, 3, v_impl_1288_);
lean_ctor_set(v_reuseFailAlloc_1377_, 4, v_r_1283_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
else
{
if (lean_obj_tag(v_r_1283_) == 0)
{
lean_object* v_l_1378_; 
v_l_1378_ = lean_ctor_get(v_r_1283_, 3);
lean_inc(v_l_1378_);
if (lean_obj_tag(v_l_1378_) == 0)
{
lean_object* v_r_1379_; 
v_r_1379_ = lean_ctor_get(v_r_1283_, 4);
lean_inc(v_r_1379_);
if (lean_obj_tag(v_r_1379_) == 0)
{
lean_object* v_size_1380_; lean_object* v_k_1381_; lean_object* v_v_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1395_; 
v_size_1380_ = lean_ctor_get(v_r_1283_, 0);
v_k_1381_ = lean_ctor_get(v_r_1283_, 1);
v_v_1382_ = lean_ctor_get(v_r_1283_, 2);
v_isSharedCheck_1395_ = !lean_is_exclusive(v_r_1283_);
if (v_isSharedCheck_1395_ == 0)
{
lean_object* v_unused_1396_; lean_object* v_unused_1397_; 
v_unused_1396_ = lean_ctor_get(v_r_1283_, 4);
lean_dec(v_unused_1396_);
v_unused_1397_ = lean_ctor_get(v_r_1283_, 3);
lean_dec(v_unused_1397_);
v___x_1384_ = v_r_1283_;
v_isShared_1385_ = v_isSharedCheck_1395_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_v_1382_);
lean_inc(v_k_1381_);
lean_inc(v_size_1380_);
lean_dec(v_r_1283_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1395_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v_size_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1390_; 
v_size_1386_ = lean_ctor_get(v_l_1378_, 0);
v___x_1387_ = lean_nat_add(v___x_1289_, v_size_1380_);
lean_dec(v_size_1380_);
v___x_1388_ = lean_nat_add(v___x_1289_, v_size_1386_);
if (v_isShared_1385_ == 0)
{
lean_ctor_set(v___x_1384_, 4, v_l_1378_);
lean_ctor_set(v___x_1384_, 3, v_impl_1288_);
lean_ctor_set(v___x_1384_, 2, v_v_1281_);
lean_ctor_set(v___x_1384_, 1, v_k_1280_);
lean_ctor_set(v___x_1384_, 0, v___x_1388_);
v___x_1390_ = v___x_1384_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v___x_1388_);
lean_ctor_set(v_reuseFailAlloc_1394_, 1, v_k_1280_);
lean_ctor_set(v_reuseFailAlloc_1394_, 2, v_v_1281_);
lean_ctor_set(v_reuseFailAlloc_1394_, 3, v_impl_1288_);
lean_ctor_set(v_reuseFailAlloc_1394_, 4, v_l_1378_);
v___x_1390_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
lean_object* v___x_1392_; 
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 4, v_r_1379_);
lean_ctor_set(v___x_1285_, 3, v___x_1390_);
lean_ctor_set(v___x_1285_, 2, v_v_1382_);
lean_ctor_set(v___x_1285_, 1, v_k_1381_);
lean_ctor_set(v___x_1285_, 0, v___x_1387_);
v___x_1392_ = v___x_1285_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v___x_1387_);
lean_ctor_set(v_reuseFailAlloc_1393_, 1, v_k_1381_);
lean_ctor_set(v_reuseFailAlloc_1393_, 2, v_v_1382_);
lean_ctor_set(v_reuseFailAlloc_1393_, 3, v___x_1390_);
lean_ctor_set(v_reuseFailAlloc_1393_, 4, v_r_1379_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
}
}
else
{
lean_object* v_k_1398_; lean_object* v_v_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1422_; 
v_k_1398_ = lean_ctor_get(v_r_1283_, 1);
v_v_1399_ = lean_ctor_get(v_r_1283_, 2);
v_isSharedCheck_1422_ = !lean_is_exclusive(v_r_1283_);
if (v_isSharedCheck_1422_ == 0)
{
lean_object* v_unused_1423_; lean_object* v_unused_1424_; lean_object* v_unused_1425_; 
v_unused_1423_ = lean_ctor_get(v_r_1283_, 4);
lean_dec(v_unused_1423_);
v_unused_1424_ = lean_ctor_get(v_r_1283_, 3);
lean_dec(v_unused_1424_);
v_unused_1425_ = lean_ctor_get(v_r_1283_, 0);
lean_dec(v_unused_1425_);
v___x_1401_ = v_r_1283_;
v_isShared_1402_ = v_isSharedCheck_1422_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_v_1399_);
lean_inc(v_k_1398_);
lean_dec(v_r_1283_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1422_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v_k_1403_; lean_object* v_v_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1418_; 
v_k_1403_ = lean_ctor_get(v_l_1378_, 1);
v_v_1404_ = lean_ctor_get(v_l_1378_, 2);
v_isSharedCheck_1418_ = !lean_is_exclusive(v_l_1378_);
if (v_isSharedCheck_1418_ == 0)
{
lean_object* v_unused_1419_; lean_object* v_unused_1420_; lean_object* v_unused_1421_; 
v_unused_1419_ = lean_ctor_get(v_l_1378_, 4);
lean_dec(v_unused_1419_);
v_unused_1420_ = lean_ctor_get(v_l_1378_, 3);
lean_dec(v_unused_1420_);
v_unused_1421_ = lean_ctor_get(v_l_1378_, 0);
lean_dec(v_unused_1421_);
v___x_1406_ = v_l_1378_;
v_isShared_1407_ = v_isSharedCheck_1418_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_v_1404_);
lean_inc(v_k_1403_);
lean_dec(v_l_1378_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1418_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v___x_1408_; lean_object* v___x_1410_; 
v___x_1408_ = lean_unsigned_to_nat(3u);
if (v_isShared_1407_ == 0)
{
lean_ctor_set(v___x_1406_, 4, v_r_1379_);
lean_ctor_set(v___x_1406_, 3, v_r_1379_);
lean_ctor_set(v___x_1406_, 2, v_v_1281_);
lean_ctor_set(v___x_1406_, 1, v_k_1280_);
lean_ctor_set(v___x_1406_, 0, v___x_1289_);
v___x_1410_ = v___x_1406_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v___x_1289_);
lean_ctor_set(v_reuseFailAlloc_1417_, 1, v_k_1280_);
lean_ctor_set(v_reuseFailAlloc_1417_, 2, v_v_1281_);
lean_ctor_set(v_reuseFailAlloc_1417_, 3, v_r_1379_);
lean_ctor_set(v_reuseFailAlloc_1417_, 4, v_r_1379_);
v___x_1410_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
lean_object* v___x_1412_; 
if (v_isShared_1402_ == 0)
{
lean_ctor_set(v___x_1401_, 3, v_r_1379_);
lean_ctor_set(v___x_1401_, 0, v___x_1289_);
v___x_1412_ = v___x_1401_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v___x_1289_);
lean_ctor_set(v_reuseFailAlloc_1416_, 1, v_k_1398_);
lean_ctor_set(v_reuseFailAlloc_1416_, 2, v_v_1399_);
lean_ctor_set(v_reuseFailAlloc_1416_, 3, v_r_1379_);
lean_ctor_set(v_reuseFailAlloc_1416_, 4, v_r_1379_);
v___x_1412_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
lean_object* v___x_1414_; 
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 4, v___x_1412_);
lean_ctor_set(v___x_1285_, 3, v___x_1410_);
lean_ctor_set(v___x_1285_, 2, v_v_1404_);
lean_ctor_set(v___x_1285_, 1, v_k_1403_);
lean_ctor_set(v___x_1285_, 0, v___x_1408_);
v___x_1414_ = v___x_1285_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v___x_1408_);
lean_ctor_set(v_reuseFailAlloc_1415_, 1, v_k_1403_);
lean_ctor_set(v_reuseFailAlloc_1415_, 2, v_v_1404_);
lean_ctor_set(v_reuseFailAlloc_1415_, 3, v___x_1410_);
lean_ctor_set(v_reuseFailAlloc_1415_, 4, v___x_1412_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
return v___x_1414_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_1426_; 
v_r_1426_ = lean_ctor_get(v_r_1283_, 4);
lean_inc(v_r_1426_);
if (lean_obj_tag(v_r_1426_) == 0)
{
lean_object* v_k_1427_; lean_object* v_v_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1439_; 
v_k_1427_ = lean_ctor_get(v_r_1283_, 1);
v_v_1428_ = lean_ctor_get(v_r_1283_, 2);
v_isSharedCheck_1439_ = !lean_is_exclusive(v_r_1283_);
if (v_isSharedCheck_1439_ == 0)
{
lean_object* v_unused_1440_; lean_object* v_unused_1441_; lean_object* v_unused_1442_; 
v_unused_1440_ = lean_ctor_get(v_r_1283_, 4);
lean_dec(v_unused_1440_);
v_unused_1441_ = lean_ctor_get(v_r_1283_, 3);
lean_dec(v_unused_1441_);
v_unused_1442_ = lean_ctor_get(v_r_1283_, 0);
lean_dec(v_unused_1442_);
v___x_1430_ = v_r_1283_;
v_isShared_1431_ = v_isSharedCheck_1439_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_v_1428_);
lean_inc(v_k_1427_);
lean_dec(v_r_1283_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1439_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1432_; lean_object* v___x_1434_; 
v___x_1432_ = lean_unsigned_to_nat(3u);
if (v_isShared_1431_ == 0)
{
lean_ctor_set(v___x_1430_, 4, v_l_1378_);
lean_ctor_set(v___x_1430_, 2, v_v_1281_);
lean_ctor_set(v___x_1430_, 1, v_k_1280_);
lean_ctor_set(v___x_1430_, 0, v___x_1289_);
v___x_1434_ = v___x_1430_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v___x_1289_);
lean_ctor_set(v_reuseFailAlloc_1438_, 1, v_k_1280_);
lean_ctor_set(v_reuseFailAlloc_1438_, 2, v_v_1281_);
lean_ctor_set(v_reuseFailAlloc_1438_, 3, v_l_1378_);
lean_ctor_set(v_reuseFailAlloc_1438_, 4, v_l_1378_);
v___x_1434_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
lean_object* v___x_1436_; 
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 4, v_r_1426_);
lean_ctor_set(v___x_1285_, 3, v___x_1434_);
lean_ctor_set(v___x_1285_, 2, v_v_1428_);
lean_ctor_set(v___x_1285_, 1, v_k_1427_);
lean_ctor_set(v___x_1285_, 0, v___x_1432_);
v___x_1436_ = v___x_1285_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v___x_1432_);
lean_ctor_set(v_reuseFailAlloc_1437_, 1, v_k_1427_);
lean_ctor_set(v_reuseFailAlloc_1437_, 2, v_v_1428_);
lean_ctor_set(v_reuseFailAlloc_1437_, 3, v___x_1434_);
lean_ctor_set(v_reuseFailAlloc_1437_, 4, v_r_1426_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
return v___x_1436_;
}
}
}
}
else
{
lean_object* v_size_1443_; lean_object* v_k_1444_; lean_object* v_v_1445_; lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1456_; 
v_size_1443_ = lean_ctor_get(v_r_1283_, 0);
v_k_1444_ = lean_ctor_get(v_r_1283_, 1);
v_v_1445_ = lean_ctor_get(v_r_1283_, 2);
v_isSharedCheck_1456_ = !lean_is_exclusive(v_r_1283_);
if (v_isSharedCheck_1456_ == 0)
{
lean_object* v_unused_1457_; lean_object* v_unused_1458_; 
v_unused_1457_ = lean_ctor_get(v_r_1283_, 4);
lean_dec(v_unused_1457_);
v_unused_1458_ = lean_ctor_get(v_r_1283_, 3);
lean_dec(v_unused_1458_);
v___x_1447_ = v_r_1283_;
v_isShared_1448_ = v_isSharedCheck_1456_;
goto v_resetjp_1446_;
}
else
{
lean_inc(v_v_1445_);
lean_inc(v_k_1444_);
lean_inc(v_size_1443_);
lean_dec(v_r_1283_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1456_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
lean_object* v___x_1450_; 
if (v_isShared_1448_ == 0)
{
lean_ctor_set(v___x_1447_, 3, v_r_1426_);
v___x_1450_ = v___x_1447_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v_size_1443_);
lean_ctor_set(v_reuseFailAlloc_1455_, 1, v_k_1444_);
lean_ctor_set(v_reuseFailAlloc_1455_, 2, v_v_1445_);
lean_ctor_set(v_reuseFailAlloc_1455_, 3, v_r_1426_);
lean_ctor_set(v_reuseFailAlloc_1455_, 4, v_r_1426_);
v___x_1450_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
lean_object* v___x_1451_; lean_object* v___x_1453_; 
v___x_1451_ = lean_unsigned_to_nat(2u);
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 4, v___x_1450_);
lean_ctor_set(v___x_1285_, 3, v_r_1426_);
lean_ctor_set(v___x_1285_, 0, v___x_1451_);
v___x_1453_ = v___x_1285_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v___x_1451_);
lean_ctor_set(v_reuseFailAlloc_1454_, 1, v_k_1280_);
lean_ctor_set(v_reuseFailAlloc_1454_, 2, v_v_1281_);
lean_ctor_set(v_reuseFailAlloc_1454_, 3, v_r_1426_);
lean_ctor_set(v_reuseFailAlloc_1454_, 4, v___x_1450_);
v___x_1453_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
return v___x_1453_;
}
}
}
}
}
}
else
{
lean_object* v___x_1460_; 
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 3, v_r_1283_);
lean_ctor_set(v___x_1285_, 0, v___x_1289_);
v___x_1460_ = v___x_1285_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v___x_1289_);
lean_ctor_set(v_reuseFailAlloc_1461_, 1, v_k_1280_);
lean_ctor_set(v_reuseFailAlloc_1461_, 2, v_v_1281_);
lean_ctor_set(v_reuseFailAlloc_1461_, 3, v_r_1283_);
lean_ctor_set(v_reuseFailAlloc_1461_, 4, v_r_1283_);
v___x_1460_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
return v___x_1460_;
}
}
}
}
case 1:
{
lean_del_object(v___x_1285_);
lean_dec(v_v_1281_);
lean_dec(v_k_1280_);
if (lean_obj_tag(v_l_1282_) == 0)
{
if (lean_obj_tag(v_r_1283_) == 0)
{
lean_object* v_size_1462_; lean_object* v_k_1463_; lean_object* v_v_1464_; lean_object* v_l_1465_; lean_object* v_r_1466_; lean_object* v_size_1467_; lean_object* v_k_1468_; lean_object* v_v_1469_; lean_object* v_l_1470_; lean_object* v_r_1471_; lean_object* v___x_1472_; uint8_t v___x_1473_; 
v_size_1462_ = lean_ctor_get(v_l_1282_, 0);
v_k_1463_ = lean_ctor_get(v_l_1282_, 1);
v_v_1464_ = lean_ctor_get(v_l_1282_, 2);
v_l_1465_ = lean_ctor_get(v_l_1282_, 3);
v_r_1466_ = lean_ctor_get(v_l_1282_, 4);
lean_inc(v_r_1466_);
v_size_1467_ = lean_ctor_get(v_r_1283_, 0);
v_k_1468_ = lean_ctor_get(v_r_1283_, 1);
v_v_1469_ = lean_ctor_get(v_r_1283_, 2);
v_l_1470_ = lean_ctor_get(v_r_1283_, 3);
lean_inc(v_l_1470_);
v_r_1471_ = lean_ctor_get(v_r_1283_, 4);
v___x_1472_ = lean_unsigned_to_nat(1u);
v___x_1473_ = lean_nat_dec_lt(v_size_1462_, v_size_1467_);
if (v___x_1473_ == 0)
{
lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1609_; 
lean_inc(v_l_1465_);
lean_inc(v_v_1464_);
lean_inc(v_k_1463_);
v_isSharedCheck_1609_ = !lean_is_exclusive(v_l_1282_);
if (v_isSharedCheck_1609_ == 0)
{
lean_object* v_unused_1610_; lean_object* v_unused_1611_; lean_object* v_unused_1612_; lean_object* v_unused_1613_; lean_object* v_unused_1614_; 
v_unused_1610_ = lean_ctor_get(v_l_1282_, 4);
lean_dec(v_unused_1610_);
v_unused_1611_ = lean_ctor_get(v_l_1282_, 3);
lean_dec(v_unused_1611_);
v_unused_1612_ = lean_ctor_get(v_l_1282_, 2);
lean_dec(v_unused_1612_);
v_unused_1613_ = lean_ctor_get(v_l_1282_, 1);
lean_dec(v_unused_1613_);
v_unused_1614_ = lean_ctor_get(v_l_1282_, 0);
lean_dec(v_unused_1614_);
v___x_1475_ = v_l_1282_;
v_isShared_1476_ = v_isSharedCheck_1609_;
goto v_resetjp_1474_;
}
else
{
lean_dec(v_l_1282_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1609_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1477_; lean_object* v_tree_1478_; 
v___x_1477_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_1463_, v_v_1464_, v_l_1465_, v_r_1466_);
v_tree_1478_ = lean_ctor_get(v___x_1477_, 2);
lean_inc(v_tree_1478_);
if (lean_obj_tag(v_tree_1478_) == 0)
{
lean_object* v_k_1479_; lean_object* v_v_1480_; lean_object* v_size_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; uint8_t v___x_1484_; 
v_k_1479_ = lean_ctor_get(v___x_1477_, 0);
lean_inc(v_k_1479_);
v_v_1480_ = lean_ctor_get(v___x_1477_, 1);
lean_inc(v_v_1480_);
lean_dec_ref(v___x_1477_);
v_size_1481_ = lean_ctor_get(v_tree_1478_, 0);
v___x_1482_ = lean_unsigned_to_nat(3u);
v___x_1483_ = lean_nat_mul(v___x_1482_, v_size_1481_);
v___x_1484_ = lean_nat_dec_lt(v___x_1483_, v_size_1467_);
lean_dec(v___x_1483_);
if (v___x_1484_ == 0)
{
lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1488_; 
lean_dec(v_l_1470_);
v___x_1485_ = lean_nat_add(v___x_1472_, v_size_1481_);
v___x_1486_ = lean_nat_add(v___x_1485_, v_size_1467_);
lean_dec(v___x_1485_);
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 4, v_r_1283_);
lean_ctor_set(v___x_1475_, 3, v_tree_1478_);
lean_ctor_set(v___x_1475_, 2, v_v_1480_);
lean_ctor_set(v___x_1475_, 1, v_k_1479_);
lean_ctor_set(v___x_1475_, 0, v___x_1486_);
v___x_1488_ = v___x_1475_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v___x_1486_);
lean_ctor_set(v_reuseFailAlloc_1489_, 1, v_k_1479_);
lean_ctor_set(v_reuseFailAlloc_1489_, 2, v_v_1480_);
lean_ctor_set(v_reuseFailAlloc_1489_, 3, v_tree_1478_);
lean_ctor_set(v_reuseFailAlloc_1489_, 4, v_r_1283_);
v___x_1488_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
return v___x_1488_;
}
}
else
{
lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1544_; 
lean_inc(v_r_1471_);
lean_inc(v_v_1469_);
lean_inc(v_k_1468_);
lean_inc(v_size_1467_);
v_isSharedCheck_1544_ = !lean_is_exclusive(v_r_1283_);
if (v_isSharedCheck_1544_ == 0)
{
lean_object* v_unused_1545_; lean_object* v_unused_1546_; lean_object* v_unused_1547_; lean_object* v_unused_1548_; lean_object* v_unused_1549_; 
v_unused_1545_ = lean_ctor_get(v_r_1283_, 4);
lean_dec(v_unused_1545_);
v_unused_1546_ = lean_ctor_get(v_r_1283_, 3);
lean_dec(v_unused_1546_);
v_unused_1547_ = lean_ctor_get(v_r_1283_, 2);
lean_dec(v_unused_1547_);
v_unused_1548_ = lean_ctor_get(v_r_1283_, 1);
lean_dec(v_unused_1548_);
v_unused_1549_ = lean_ctor_get(v_r_1283_, 0);
lean_dec(v_unused_1549_);
v___x_1491_ = v_r_1283_;
v_isShared_1492_ = v_isSharedCheck_1544_;
goto v_resetjp_1490_;
}
else
{
lean_dec(v_r_1283_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1544_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v_size_1493_; lean_object* v_k_1494_; lean_object* v_v_1495_; lean_object* v_l_1496_; lean_object* v_r_1497_; lean_object* v_size_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; uint8_t v___x_1501_; 
v_size_1493_ = lean_ctor_get(v_l_1470_, 0);
v_k_1494_ = lean_ctor_get(v_l_1470_, 1);
v_v_1495_ = lean_ctor_get(v_l_1470_, 2);
v_l_1496_ = lean_ctor_get(v_l_1470_, 3);
v_r_1497_ = lean_ctor_get(v_l_1470_, 4);
v_size_1498_ = lean_ctor_get(v_r_1471_, 0);
v___x_1499_ = lean_unsigned_to_nat(2u);
v___x_1500_ = lean_nat_mul(v___x_1499_, v_size_1498_);
v___x_1501_ = lean_nat_dec_lt(v_size_1493_, v___x_1500_);
lean_dec(v___x_1500_);
if (v___x_1501_ == 0)
{
lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1529_; 
lean_inc(v_r_1497_);
lean_inc(v_l_1496_);
lean_inc(v_v_1495_);
lean_inc(v_k_1494_);
v_isSharedCheck_1529_ = !lean_is_exclusive(v_l_1470_);
if (v_isSharedCheck_1529_ == 0)
{
lean_object* v_unused_1530_; lean_object* v_unused_1531_; lean_object* v_unused_1532_; lean_object* v_unused_1533_; lean_object* v_unused_1534_; 
v_unused_1530_ = lean_ctor_get(v_l_1470_, 4);
lean_dec(v_unused_1530_);
v_unused_1531_ = lean_ctor_get(v_l_1470_, 3);
lean_dec(v_unused_1531_);
v_unused_1532_ = lean_ctor_get(v_l_1470_, 2);
lean_dec(v_unused_1532_);
v_unused_1533_ = lean_ctor_get(v_l_1470_, 1);
lean_dec(v_unused_1533_);
v_unused_1534_ = lean_ctor_get(v_l_1470_, 0);
lean_dec(v_unused_1534_);
v___x_1503_ = v_l_1470_;
v_isShared_1504_ = v_isSharedCheck_1529_;
goto v_resetjp_1502_;
}
else
{
lean_dec(v_l_1470_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1529_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___y_1508_; lean_object* v___y_1509_; lean_object* v___y_1510_; lean_object* v___y_1519_; 
v___x_1505_ = lean_nat_add(v___x_1472_, v_size_1481_);
v___x_1506_ = lean_nat_add(v___x_1505_, v_size_1467_);
lean_dec(v_size_1467_);
if (lean_obj_tag(v_l_1496_) == 0)
{
lean_object* v_size_1527_; 
v_size_1527_ = lean_ctor_get(v_l_1496_, 0);
lean_inc(v_size_1527_);
v___y_1519_ = v_size_1527_;
goto v___jp_1518_;
}
else
{
lean_object* v___x_1528_; 
v___x_1528_ = lean_unsigned_to_nat(0u);
v___y_1519_ = v___x_1528_;
goto v___jp_1518_;
}
v___jp_1507_:
{
lean_object* v___x_1511_; lean_object* v___x_1513_; 
v___x_1511_ = lean_nat_add(v___y_1509_, v___y_1510_);
lean_dec(v___y_1510_);
lean_dec(v___y_1509_);
if (v_isShared_1504_ == 0)
{
lean_ctor_set(v___x_1503_, 4, v_r_1471_);
lean_ctor_set(v___x_1503_, 3, v_r_1497_);
lean_ctor_set(v___x_1503_, 2, v_v_1469_);
lean_ctor_set(v___x_1503_, 1, v_k_1468_);
lean_ctor_set(v___x_1503_, 0, v___x_1511_);
v___x_1513_ = v___x_1503_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v___x_1511_);
lean_ctor_set(v_reuseFailAlloc_1517_, 1, v_k_1468_);
lean_ctor_set(v_reuseFailAlloc_1517_, 2, v_v_1469_);
lean_ctor_set(v_reuseFailAlloc_1517_, 3, v_r_1497_);
lean_ctor_set(v_reuseFailAlloc_1517_, 4, v_r_1471_);
v___x_1513_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
lean_object* v___x_1515_; 
if (v_isShared_1492_ == 0)
{
lean_ctor_set(v___x_1491_, 4, v___x_1513_);
lean_ctor_set(v___x_1491_, 3, v___y_1508_);
lean_ctor_set(v___x_1491_, 2, v_v_1495_);
lean_ctor_set(v___x_1491_, 1, v_k_1494_);
lean_ctor_set(v___x_1491_, 0, v___x_1506_);
v___x_1515_ = v___x_1491_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v___x_1506_);
lean_ctor_set(v_reuseFailAlloc_1516_, 1, v_k_1494_);
lean_ctor_set(v_reuseFailAlloc_1516_, 2, v_v_1495_);
lean_ctor_set(v_reuseFailAlloc_1516_, 3, v___y_1508_);
lean_ctor_set(v_reuseFailAlloc_1516_, 4, v___x_1513_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
}
v___jp_1518_:
{
lean_object* v___x_1520_; lean_object* v___x_1522_; 
v___x_1520_ = lean_nat_add(v___x_1505_, v___y_1519_);
lean_dec(v___y_1519_);
lean_dec(v___x_1505_);
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 4, v_l_1496_);
lean_ctor_set(v___x_1475_, 3, v_tree_1478_);
lean_ctor_set(v___x_1475_, 2, v_v_1480_);
lean_ctor_set(v___x_1475_, 1, v_k_1479_);
lean_ctor_set(v___x_1475_, 0, v___x_1520_);
v___x_1522_ = v___x_1475_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v___x_1520_);
lean_ctor_set(v_reuseFailAlloc_1526_, 1, v_k_1479_);
lean_ctor_set(v_reuseFailAlloc_1526_, 2, v_v_1480_);
lean_ctor_set(v_reuseFailAlloc_1526_, 3, v_tree_1478_);
lean_ctor_set(v_reuseFailAlloc_1526_, 4, v_l_1496_);
v___x_1522_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
lean_object* v___x_1523_; 
v___x_1523_ = lean_nat_add(v___x_1472_, v_size_1498_);
if (lean_obj_tag(v_r_1497_) == 0)
{
lean_object* v_size_1524_; 
v_size_1524_ = lean_ctor_get(v_r_1497_, 0);
lean_inc(v_size_1524_);
v___y_1508_ = v___x_1522_;
v___y_1509_ = v___x_1523_;
v___y_1510_ = v_size_1524_;
goto v___jp_1507_;
}
else
{
lean_object* v___x_1525_; 
v___x_1525_ = lean_unsigned_to_nat(0u);
v___y_1508_ = v___x_1522_;
v___y_1509_ = v___x_1523_;
v___y_1510_ = v___x_1525_;
goto v___jp_1507_;
}
}
}
}
}
else
{
lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1539_; 
v___x_1535_ = lean_nat_add(v___x_1472_, v_size_1481_);
v___x_1536_ = lean_nat_add(v___x_1535_, v_size_1467_);
lean_dec(v_size_1467_);
v___x_1537_ = lean_nat_add(v___x_1535_, v_size_1493_);
lean_dec(v___x_1535_);
if (v_isShared_1492_ == 0)
{
lean_ctor_set(v___x_1491_, 4, v_l_1470_);
lean_ctor_set(v___x_1491_, 3, v_tree_1478_);
lean_ctor_set(v___x_1491_, 2, v_v_1480_);
lean_ctor_set(v___x_1491_, 1, v_k_1479_);
lean_ctor_set(v___x_1491_, 0, v___x_1537_);
v___x_1539_ = v___x_1491_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v___x_1537_);
lean_ctor_set(v_reuseFailAlloc_1543_, 1, v_k_1479_);
lean_ctor_set(v_reuseFailAlloc_1543_, 2, v_v_1480_);
lean_ctor_set(v_reuseFailAlloc_1543_, 3, v_tree_1478_);
lean_ctor_set(v_reuseFailAlloc_1543_, 4, v_l_1470_);
v___x_1539_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
lean_object* v___x_1541_; 
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 4, v_r_1471_);
lean_ctor_set(v___x_1475_, 3, v___x_1539_);
lean_ctor_set(v___x_1475_, 2, v_v_1469_);
lean_ctor_set(v___x_1475_, 1, v_k_1468_);
lean_ctor_set(v___x_1475_, 0, v___x_1536_);
v___x_1541_ = v___x_1475_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v___x_1536_);
lean_ctor_set(v_reuseFailAlloc_1542_, 1, v_k_1468_);
lean_ctor_set(v_reuseFailAlloc_1542_, 2, v_v_1469_);
lean_ctor_set(v_reuseFailAlloc_1542_, 3, v___x_1539_);
lean_ctor_set(v_reuseFailAlloc_1542_, 4, v_r_1471_);
v___x_1541_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
return v___x_1541_;
}
}
}
}
}
}
else
{
lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1603_; 
lean_inc(v_r_1471_);
lean_inc(v_v_1469_);
lean_inc(v_k_1468_);
lean_inc(v_size_1467_);
v_isSharedCheck_1603_ = !lean_is_exclusive(v_r_1283_);
if (v_isSharedCheck_1603_ == 0)
{
lean_object* v_unused_1604_; lean_object* v_unused_1605_; lean_object* v_unused_1606_; lean_object* v_unused_1607_; lean_object* v_unused_1608_; 
v_unused_1604_ = lean_ctor_get(v_r_1283_, 4);
lean_dec(v_unused_1604_);
v_unused_1605_ = lean_ctor_get(v_r_1283_, 3);
lean_dec(v_unused_1605_);
v_unused_1606_ = lean_ctor_get(v_r_1283_, 2);
lean_dec(v_unused_1606_);
v_unused_1607_ = lean_ctor_get(v_r_1283_, 1);
lean_dec(v_unused_1607_);
v_unused_1608_ = lean_ctor_get(v_r_1283_, 0);
lean_dec(v_unused_1608_);
v___x_1551_ = v_r_1283_;
v_isShared_1552_ = v_isSharedCheck_1603_;
goto v_resetjp_1550_;
}
else
{
lean_dec(v_r_1283_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1603_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
if (lean_obj_tag(v_l_1470_) == 0)
{
if (lean_obj_tag(v_r_1471_) == 0)
{
lean_object* v_k_1553_; lean_object* v_v_1554_; lean_object* v_size_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1559_; 
v_k_1553_ = lean_ctor_get(v___x_1477_, 0);
lean_inc(v_k_1553_);
v_v_1554_ = lean_ctor_get(v___x_1477_, 1);
lean_inc(v_v_1554_);
lean_dec_ref(v___x_1477_);
v_size_1555_ = lean_ctor_get(v_l_1470_, 0);
v___x_1556_ = lean_nat_add(v___x_1472_, v_size_1467_);
lean_dec(v_size_1467_);
v___x_1557_ = lean_nat_add(v___x_1472_, v_size_1555_);
if (v_isShared_1552_ == 0)
{
lean_ctor_set(v___x_1551_, 4, v_l_1470_);
lean_ctor_set(v___x_1551_, 3, v_tree_1478_);
lean_ctor_set(v___x_1551_, 2, v_v_1554_);
lean_ctor_set(v___x_1551_, 1, v_k_1553_);
lean_ctor_set(v___x_1551_, 0, v___x_1557_);
v___x_1559_ = v___x_1551_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v___x_1557_);
lean_ctor_set(v_reuseFailAlloc_1563_, 1, v_k_1553_);
lean_ctor_set(v_reuseFailAlloc_1563_, 2, v_v_1554_);
lean_ctor_set(v_reuseFailAlloc_1563_, 3, v_tree_1478_);
lean_ctor_set(v_reuseFailAlloc_1563_, 4, v_l_1470_);
v___x_1559_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
lean_object* v___x_1561_; 
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 4, v_r_1471_);
lean_ctor_set(v___x_1475_, 3, v___x_1559_);
lean_ctor_set(v___x_1475_, 2, v_v_1469_);
lean_ctor_set(v___x_1475_, 1, v_k_1468_);
lean_ctor_set(v___x_1475_, 0, v___x_1556_);
v___x_1561_ = v___x_1475_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v___x_1556_);
lean_ctor_set(v_reuseFailAlloc_1562_, 1, v_k_1468_);
lean_ctor_set(v_reuseFailAlloc_1562_, 2, v_v_1469_);
lean_ctor_set(v_reuseFailAlloc_1562_, 3, v___x_1559_);
lean_ctor_set(v_reuseFailAlloc_1562_, 4, v_r_1471_);
v___x_1561_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
return v___x_1561_;
}
}
}
else
{
lean_object* v_k_1564_; lean_object* v_v_1565_; lean_object* v_k_1566_; lean_object* v_v_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1581_; 
lean_dec(v_size_1467_);
v_k_1564_ = lean_ctor_get(v___x_1477_, 0);
lean_inc(v_k_1564_);
v_v_1565_ = lean_ctor_get(v___x_1477_, 1);
lean_inc(v_v_1565_);
lean_dec_ref(v___x_1477_);
v_k_1566_ = lean_ctor_get(v_l_1470_, 1);
v_v_1567_ = lean_ctor_get(v_l_1470_, 2);
v_isSharedCheck_1581_ = !lean_is_exclusive(v_l_1470_);
if (v_isSharedCheck_1581_ == 0)
{
lean_object* v_unused_1582_; lean_object* v_unused_1583_; lean_object* v_unused_1584_; 
v_unused_1582_ = lean_ctor_get(v_l_1470_, 4);
lean_dec(v_unused_1582_);
v_unused_1583_ = lean_ctor_get(v_l_1470_, 3);
lean_dec(v_unused_1583_);
v_unused_1584_ = lean_ctor_get(v_l_1470_, 0);
lean_dec(v_unused_1584_);
v___x_1569_ = v_l_1470_;
v_isShared_1570_ = v_isSharedCheck_1581_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_v_1567_);
lean_inc(v_k_1566_);
lean_dec(v_l_1470_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1581_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v___x_1571_; lean_object* v___x_1573_; 
v___x_1571_ = lean_unsigned_to_nat(3u);
if (v_isShared_1570_ == 0)
{
lean_ctor_set(v___x_1569_, 4, v_r_1471_);
lean_ctor_set(v___x_1569_, 3, v_r_1471_);
lean_ctor_set(v___x_1569_, 2, v_v_1565_);
lean_ctor_set(v___x_1569_, 1, v_k_1564_);
lean_ctor_set(v___x_1569_, 0, v___x_1472_);
v___x_1573_ = v___x_1569_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v___x_1472_);
lean_ctor_set(v_reuseFailAlloc_1580_, 1, v_k_1564_);
lean_ctor_set(v_reuseFailAlloc_1580_, 2, v_v_1565_);
lean_ctor_set(v_reuseFailAlloc_1580_, 3, v_r_1471_);
lean_ctor_set(v_reuseFailAlloc_1580_, 4, v_r_1471_);
v___x_1573_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
lean_object* v___x_1575_; 
if (v_isShared_1552_ == 0)
{
lean_ctor_set(v___x_1551_, 3, v_r_1471_);
lean_ctor_set(v___x_1551_, 0, v___x_1472_);
v___x_1575_ = v___x_1551_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v___x_1472_);
lean_ctor_set(v_reuseFailAlloc_1579_, 1, v_k_1468_);
lean_ctor_set(v_reuseFailAlloc_1579_, 2, v_v_1469_);
lean_ctor_set(v_reuseFailAlloc_1579_, 3, v_r_1471_);
lean_ctor_set(v_reuseFailAlloc_1579_, 4, v_r_1471_);
v___x_1575_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
lean_object* v___x_1577_; 
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 4, v___x_1575_);
lean_ctor_set(v___x_1475_, 3, v___x_1573_);
lean_ctor_set(v___x_1475_, 2, v_v_1567_);
lean_ctor_set(v___x_1475_, 1, v_k_1566_);
lean_ctor_set(v___x_1475_, 0, v___x_1571_);
v___x_1577_ = v___x_1475_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v___x_1571_);
lean_ctor_set(v_reuseFailAlloc_1578_, 1, v_k_1566_);
lean_ctor_set(v_reuseFailAlloc_1578_, 2, v_v_1567_);
lean_ctor_set(v_reuseFailAlloc_1578_, 3, v___x_1573_);
lean_ctor_set(v_reuseFailAlloc_1578_, 4, v___x_1575_);
v___x_1577_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
return v___x_1577_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1471_) == 0)
{
lean_object* v_k_1585_; lean_object* v_v_1586_; lean_object* v___x_1587_; lean_object* v___x_1589_; 
lean_dec(v_size_1467_);
v_k_1585_ = lean_ctor_get(v___x_1477_, 0);
lean_inc(v_k_1585_);
v_v_1586_ = lean_ctor_get(v___x_1477_, 1);
lean_inc(v_v_1586_);
lean_dec_ref(v___x_1477_);
v___x_1587_ = lean_unsigned_to_nat(3u);
if (v_isShared_1552_ == 0)
{
lean_ctor_set(v___x_1551_, 4, v_l_1470_);
lean_ctor_set(v___x_1551_, 2, v_v_1586_);
lean_ctor_set(v___x_1551_, 1, v_k_1585_);
lean_ctor_set(v___x_1551_, 0, v___x_1472_);
v___x_1589_ = v___x_1551_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v___x_1472_);
lean_ctor_set(v_reuseFailAlloc_1593_, 1, v_k_1585_);
lean_ctor_set(v_reuseFailAlloc_1593_, 2, v_v_1586_);
lean_ctor_set(v_reuseFailAlloc_1593_, 3, v_l_1470_);
lean_ctor_set(v_reuseFailAlloc_1593_, 4, v_l_1470_);
v___x_1589_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
lean_object* v___x_1591_; 
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 4, v_r_1471_);
lean_ctor_set(v___x_1475_, 3, v___x_1589_);
lean_ctor_set(v___x_1475_, 2, v_v_1469_);
lean_ctor_set(v___x_1475_, 1, v_k_1468_);
lean_ctor_set(v___x_1475_, 0, v___x_1587_);
v___x_1591_ = v___x_1475_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v___x_1587_);
lean_ctor_set(v_reuseFailAlloc_1592_, 1, v_k_1468_);
lean_ctor_set(v_reuseFailAlloc_1592_, 2, v_v_1469_);
lean_ctor_set(v_reuseFailAlloc_1592_, 3, v___x_1589_);
lean_ctor_set(v_reuseFailAlloc_1592_, 4, v_r_1471_);
v___x_1591_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
return v___x_1591_;
}
}
}
else
{
lean_object* v_k_1594_; lean_object* v_v_1595_; lean_object* v___x_1597_; 
v_k_1594_ = lean_ctor_get(v___x_1477_, 0);
lean_inc(v_k_1594_);
v_v_1595_ = lean_ctor_get(v___x_1477_, 1);
lean_inc(v_v_1595_);
lean_dec_ref(v___x_1477_);
if (v_isShared_1552_ == 0)
{
lean_ctor_set(v___x_1551_, 3, v_r_1471_);
v___x_1597_ = v___x_1551_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_size_1467_);
lean_ctor_set(v_reuseFailAlloc_1602_, 1, v_k_1468_);
lean_ctor_set(v_reuseFailAlloc_1602_, 2, v_v_1469_);
lean_ctor_set(v_reuseFailAlloc_1602_, 3, v_r_1471_);
lean_ctor_set(v_reuseFailAlloc_1602_, 4, v_r_1471_);
v___x_1597_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
lean_object* v___x_1598_; lean_object* v___x_1600_; 
v___x_1598_ = lean_unsigned_to_nat(2u);
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 4, v___x_1597_);
lean_ctor_set(v___x_1475_, 3, v_r_1471_);
lean_ctor_set(v___x_1475_, 2, v_v_1595_);
lean_ctor_set(v___x_1475_, 1, v_k_1594_);
lean_ctor_set(v___x_1475_, 0, v___x_1598_);
v___x_1600_ = v___x_1475_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v___x_1598_);
lean_ctor_set(v_reuseFailAlloc_1601_, 1, v_k_1594_);
lean_ctor_set(v_reuseFailAlloc_1601_, 2, v_v_1595_);
lean_ctor_set(v_reuseFailAlloc_1601_, 3, v_r_1471_);
lean_ctor_set(v_reuseFailAlloc_1601_, 4, v___x_1597_);
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
}
else
{
lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1767_; 
lean_inc(v_r_1471_);
lean_inc(v_v_1469_);
lean_inc(v_k_1468_);
v_isSharedCheck_1767_ = !lean_is_exclusive(v_r_1283_);
if (v_isSharedCheck_1767_ == 0)
{
lean_object* v_unused_1768_; lean_object* v_unused_1769_; lean_object* v_unused_1770_; lean_object* v_unused_1771_; lean_object* v_unused_1772_; 
v_unused_1768_ = lean_ctor_get(v_r_1283_, 4);
lean_dec(v_unused_1768_);
v_unused_1769_ = lean_ctor_get(v_r_1283_, 3);
lean_dec(v_unused_1769_);
v_unused_1770_ = lean_ctor_get(v_r_1283_, 2);
lean_dec(v_unused_1770_);
v_unused_1771_ = lean_ctor_get(v_r_1283_, 1);
lean_dec(v_unused_1771_);
v_unused_1772_ = lean_ctor_get(v_r_1283_, 0);
lean_dec(v_unused_1772_);
v___x_1616_ = v_r_1283_;
v_isShared_1617_ = v_isSharedCheck_1767_;
goto v_resetjp_1615_;
}
else
{
lean_dec(v_r_1283_);
v___x_1616_ = lean_box(0);
v_isShared_1617_ = v_isSharedCheck_1767_;
goto v_resetjp_1615_;
}
v_resetjp_1615_:
{
lean_object* v___x_1618_; lean_object* v_tree_1619_; 
v___x_1618_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_1468_, v_v_1469_, v_l_1470_, v_r_1471_);
v_tree_1619_ = lean_ctor_get(v___x_1618_, 2);
lean_inc(v_tree_1619_);
if (lean_obj_tag(v_tree_1619_) == 0)
{
lean_object* v_k_1620_; lean_object* v_v_1621_; lean_object* v_size_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; uint8_t v___x_1625_; 
v_k_1620_ = lean_ctor_get(v___x_1618_, 0);
lean_inc(v_k_1620_);
v_v_1621_ = lean_ctor_get(v___x_1618_, 1);
lean_inc(v_v_1621_);
lean_dec_ref(v___x_1618_);
v_size_1622_ = lean_ctor_get(v_tree_1619_, 0);
v___x_1623_ = lean_unsigned_to_nat(3u);
v___x_1624_ = lean_nat_mul(v___x_1623_, v_size_1622_);
v___x_1625_ = lean_nat_dec_lt(v___x_1624_, v_size_1462_);
lean_dec(v___x_1624_);
if (v___x_1625_ == 0)
{
lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1629_; 
lean_dec(v_r_1466_);
v___x_1626_ = lean_nat_add(v___x_1472_, v_size_1462_);
v___x_1627_ = lean_nat_add(v___x_1626_, v_size_1622_);
lean_dec(v___x_1626_);
if (v_isShared_1617_ == 0)
{
lean_ctor_set(v___x_1616_, 4, v_tree_1619_);
lean_ctor_set(v___x_1616_, 3, v_l_1282_);
lean_ctor_set(v___x_1616_, 2, v_v_1621_);
lean_ctor_set(v___x_1616_, 1, v_k_1620_);
lean_ctor_set(v___x_1616_, 0, v___x_1627_);
v___x_1629_ = v___x_1616_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v___x_1627_);
lean_ctor_set(v_reuseFailAlloc_1630_, 1, v_k_1620_);
lean_ctor_set(v_reuseFailAlloc_1630_, 2, v_v_1621_);
lean_ctor_set(v_reuseFailAlloc_1630_, 3, v_l_1282_);
lean_ctor_set(v_reuseFailAlloc_1630_, 4, v_tree_1619_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
return v___x_1629_;
}
}
else
{
lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1696_; 
lean_inc(v_l_1465_);
lean_inc(v_v_1464_);
lean_inc(v_k_1463_);
lean_inc(v_size_1462_);
v_isSharedCheck_1696_ = !lean_is_exclusive(v_l_1282_);
if (v_isSharedCheck_1696_ == 0)
{
lean_object* v_unused_1697_; lean_object* v_unused_1698_; lean_object* v_unused_1699_; lean_object* v_unused_1700_; lean_object* v_unused_1701_; 
v_unused_1697_ = lean_ctor_get(v_l_1282_, 4);
lean_dec(v_unused_1697_);
v_unused_1698_ = lean_ctor_get(v_l_1282_, 3);
lean_dec(v_unused_1698_);
v_unused_1699_ = lean_ctor_get(v_l_1282_, 2);
lean_dec(v_unused_1699_);
v_unused_1700_ = lean_ctor_get(v_l_1282_, 1);
lean_dec(v_unused_1700_);
v_unused_1701_ = lean_ctor_get(v_l_1282_, 0);
lean_dec(v_unused_1701_);
v___x_1632_ = v_l_1282_;
v_isShared_1633_ = v_isSharedCheck_1696_;
goto v_resetjp_1631_;
}
else
{
lean_dec(v_l_1282_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1696_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v_size_1634_; lean_object* v_size_1635_; lean_object* v_k_1636_; lean_object* v_v_1637_; lean_object* v_l_1638_; lean_object* v_r_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; uint8_t v___x_1642_; 
v_size_1634_ = lean_ctor_get(v_l_1465_, 0);
v_size_1635_ = lean_ctor_get(v_r_1466_, 0);
v_k_1636_ = lean_ctor_get(v_r_1466_, 1);
v_v_1637_ = lean_ctor_get(v_r_1466_, 2);
v_l_1638_ = lean_ctor_get(v_r_1466_, 3);
v_r_1639_ = lean_ctor_get(v_r_1466_, 4);
v___x_1640_ = lean_unsigned_to_nat(2u);
v___x_1641_ = lean_nat_mul(v___x_1640_, v_size_1634_);
v___x_1642_ = lean_nat_dec_lt(v_size_1635_, v___x_1641_);
lean_dec(v___x_1641_);
if (v___x_1642_ == 0)
{
lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1680_; 
lean_inc(v_r_1639_);
lean_inc(v_l_1638_);
lean_inc(v_v_1637_);
lean_inc(v_k_1636_);
lean_del_object(v___x_1632_);
v_isSharedCheck_1680_ = !lean_is_exclusive(v_r_1466_);
if (v_isSharedCheck_1680_ == 0)
{
lean_object* v_unused_1681_; lean_object* v_unused_1682_; lean_object* v_unused_1683_; lean_object* v_unused_1684_; lean_object* v_unused_1685_; 
v_unused_1681_ = lean_ctor_get(v_r_1466_, 4);
lean_dec(v_unused_1681_);
v_unused_1682_ = lean_ctor_get(v_r_1466_, 3);
lean_dec(v_unused_1682_);
v_unused_1683_ = lean_ctor_get(v_r_1466_, 2);
lean_dec(v_unused_1683_);
v_unused_1684_ = lean_ctor_get(v_r_1466_, 1);
lean_dec(v_unused_1684_);
v_unused_1685_ = lean_ctor_get(v_r_1466_, 0);
lean_dec(v_unused_1685_);
v___x_1644_ = v_r_1466_;
v_isShared_1645_ = v_isSharedCheck_1680_;
goto v_resetjp_1643_;
}
else
{
lean_dec(v_r_1466_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1680_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___y_1649_; lean_object* v___y_1650_; lean_object* v___y_1651_; lean_object* v___x_1668_; lean_object* v___y_1670_; 
v___x_1646_ = lean_nat_add(v___x_1472_, v_size_1462_);
lean_dec(v_size_1462_);
v___x_1647_ = lean_nat_add(v___x_1646_, v_size_1622_);
lean_dec(v___x_1646_);
v___x_1668_ = lean_nat_add(v___x_1472_, v_size_1634_);
if (lean_obj_tag(v_l_1638_) == 0)
{
lean_object* v_size_1678_; 
v_size_1678_ = lean_ctor_get(v_l_1638_, 0);
lean_inc(v_size_1678_);
v___y_1670_ = v_size_1678_;
goto v___jp_1669_;
}
else
{
lean_object* v___x_1679_; 
v___x_1679_ = lean_unsigned_to_nat(0u);
v___y_1670_ = v___x_1679_;
goto v___jp_1669_;
}
v___jp_1648_:
{
lean_object* v___x_1652_; lean_object* v___x_1654_; 
v___x_1652_ = lean_nat_add(v___y_1649_, v___y_1651_);
lean_dec(v___y_1651_);
lean_dec(v___y_1649_);
lean_inc_ref(v_tree_1619_);
if (v_isShared_1645_ == 0)
{
lean_ctor_set(v___x_1644_, 4, v_tree_1619_);
lean_ctor_set(v___x_1644_, 3, v_r_1639_);
lean_ctor_set(v___x_1644_, 2, v_v_1621_);
lean_ctor_set(v___x_1644_, 1, v_k_1620_);
lean_ctor_set(v___x_1644_, 0, v___x_1652_);
v___x_1654_ = v___x_1644_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v___x_1652_);
lean_ctor_set(v_reuseFailAlloc_1667_, 1, v_k_1620_);
lean_ctor_set(v_reuseFailAlloc_1667_, 2, v_v_1621_);
lean_ctor_set(v_reuseFailAlloc_1667_, 3, v_r_1639_);
lean_ctor_set(v_reuseFailAlloc_1667_, 4, v_tree_1619_);
v___x_1654_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1661_; 
v_isSharedCheck_1661_ = !lean_is_exclusive(v_tree_1619_);
if (v_isSharedCheck_1661_ == 0)
{
lean_object* v_unused_1662_; lean_object* v_unused_1663_; lean_object* v_unused_1664_; lean_object* v_unused_1665_; lean_object* v_unused_1666_; 
v_unused_1662_ = lean_ctor_get(v_tree_1619_, 4);
lean_dec(v_unused_1662_);
v_unused_1663_ = lean_ctor_get(v_tree_1619_, 3);
lean_dec(v_unused_1663_);
v_unused_1664_ = lean_ctor_get(v_tree_1619_, 2);
lean_dec(v_unused_1664_);
v_unused_1665_ = lean_ctor_get(v_tree_1619_, 1);
lean_dec(v_unused_1665_);
v_unused_1666_ = lean_ctor_get(v_tree_1619_, 0);
lean_dec(v_unused_1666_);
v___x_1656_ = v_tree_1619_;
v_isShared_1657_ = v_isSharedCheck_1661_;
goto v_resetjp_1655_;
}
else
{
lean_dec(v_tree_1619_);
v___x_1656_ = lean_box(0);
v_isShared_1657_ = v_isSharedCheck_1661_;
goto v_resetjp_1655_;
}
v_resetjp_1655_:
{
lean_object* v___x_1659_; 
if (v_isShared_1657_ == 0)
{
lean_ctor_set(v___x_1656_, 4, v___x_1654_);
lean_ctor_set(v___x_1656_, 3, v___y_1650_);
lean_ctor_set(v___x_1656_, 2, v_v_1637_);
lean_ctor_set(v___x_1656_, 1, v_k_1636_);
lean_ctor_set(v___x_1656_, 0, v___x_1647_);
v___x_1659_ = v___x_1656_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v___x_1647_);
lean_ctor_set(v_reuseFailAlloc_1660_, 1, v_k_1636_);
lean_ctor_set(v_reuseFailAlloc_1660_, 2, v_v_1637_);
lean_ctor_set(v_reuseFailAlloc_1660_, 3, v___y_1650_);
lean_ctor_set(v_reuseFailAlloc_1660_, 4, v___x_1654_);
v___x_1659_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
return v___x_1659_;
}
}
}
}
v___jp_1669_:
{
lean_object* v___x_1671_; lean_object* v___x_1673_; 
v___x_1671_ = lean_nat_add(v___x_1668_, v___y_1670_);
lean_dec(v___y_1670_);
lean_dec(v___x_1668_);
if (v_isShared_1617_ == 0)
{
lean_ctor_set(v___x_1616_, 4, v_l_1638_);
lean_ctor_set(v___x_1616_, 3, v_l_1465_);
lean_ctor_set(v___x_1616_, 2, v_v_1464_);
lean_ctor_set(v___x_1616_, 1, v_k_1463_);
lean_ctor_set(v___x_1616_, 0, v___x_1671_);
v___x_1673_ = v___x_1616_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v___x_1671_);
lean_ctor_set(v_reuseFailAlloc_1677_, 1, v_k_1463_);
lean_ctor_set(v_reuseFailAlloc_1677_, 2, v_v_1464_);
lean_ctor_set(v_reuseFailAlloc_1677_, 3, v_l_1465_);
lean_ctor_set(v_reuseFailAlloc_1677_, 4, v_l_1638_);
v___x_1673_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
lean_object* v___x_1674_; 
v___x_1674_ = lean_nat_add(v___x_1472_, v_size_1622_);
if (lean_obj_tag(v_r_1639_) == 0)
{
lean_object* v_size_1675_; 
v_size_1675_ = lean_ctor_get(v_r_1639_, 0);
lean_inc(v_size_1675_);
v___y_1649_ = v___x_1674_;
v___y_1650_ = v___x_1673_;
v___y_1651_ = v_size_1675_;
goto v___jp_1648_;
}
else
{
lean_object* v___x_1676_; 
v___x_1676_ = lean_unsigned_to_nat(0u);
v___y_1649_ = v___x_1674_;
v___y_1650_ = v___x_1673_;
v___y_1651_ = v___x_1676_;
goto v___jp_1648_;
}
}
}
}
}
else
{
lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1691_; 
v___x_1686_ = lean_nat_add(v___x_1472_, v_size_1462_);
lean_dec(v_size_1462_);
v___x_1687_ = lean_nat_add(v___x_1686_, v_size_1622_);
lean_dec(v___x_1686_);
v___x_1688_ = lean_nat_add(v___x_1472_, v_size_1622_);
v___x_1689_ = lean_nat_add(v___x_1688_, v_size_1635_);
lean_dec(v___x_1688_);
if (v_isShared_1617_ == 0)
{
lean_ctor_set(v___x_1616_, 4, v_tree_1619_);
lean_ctor_set(v___x_1616_, 3, v_r_1466_);
lean_ctor_set(v___x_1616_, 2, v_v_1621_);
lean_ctor_set(v___x_1616_, 1, v_k_1620_);
lean_ctor_set(v___x_1616_, 0, v___x_1689_);
v___x_1691_ = v___x_1616_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v___x_1689_);
lean_ctor_set(v_reuseFailAlloc_1695_, 1, v_k_1620_);
lean_ctor_set(v_reuseFailAlloc_1695_, 2, v_v_1621_);
lean_ctor_set(v_reuseFailAlloc_1695_, 3, v_r_1466_);
lean_ctor_set(v_reuseFailAlloc_1695_, 4, v_tree_1619_);
v___x_1691_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
lean_object* v___x_1693_; 
if (v_isShared_1633_ == 0)
{
lean_ctor_set(v___x_1632_, 4, v___x_1691_);
lean_ctor_set(v___x_1632_, 0, v___x_1687_);
v___x_1693_ = v___x_1632_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v___x_1687_);
lean_ctor_set(v_reuseFailAlloc_1694_, 1, v_k_1463_);
lean_ctor_set(v_reuseFailAlloc_1694_, 2, v_v_1464_);
lean_ctor_set(v_reuseFailAlloc_1694_, 3, v_l_1465_);
lean_ctor_set(v_reuseFailAlloc_1694_, 4, v___x_1691_);
v___x_1693_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
return v___x_1693_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_1465_) == 0)
{
lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1725_; 
lean_inc_ref(v_l_1465_);
lean_inc(v_v_1464_);
lean_inc(v_k_1463_);
lean_inc(v_size_1462_);
v_isSharedCheck_1725_ = !lean_is_exclusive(v_l_1282_);
if (v_isSharedCheck_1725_ == 0)
{
lean_object* v_unused_1726_; lean_object* v_unused_1727_; lean_object* v_unused_1728_; lean_object* v_unused_1729_; lean_object* v_unused_1730_; 
v_unused_1726_ = lean_ctor_get(v_l_1282_, 4);
lean_dec(v_unused_1726_);
v_unused_1727_ = lean_ctor_get(v_l_1282_, 3);
lean_dec(v_unused_1727_);
v_unused_1728_ = lean_ctor_get(v_l_1282_, 2);
lean_dec(v_unused_1728_);
v_unused_1729_ = lean_ctor_get(v_l_1282_, 1);
lean_dec(v_unused_1729_);
v_unused_1730_ = lean_ctor_get(v_l_1282_, 0);
lean_dec(v_unused_1730_);
v___x_1703_ = v_l_1282_;
v_isShared_1704_ = v_isSharedCheck_1725_;
goto v_resetjp_1702_;
}
else
{
lean_dec(v_l_1282_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1725_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
if (lean_obj_tag(v_r_1466_) == 0)
{
lean_object* v_k_1705_; lean_object* v_v_1706_; lean_object* v_size_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1711_; 
v_k_1705_ = lean_ctor_get(v___x_1618_, 0);
lean_inc(v_k_1705_);
v_v_1706_ = lean_ctor_get(v___x_1618_, 1);
lean_inc(v_v_1706_);
lean_dec_ref(v___x_1618_);
v_size_1707_ = lean_ctor_get(v_r_1466_, 0);
v___x_1708_ = lean_nat_add(v___x_1472_, v_size_1462_);
lean_dec(v_size_1462_);
v___x_1709_ = lean_nat_add(v___x_1472_, v_size_1707_);
if (v_isShared_1617_ == 0)
{
lean_ctor_set(v___x_1616_, 4, v_tree_1619_);
lean_ctor_set(v___x_1616_, 3, v_r_1466_);
lean_ctor_set(v___x_1616_, 2, v_v_1706_);
lean_ctor_set(v___x_1616_, 1, v_k_1705_);
lean_ctor_set(v___x_1616_, 0, v___x_1709_);
v___x_1711_ = v___x_1616_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v___x_1709_);
lean_ctor_set(v_reuseFailAlloc_1715_, 1, v_k_1705_);
lean_ctor_set(v_reuseFailAlloc_1715_, 2, v_v_1706_);
lean_ctor_set(v_reuseFailAlloc_1715_, 3, v_r_1466_);
lean_ctor_set(v_reuseFailAlloc_1715_, 4, v_tree_1619_);
v___x_1711_ = v_reuseFailAlloc_1715_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
lean_object* v___x_1713_; 
if (v_isShared_1704_ == 0)
{
lean_ctor_set(v___x_1703_, 4, v___x_1711_);
lean_ctor_set(v___x_1703_, 0, v___x_1708_);
v___x_1713_ = v___x_1703_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v___x_1708_);
lean_ctor_set(v_reuseFailAlloc_1714_, 1, v_k_1463_);
lean_ctor_set(v_reuseFailAlloc_1714_, 2, v_v_1464_);
lean_ctor_set(v_reuseFailAlloc_1714_, 3, v_l_1465_);
lean_ctor_set(v_reuseFailAlloc_1714_, 4, v___x_1711_);
v___x_1713_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
return v___x_1713_;
}
}
}
else
{
lean_object* v_k_1716_; lean_object* v_v_1717_; lean_object* v___x_1718_; lean_object* v___x_1720_; 
lean_dec(v_size_1462_);
v_k_1716_ = lean_ctor_get(v___x_1618_, 0);
lean_inc(v_k_1716_);
v_v_1717_ = lean_ctor_get(v___x_1618_, 1);
lean_inc(v_v_1717_);
lean_dec_ref(v___x_1618_);
v___x_1718_ = lean_unsigned_to_nat(3u);
if (v_isShared_1617_ == 0)
{
lean_ctor_set(v___x_1616_, 4, v_r_1466_);
lean_ctor_set(v___x_1616_, 3, v_r_1466_);
lean_ctor_set(v___x_1616_, 2, v_v_1717_);
lean_ctor_set(v___x_1616_, 1, v_k_1716_);
lean_ctor_set(v___x_1616_, 0, v___x_1472_);
v___x_1720_ = v___x_1616_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v___x_1472_);
lean_ctor_set(v_reuseFailAlloc_1724_, 1, v_k_1716_);
lean_ctor_set(v_reuseFailAlloc_1724_, 2, v_v_1717_);
lean_ctor_set(v_reuseFailAlloc_1724_, 3, v_r_1466_);
lean_ctor_set(v_reuseFailAlloc_1724_, 4, v_r_1466_);
v___x_1720_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
lean_object* v___x_1722_; 
if (v_isShared_1704_ == 0)
{
lean_ctor_set(v___x_1703_, 4, v___x_1720_);
lean_ctor_set(v___x_1703_, 0, v___x_1718_);
v___x_1722_ = v___x_1703_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v___x_1718_);
lean_ctor_set(v_reuseFailAlloc_1723_, 1, v_k_1463_);
lean_ctor_set(v_reuseFailAlloc_1723_, 2, v_v_1464_);
lean_ctor_set(v_reuseFailAlloc_1723_, 3, v_l_1465_);
lean_ctor_set(v_reuseFailAlloc_1723_, 4, v___x_1720_);
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
else
{
if (lean_obj_tag(v_r_1466_) == 0)
{
lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1755_; 
lean_inc(v_l_1465_);
lean_inc(v_v_1464_);
lean_inc(v_k_1463_);
v_isSharedCheck_1755_ = !lean_is_exclusive(v_l_1282_);
if (v_isSharedCheck_1755_ == 0)
{
lean_object* v_unused_1756_; lean_object* v_unused_1757_; lean_object* v_unused_1758_; lean_object* v_unused_1759_; lean_object* v_unused_1760_; 
v_unused_1756_ = lean_ctor_get(v_l_1282_, 4);
lean_dec(v_unused_1756_);
v_unused_1757_ = lean_ctor_get(v_l_1282_, 3);
lean_dec(v_unused_1757_);
v_unused_1758_ = lean_ctor_get(v_l_1282_, 2);
lean_dec(v_unused_1758_);
v_unused_1759_ = lean_ctor_get(v_l_1282_, 1);
lean_dec(v_unused_1759_);
v_unused_1760_ = lean_ctor_get(v_l_1282_, 0);
lean_dec(v_unused_1760_);
v___x_1732_ = v_l_1282_;
v_isShared_1733_ = v_isSharedCheck_1755_;
goto v_resetjp_1731_;
}
else
{
lean_dec(v_l_1282_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_1755_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
lean_object* v_k_1734_; lean_object* v_v_1735_; lean_object* v_k_1736_; lean_object* v_v_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1751_; 
v_k_1734_ = lean_ctor_get(v___x_1618_, 0);
lean_inc(v_k_1734_);
v_v_1735_ = lean_ctor_get(v___x_1618_, 1);
lean_inc(v_v_1735_);
lean_dec_ref(v___x_1618_);
v_k_1736_ = lean_ctor_get(v_r_1466_, 1);
v_v_1737_ = lean_ctor_get(v_r_1466_, 2);
v_isSharedCheck_1751_ = !lean_is_exclusive(v_r_1466_);
if (v_isSharedCheck_1751_ == 0)
{
lean_object* v_unused_1752_; lean_object* v_unused_1753_; lean_object* v_unused_1754_; 
v_unused_1752_ = lean_ctor_get(v_r_1466_, 4);
lean_dec(v_unused_1752_);
v_unused_1753_ = lean_ctor_get(v_r_1466_, 3);
lean_dec(v_unused_1753_);
v_unused_1754_ = lean_ctor_get(v_r_1466_, 0);
lean_dec(v_unused_1754_);
v___x_1739_ = v_r_1466_;
v_isShared_1740_ = v_isSharedCheck_1751_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_v_1737_);
lean_inc(v_k_1736_);
lean_dec(v_r_1466_);
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
lean_ctor_set(v___x_1739_, 4, v_l_1465_);
lean_ctor_set(v___x_1739_, 3, v_l_1465_);
lean_ctor_set(v___x_1739_, 2, v_v_1464_);
lean_ctor_set(v___x_1739_, 1, v_k_1463_);
lean_ctor_set(v___x_1739_, 0, v___x_1472_);
v___x_1743_ = v___x_1739_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v___x_1472_);
lean_ctor_set(v_reuseFailAlloc_1750_, 1, v_k_1463_);
lean_ctor_set(v_reuseFailAlloc_1750_, 2, v_v_1464_);
lean_ctor_set(v_reuseFailAlloc_1750_, 3, v_l_1465_);
lean_ctor_set(v_reuseFailAlloc_1750_, 4, v_l_1465_);
v___x_1743_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
lean_object* v___x_1745_; 
if (v_isShared_1617_ == 0)
{
lean_ctor_set(v___x_1616_, 4, v_l_1465_);
lean_ctor_set(v___x_1616_, 3, v_l_1465_);
lean_ctor_set(v___x_1616_, 2, v_v_1735_);
lean_ctor_set(v___x_1616_, 1, v_k_1734_);
lean_ctor_set(v___x_1616_, 0, v___x_1472_);
v___x_1745_ = v___x_1616_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1749_; 
v_reuseFailAlloc_1749_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1749_, 0, v___x_1472_);
lean_ctor_set(v_reuseFailAlloc_1749_, 1, v_k_1734_);
lean_ctor_set(v_reuseFailAlloc_1749_, 2, v_v_1735_);
lean_ctor_set(v_reuseFailAlloc_1749_, 3, v_l_1465_);
lean_ctor_set(v_reuseFailAlloc_1749_, 4, v_l_1465_);
v___x_1745_ = v_reuseFailAlloc_1749_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
lean_object* v___x_1747_; 
if (v_isShared_1733_ == 0)
{
lean_ctor_set(v___x_1732_, 4, v___x_1745_);
lean_ctor_set(v___x_1732_, 3, v___x_1743_);
lean_ctor_set(v___x_1732_, 2, v_v_1737_);
lean_ctor_set(v___x_1732_, 1, v_k_1736_);
lean_ctor_set(v___x_1732_, 0, v___x_1741_);
v___x_1747_ = v___x_1732_;
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
lean_object* v_k_1761_; lean_object* v_v_1762_; lean_object* v___x_1763_; lean_object* v___x_1765_; 
v_k_1761_ = lean_ctor_get(v___x_1618_, 0);
lean_inc(v_k_1761_);
v_v_1762_ = lean_ctor_get(v___x_1618_, 1);
lean_inc(v_v_1762_);
lean_dec_ref(v___x_1618_);
v___x_1763_ = lean_unsigned_to_nat(2u);
if (v_isShared_1617_ == 0)
{
lean_ctor_set(v___x_1616_, 4, v_r_1466_);
lean_ctor_set(v___x_1616_, 3, v_l_1282_);
lean_ctor_set(v___x_1616_, 2, v_v_1762_);
lean_ctor_set(v___x_1616_, 1, v_k_1761_);
lean_ctor_set(v___x_1616_, 0, v___x_1763_);
v___x_1765_ = v___x_1616_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v___x_1763_);
lean_ctor_set(v_reuseFailAlloc_1766_, 1, v_k_1761_);
lean_ctor_set(v_reuseFailAlloc_1766_, 2, v_v_1762_);
lean_ctor_set(v_reuseFailAlloc_1766_, 3, v_l_1282_);
lean_ctor_set(v_reuseFailAlloc_1766_, 4, v_r_1466_);
v___x_1765_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
return v___x_1765_;
}
}
}
}
}
}
}
else
{
return v_l_1282_;
}
}
else
{
return v_r_1283_;
}
}
default: 
{
lean_object* v_impl_1773_; lean_object* v___x_1774_; 
v_impl_1773_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_k_1278_, v_r_1283_);
v___x_1774_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1773_) == 0)
{
if (lean_obj_tag(v_l_1282_) == 0)
{
lean_object* v_size_1775_; lean_object* v_size_1776_; lean_object* v_k_1777_; lean_object* v_v_1778_; lean_object* v_l_1779_; lean_object* v_r_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; uint8_t v___x_1783_; 
v_size_1775_ = lean_ctor_get(v_impl_1773_, 0);
lean_inc(v_size_1775_);
v_size_1776_ = lean_ctor_get(v_l_1282_, 0);
v_k_1777_ = lean_ctor_get(v_l_1282_, 1);
v_v_1778_ = lean_ctor_get(v_l_1282_, 2);
v_l_1779_ = lean_ctor_get(v_l_1282_, 3);
v_r_1780_ = lean_ctor_get(v_l_1282_, 4);
lean_inc(v_r_1780_);
v___x_1781_ = lean_unsigned_to_nat(3u);
v___x_1782_ = lean_nat_mul(v___x_1781_, v_size_1775_);
v___x_1783_ = lean_nat_dec_lt(v___x_1782_, v_size_1776_);
lean_dec(v___x_1782_);
if (v___x_1783_ == 0)
{
lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1787_; 
lean_dec(v_r_1780_);
v___x_1784_ = lean_nat_add(v___x_1774_, v_size_1776_);
v___x_1785_ = lean_nat_add(v___x_1784_, v_size_1775_);
lean_dec(v_size_1775_);
lean_dec(v___x_1784_);
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 4, v_impl_1773_);
lean_ctor_set(v___x_1285_, 0, v___x_1785_);
v___x_1787_ = v___x_1285_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v___x_1785_);
lean_ctor_set(v_reuseFailAlloc_1788_, 1, v_k_1280_);
lean_ctor_set(v_reuseFailAlloc_1788_, 2, v_v_1281_);
lean_ctor_set(v_reuseFailAlloc_1788_, 3, v_l_1282_);
lean_ctor_set(v_reuseFailAlloc_1788_, 4, v_impl_1773_);
v___x_1787_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
return v___x_1787_;
}
}
else
{
lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1854_; 
lean_inc(v_l_1779_);
lean_inc(v_v_1778_);
lean_inc(v_k_1777_);
lean_inc(v_size_1776_);
v_isSharedCheck_1854_ = !lean_is_exclusive(v_l_1282_);
if (v_isSharedCheck_1854_ == 0)
{
lean_object* v_unused_1855_; lean_object* v_unused_1856_; lean_object* v_unused_1857_; lean_object* v_unused_1858_; lean_object* v_unused_1859_; 
v_unused_1855_ = lean_ctor_get(v_l_1282_, 4);
lean_dec(v_unused_1855_);
v_unused_1856_ = lean_ctor_get(v_l_1282_, 3);
lean_dec(v_unused_1856_);
v_unused_1857_ = lean_ctor_get(v_l_1282_, 2);
lean_dec(v_unused_1857_);
v_unused_1858_ = lean_ctor_get(v_l_1282_, 1);
lean_dec(v_unused_1858_);
v_unused_1859_ = lean_ctor_get(v_l_1282_, 0);
lean_dec(v_unused_1859_);
v___x_1790_ = v_l_1282_;
v_isShared_1791_ = v_isSharedCheck_1854_;
goto v_resetjp_1789_;
}
else
{
lean_dec(v_l_1282_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1854_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v_size_1792_; lean_object* v_size_1793_; lean_object* v_k_1794_; lean_object* v_v_1795_; lean_object* v_l_1796_; lean_object* v_r_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; uint8_t v___x_1800_; 
v_size_1792_ = lean_ctor_get(v_l_1779_, 0);
v_size_1793_ = lean_ctor_get(v_r_1780_, 0);
v_k_1794_ = lean_ctor_get(v_r_1780_, 1);
v_v_1795_ = lean_ctor_get(v_r_1780_, 2);
v_l_1796_ = lean_ctor_get(v_r_1780_, 3);
v_r_1797_ = lean_ctor_get(v_r_1780_, 4);
v___x_1798_ = lean_unsigned_to_nat(2u);
v___x_1799_ = lean_nat_mul(v___x_1798_, v_size_1792_);
v___x_1800_ = lean_nat_dec_lt(v_size_1793_, v___x_1799_);
lean_dec(v___x_1799_);
if (v___x_1800_ == 0)
{
lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1829_; 
lean_inc(v_r_1797_);
lean_inc(v_l_1796_);
lean_inc(v_v_1795_);
lean_inc(v_k_1794_);
v_isSharedCheck_1829_ = !lean_is_exclusive(v_r_1780_);
if (v_isSharedCheck_1829_ == 0)
{
lean_object* v_unused_1830_; lean_object* v_unused_1831_; lean_object* v_unused_1832_; lean_object* v_unused_1833_; lean_object* v_unused_1834_; 
v_unused_1830_ = lean_ctor_get(v_r_1780_, 4);
lean_dec(v_unused_1830_);
v_unused_1831_ = lean_ctor_get(v_r_1780_, 3);
lean_dec(v_unused_1831_);
v_unused_1832_ = lean_ctor_get(v_r_1780_, 2);
lean_dec(v_unused_1832_);
v_unused_1833_ = lean_ctor_get(v_r_1780_, 1);
lean_dec(v_unused_1833_);
v_unused_1834_ = lean_ctor_get(v_r_1780_, 0);
lean_dec(v_unused_1834_);
v___x_1802_ = v_r_1780_;
v_isShared_1803_ = v_isSharedCheck_1829_;
goto v_resetjp_1801_;
}
else
{
lean_dec(v_r_1780_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1829_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___y_1807_; lean_object* v___y_1808_; lean_object* v___y_1809_; lean_object* v___x_1817_; lean_object* v___y_1819_; 
v___x_1804_ = lean_nat_add(v___x_1774_, v_size_1776_);
lean_dec(v_size_1776_);
v___x_1805_ = lean_nat_add(v___x_1804_, v_size_1775_);
lean_dec(v___x_1804_);
v___x_1817_ = lean_nat_add(v___x_1774_, v_size_1792_);
if (lean_obj_tag(v_l_1796_) == 0)
{
lean_object* v_size_1827_; 
v_size_1827_ = lean_ctor_get(v_l_1796_, 0);
lean_inc(v_size_1827_);
v___y_1819_ = v_size_1827_;
goto v___jp_1818_;
}
else
{
lean_object* v___x_1828_; 
v___x_1828_ = lean_unsigned_to_nat(0u);
v___y_1819_ = v___x_1828_;
goto v___jp_1818_;
}
v___jp_1806_:
{
lean_object* v___x_1810_; lean_object* v___x_1812_; 
v___x_1810_ = lean_nat_add(v___y_1807_, v___y_1809_);
lean_dec(v___y_1809_);
lean_dec(v___y_1807_);
if (v_isShared_1803_ == 0)
{
lean_ctor_set(v___x_1802_, 4, v_impl_1773_);
lean_ctor_set(v___x_1802_, 3, v_r_1797_);
lean_ctor_set(v___x_1802_, 2, v_v_1281_);
lean_ctor_set(v___x_1802_, 1, v_k_1280_);
lean_ctor_set(v___x_1802_, 0, v___x_1810_);
v___x_1812_ = v___x_1802_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v___x_1810_);
lean_ctor_set(v_reuseFailAlloc_1816_, 1, v_k_1280_);
lean_ctor_set(v_reuseFailAlloc_1816_, 2, v_v_1281_);
lean_ctor_set(v_reuseFailAlloc_1816_, 3, v_r_1797_);
lean_ctor_set(v_reuseFailAlloc_1816_, 4, v_impl_1773_);
v___x_1812_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
lean_object* v___x_1814_; 
if (v_isShared_1791_ == 0)
{
lean_ctor_set(v___x_1790_, 4, v___x_1812_);
lean_ctor_set(v___x_1790_, 3, v___y_1808_);
lean_ctor_set(v___x_1790_, 2, v_v_1795_);
lean_ctor_set(v___x_1790_, 1, v_k_1794_);
lean_ctor_set(v___x_1790_, 0, v___x_1805_);
v___x_1814_ = v___x_1790_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v___x_1805_);
lean_ctor_set(v_reuseFailAlloc_1815_, 1, v_k_1794_);
lean_ctor_set(v_reuseFailAlloc_1815_, 2, v_v_1795_);
lean_ctor_set(v_reuseFailAlloc_1815_, 3, v___y_1808_);
lean_ctor_set(v_reuseFailAlloc_1815_, 4, v___x_1812_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
return v___x_1814_;
}
}
}
v___jp_1818_:
{
lean_object* v___x_1820_; lean_object* v___x_1822_; 
v___x_1820_ = lean_nat_add(v___x_1817_, v___y_1819_);
lean_dec(v___y_1819_);
lean_dec(v___x_1817_);
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 4, v_l_1796_);
lean_ctor_set(v___x_1285_, 3, v_l_1779_);
lean_ctor_set(v___x_1285_, 2, v_v_1778_);
lean_ctor_set(v___x_1285_, 1, v_k_1777_);
lean_ctor_set(v___x_1285_, 0, v___x_1820_);
v___x_1822_ = v___x_1285_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v___x_1820_);
lean_ctor_set(v_reuseFailAlloc_1826_, 1, v_k_1777_);
lean_ctor_set(v_reuseFailAlloc_1826_, 2, v_v_1778_);
lean_ctor_set(v_reuseFailAlloc_1826_, 3, v_l_1779_);
lean_ctor_set(v_reuseFailAlloc_1826_, 4, v_l_1796_);
v___x_1822_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
lean_object* v___x_1823_; 
v___x_1823_ = lean_nat_add(v___x_1774_, v_size_1775_);
lean_dec(v_size_1775_);
if (lean_obj_tag(v_r_1797_) == 0)
{
lean_object* v_size_1824_; 
v_size_1824_ = lean_ctor_get(v_r_1797_, 0);
lean_inc(v_size_1824_);
v___y_1807_ = v___x_1823_;
v___y_1808_ = v___x_1822_;
v___y_1809_ = v_size_1824_;
goto v___jp_1806_;
}
else
{
lean_object* v___x_1825_; 
v___x_1825_ = lean_unsigned_to_nat(0u);
v___y_1807_ = v___x_1823_;
v___y_1808_ = v___x_1822_;
v___y_1809_ = v___x_1825_;
goto v___jp_1806_;
}
}
}
}
}
else
{
lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1840_; 
lean_del_object(v___x_1285_);
v___x_1835_ = lean_nat_add(v___x_1774_, v_size_1776_);
lean_dec(v_size_1776_);
v___x_1836_ = lean_nat_add(v___x_1835_, v_size_1775_);
lean_dec(v___x_1835_);
v___x_1837_ = lean_nat_add(v___x_1774_, v_size_1775_);
lean_dec(v_size_1775_);
v___x_1838_ = lean_nat_add(v___x_1837_, v_size_1793_);
lean_dec(v___x_1837_);
lean_inc_ref(v_impl_1773_);
if (v_isShared_1791_ == 0)
{
lean_ctor_set(v___x_1790_, 4, v_impl_1773_);
lean_ctor_set(v___x_1790_, 3, v_r_1780_);
lean_ctor_set(v___x_1790_, 2, v_v_1281_);
lean_ctor_set(v___x_1790_, 1, v_k_1280_);
lean_ctor_set(v___x_1790_, 0, v___x_1838_);
v___x_1840_ = v___x_1790_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v___x_1838_);
lean_ctor_set(v_reuseFailAlloc_1853_, 1, v_k_1280_);
lean_ctor_set(v_reuseFailAlloc_1853_, 2, v_v_1281_);
lean_ctor_set(v_reuseFailAlloc_1853_, 3, v_r_1780_);
lean_ctor_set(v_reuseFailAlloc_1853_, 4, v_impl_1773_);
v___x_1840_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1847_; 
v_isSharedCheck_1847_ = !lean_is_exclusive(v_impl_1773_);
if (v_isSharedCheck_1847_ == 0)
{
lean_object* v_unused_1848_; lean_object* v_unused_1849_; lean_object* v_unused_1850_; lean_object* v_unused_1851_; lean_object* v_unused_1852_; 
v_unused_1848_ = lean_ctor_get(v_impl_1773_, 4);
lean_dec(v_unused_1848_);
v_unused_1849_ = lean_ctor_get(v_impl_1773_, 3);
lean_dec(v_unused_1849_);
v_unused_1850_ = lean_ctor_get(v_impl_1773_, 2);
lean_dec(v_unused_1850_);
v_unused_1851_ = lean_ctor_get(v_impl_1773_, 1);
lean_dec(v_unused_1851_);
v_unused_1852_ = lean_ctor_get(v_impl_1773_, 0);
lean_dec(v_unused_1852_);
v___x_1842_ = v_impl_1773_;
v_isShared_1843_ = v_isSharedCheck_1847_;
goto v_resetjp_1841_;
}
else
{
lean_dec(v_impl_1773_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1847_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
lean_object* v___x_1845_; 
if (v_isShared_1843_ == 0)
{
lean_ctor_set(v___x_1842_, 4, v___x_1840_);
lean_ctor_set(v___x_1842_, 3, v_l_1779_);
lean_ctor_set(v___x_1842_, 2, v_v_1778_);
lean_ctor_set(v___x_1842_, 1, v_k_1777_);
lean_ctor_set(v___x_1842_, 0, v___x_1836_);
v___x_1845_ = v___x_1842_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v___x_1836_);
lean_ctor_set(v_reuseFailAlloc_1846_, 1, v_k_1777_);
lean_ctor_set(v_reuseFailAlloc_1846_, 2, v_v_1778_);
lean_ctor_set(v_reuseFailAlloc_1846_, 3, v_l_1779_);
lean_ctor_set(v_reuseFailAlloc_1846_, 4, v___x_1840_);
v___x_1845_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
return v___x_1845_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1860_; lean_object* v___x_1861_; lean_object* v___x_1863_; 
v_size_1860_ = lean_ctor_get(v_impl_1773_, 0);
lean_inc(v_size_1860_);
v___x_1861_ = lean_nat_add(v___x_1774_, v_size_1860_);
lean_dec(v_size_1860_);
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 4, v_impl_1773_);
lean_ctor_set(v___x_1285_, 0, v___x_1861_);
v___x_1863_ = v___x_1285_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v___x_1861_);
lean_ctor_set(v_reuseFailAlloc_1864_, 1, v_k_1280_);
lean_ctor_set(v_reuseFailAlloc_1864_, 2, v_v_1281_);
lean_ctor_set(v_reuseFailAlloc_1864_, 3, v_l_1282_);
lean_ctor_set(v_reuseFailAlloc_1864_, 4, v_impl_1773_);
v___x_1863_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
return v___x_1863_;
}
}
}
else
{
if (lean_obj_tag(v_l_1282_) == 0)
{
lean_object* v_l_1865_; 
v_l_1865_ = lean_ctor_get(v_l_1282_, 3);
if (lean_obj_tag(v_l_1865_) == 0)
{
lean_object* v_r_1866_; 
lean_inc_ref(v_l_1865_);
v_r_1866_ = lean_ctor_get(v_l_1282_, 4);
lean_inc(v_r_1866_);
if (lean_obj_tag(v_r_1866_) == 0)
{
lean_object* v_size_1867_; lean_object* v_k_1868_; lean_object* v_v_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1882_; 
v_size_1867_ = lean_ctor_get(v_l_1282_, 0);
v_k_1868_ = lean_ctor_get(v_l_1282_, 1);
v_v_1869_ = lean_ctor_get(v_l_1282_, 2);
v_isSharedCheck_1882_ = !lean_is_exclusive(v_l_1282_);
if (v_isSharedCheck_1882_ == 0)
{
lean_object* v_unused_1883_; lean_object* v_unused_1884_; 
v_unused_1883_ = lean_ctor_get(v_l_1282_, 4);
lean_dec(v_unused_1883_);
v_unused_1884_ = lean_ctor_get(v_l_1282_, 3);
lean_dec(v_unused_1884_);
v___x_1871_ = v_l_1282_;
v_isShared_1872_ = v_isSharedCheck_1882_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_v_1869_);
lean_inc(v_k_1868_);
lean_inc(v_size_1867_);
lean_dec(v_l_1282_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1882_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v_size_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1877_; 
v_size_1873_ = lean_ctor_get(v_r_1866_, 0);
v___x_1874_ = lean_nat_add(v___x_1774_, v_size_1867_);
lean_dec(v_size_1867_);
v___x_1875_ = lean_nat_add(v___x_1774_, v_size_1873_);
if (v_isShared_1872_ == 0)
{
lean_ctor_set(v___x_1871_, 4, v_impl_1773_);
lean_ctor_set(v___x_1871_, 3, v_r_1866_);
lean_ctor_set(v___x_1871_, 2, v_v_1281_);
lean_ctor_set(v___x_1871_, 1, v_k_1280_);
lean_ctor_set(v___x_1871_, 0, v___x_1875_);
v___x_1877_ = v___x_1871_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v___x_1875_);
lean_ctor_set(v_reuseFailAlloc_1881_, 1, v_k_1280_);
lean_ctor_set(v_reuseFailAlloc_1881_, 2, v_v_1281_);
lean_ctor_set(v_reuseFailAlloc_1881_, 3, v_r_1866_);
lean_ctor_set(v_reuseFailAlloc_1881_, 4, v_impl_1773_);
v___x_1877_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
lean_object* v___x_1879_; 
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 4, v___x_1877_);
lean_ctor_set(v___x_1285_, 3, v_l_1865_);
lean_ctor_set(v___x_1285_, 2, v_v_1869_);
lean_ctor_set(v___x_1285_, 1, v_k_1868_);
lean_ctor_set(v___x_1285_, 0, v___x_1874_);
v___x_1879_ = v___x_1285_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v___x_1874_);
lean_ctor_set(v_reuseFailAlloc_1880_, 1, v_k_1868_);
lean_ctor_set(v_reuseFailAlloc_1880_, 2, v_v_1869_);
lean_ctor_set(v_reuseFailAlloc_1880_, 3, v_l_1865_);
lean_ctor_set(v_reuseFailAlloc_1880_, 4, v___x_1877_);
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
lean_object* v_k_1885_; lean_object* v_v_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1897_; 
v_k_1885_ = lean_ctor_get(v_l_1282_, 1);
v_v_1886_ = lean_ctor_get(v_l_1282_, 2);
v_isSharedCheck_1897_ = !lean_is_exclusive(v_l_1282_);
if (v_isSharedCheck_1897_ == 0)
{
lean_object* v_unused_1898_; lean_object* v_unused_1899_; lean_object* v_unused_1900_; 
v_unused_1898_ = lean_ctor_get(v_l_1282_, 4);
lean_dec(v_unused_1898_);
v_unused_1899_ = lean_ctor_get(v_l_1282_, 3);
lean_dec(v_unused_1899_);
v_unused_1900_ = lean_ctor_get(v_l_1282_, 0);
lean_dec(v_unused_1900_);
v___x_1888_ = v_l_1282_;
v_isShared_1889_ = v_isSharedCheck_1897_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_v_1886_);
lean_inc(v_k_1885_);
lean_dec(v_l_1282_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1897_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v___x_1890_; lean_object* v___x_1892_; 
v___x_1890_ = lean_unsigned_to_nat(3u);
if (v_isShared_1889_ == 0)
{
lean_ctor_set(v___x_1888_, 3, v_r_1866_);
lean_ctor_set(v___x_1888_, 2, v_v_1281_);
lean_ctor_set(v___x_1888_, 1, v_k_1280_);
lean_ctor_set(v___x_1888_, 0, v___x_1774_);
v___x_1892_ = v___x_1888_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v___x_1774_);
lean_ctor_set(v_reuseFailAlloc_1896_, 1, v_k_1280_);
lean_ctor_set(v_reuseFailAlloc_1896_, 2, v_v_1281_);
lean_ctor_set(v_reuseFailAlloc_1896_, 3, v_r_1866_);
lean_ctor_set(v_reuseFailAlloc_1896_, 4, v_r_1866_);
v___x_1892_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
lean_object* v___x_1894_; 
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 4, v___x_1892_);
lean_ctor_set(v___x_1285_, 3, v_l_1865_);
lean_ctor_set(v___x_1285_, 2, v_v_1886_);
lean_ctor_set(v___x_1285_, 1, v_k_1885_);
lean_ctor_set(v___x_1285_, 0, v___x_1890_);
v___x_1894_ = v___x_1285_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v___x_1890_);
lean_ctor_set(v_reuseFailAlloc_1895_, 1, v_k_1885_);
lean_ctor_set(v_reuseFailAlloc_1895_, 2, v_v_1886_);
lean_ctor_set(v_reuseFailAlloc_1895_, 3, v_l_1865_);
lean_ctor_set(v_reuseFailAlloc_1895_, 4, v___x_1892_);
v___x_1894_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
return v___x_1894_;
}
}
}
}
}
else
{
lean_object* v_r_1901_; 
v_r_1901_ = lean_ctor_get(v_l_1282_, 4);
lean_inc(v_r_1901_);
if (lean_obj_tag(v_r_1901_) == 0)
{
lean_object* v_k_1902_; lean_object* v_v_1903_; lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1926_; 
lean_inc(v_l_1865_);
v_k_1902_ = lean_ctor_get(v_l_1282_, 1);
v_v_1903_ = lean_ctor_get(v_l_1282_, 2);
v_isSharedCheck_1926_ = !lean_is_exclusive(v_l_1282_);
if (v_isSharedCheck_1926_ == 0)
{
lean_object* v_unused_1927_; lean_object* v_unused_1928_; lean_object* v_unused_1929_; 
v_unused_1927_ = lean_ctor_get(v_l_1282_, 4);
lean_dec(v_unused_1927_);
v_unused_1928_ = lean_ctor_get(v_l_1282_, 3);
lean_dec(v_unused_1928_);
v_unused_1929_ = lean_ctor_get(v_l_1282_, 0);
lean_dec(v_unused_1929_);
v___x_1905_ = v_l_1282_;
v_isShared_1906_ = v_isSharedCheck_1926_;
goto v_resetjp_1904_;
}
else
{
lean_inc(v_v_1903_);
lean_inc(v_k_1902_);
lean_dec(v_l_1282_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1926_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
lean_object* v_k_1907_; lean_object* v_v_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1922_; 
v_k_1907_ = lean_ctor_get(v_r_1901_, 1);
v_v_1908_ = lean_ctor_get(v_r_1901_, 2);
v_isSharedCheck_1922_ = !lean_is_exclusive(v_r_1901_);
if (v_isSharedCheck_1922_ == 0)
{
lean_object* v_unused_1923_; lean_object* v_unused_1924_; lean_object* v_unused_1925_; 
v_unused_1923_ = lean_ctor_get(v_r_1901_, 4);
lean_dec(v_unused_1923_);
v_unused_1924_ = lean_ctor_get(v_r_1901_, 3);
lean_dec(v_unused_1924_);
v_unused_1925_ = lean_ctor_get(v_r_1901_, 0);
lean_dec(v_unused_1925_);
v___x_1910_ = v_r_1901_;
v_isShared_1911_ = v_isSharedCheck_1922_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_v_1908_);
lean_inc(v_k_1907_);
lean_dec(v_r_1901_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1922_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
lean_object* v___x_1912_; lean_object* v___x_1914_; 
v___x_1912_ = lean_unsigned_to_nat(3u);
if (v_isShared_1911_ == 0)
{
lean_ctor_set(v___x_1910_, 4, v_l_1865_);
lean_ctor_set(v___x_1910_, 3, v_l_1865_);
lean_ctor_set(v___x_1910_, 2, v_v_1903_);
lean_ctor_set(v___x_1910_, 1, v_k_1902_);
lean_ctor_set(v___x_1910_, 0, v___x_1774_);
v___x_1914_ = v___x_1910_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v___x_1774_);
lean_ctor_set(v_reuseFailAlloc_1921_, 1, v_k_1902_);
lean_ctor_set(v_reuseFailAlloc_1921_, 2, v_v_1903_);
lean_ctor_set(v_reuseFailAlloc_1921_, 3, v_l_1865_);
lean_ctor_set(v_reuseFailAlloc_1921_, 4, v_l_1865_);
v___x_1914_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
lean_object* v___x_1916_; 
if (v_isShared_1906_ == 0)
{
lean_ctor_set(v___x_1905_, 4, v_l_1865_);
lean_ctor_set(v___x_1905_, 2, v_v_1281_);
lean_ctor_set(v___x_1905_, 1, v_k_1280_);
lean_ctor_set(v___x_1905_, 0, v___x_1774_);
v___x_1916_ = v___x_1905_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v___x_1774_);
lean_ctor_set(v_reuseFailAlloc_1920_, 1, v_k_1280_);
lean_ctor_set(v_reuseFailAlloc_1920_, 2, v_v_1281_);
lean_ctor_set(v_reuseFailAlloc_1920_, 3, v_l_1865_);
lean_ctor_set(v_reuseFailAlloc_1920_, 4, v_l_1865_);
v___x_1916_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
lean_object* v___x_1918_; 
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 4, v___x_1916_);
lean_ctor_set(v___x_1285_, 3, v___x_1914_);
lean_ctor_set(v___x_1285_, 2, v_v_1908_);
lean_ctor_set(v___x_1285_, 1, v_k_1907_);
lean_ctor_set(v___x_1285_, 0, v___x_1912_);
v___x_1918_ = v___x_1285_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v___x_1912_);
lean_ctor_set(v_reuseFailAlloc_1919_, 1, v_k_1907_);
lean_ctor_set(v_reuseFailAlloc_1919_, 2, v_v_1908_);
lean_ctor_set(v_reuseFailAlloc_1919_, 3, v___x_1914_);
lean_ctor_set(v_reuseFailAlloc_1919_, 4, v___x_1916_);
v___x_1918_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
return v___x_1918_;
}
}
}
}
}
}
else
{
lean_object* v___x_1930_; lean_object* v___x_1932_; 
v___x_1930_ = lean_unsigned_to_nat(2u);
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 4, v_r_1901_);
lean_ctor_set(v___x_1285_, 0, v___x_1930_);
v___x_1932_ = v___x_1285_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1933_; 
v_reuseFailAlloc_1933_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1933_, 0, v___x_1930_);
lean_ctor_set(v_reuseFailAlloc_1933_, 1, v_k_1280_);
lean_ctor_set(v_reuseFailAlloc_1933_, 2, v_v_1281_);
lean_ctor_set(v_reuseFailAlloc_1933_, 3, v_l_1282_);
lean_ctor_set(v_reuseFailAlloc_1933_, 4, v_r_1901_);
v___x_1932_ = v_reuseFailAlloc_1933_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
return v___x_1932_;
}
}
}
}
else
{
lean_object* v___x_1935_; 
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 4, v_l_1282_);
lean_ctor_set(v___x_1285_, 0, v___x_1774_);
v___x_1935_ = v___x_1285_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v___x_1774_);
lean_ctor_set(v_reuseFailAlloc_1936_, 1, v_k_1280_);
lean_ctor_set(v_reuseFailAlloc_1936_, 2, v_v_1281_);
lean_ctor_set(v_reuseFailAlloc_1936_, 3, v_l_1282_);
lean_ctor_set(v_reuseFailAlloc_1936_, 4, v_l_1282_);
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
else
{
return v_t_1279_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg___boxed(lean_object* v_k_1939_, lean_object* v_t_1940_){
_start:
{
lean_object* v_res_1941_; 
v_res_1941_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_k_1939_, v_t_1940_);
lean_dec_ref(v_k_1939_);
return v_res_1941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___lam__0(lean_object* v_val_1942_, lean_object* v_s_1943_){
_start:
{
lean_object* v_toRing_1944_; lean_object* v_invFn_x3f_1945_; lean_object* v_semiringId_x3f_1946_; lean_object* v_commSemiringInst_1947_; lean_object* v_commRingInst_1948_; lean_object* v_noZeroDivInst_x3f_1949_; lean_object* v_fieldInst_x3f_1950_; lean_object* v_powIdentityInst_x3f_1951_; lean_object* v_denoteEntries_1952_; lean_object* v_nextId_1953_; lean_object* v_steps_1954_; lean_object* v_queue_1955_; lean_object* v_basis_1956_; lean_object* v_diseqs_1957_; uint8_t v_recheck_1958_; lean_object* v_invSet_1959_; lean_object* v_powIdentityVarCount_1960_; lean_object* v_numEq0_x3f_1961_; uint8_t v_numEq0Updated_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_1970_; 
v_toRing_1944_ = lean_ctor_get(v_s_1943_, 0);
v_invFn_x3f_1945_ = lean_ctor_get(v_s_1943_, 1);
v_semiringId_x3f_1946_ = lean_ctor_get(v_s_1943_, 2);
v_commSemiringInst_1947_ = lean_ctor_get(v_s_1943_, 3);
v_commRingInst_1948_ = lean_ctor_get(v_s_1943_, 4);
v_noZeroDivInst_x3f_1949_ = lean_ctor_get(v_s_1943_, 5);
v_fieldInst_x3f_1950_ = lean_ctor_get(v_s_1943_, 6);
v_powIdentityInst_x3f_1951_ = lean_ctor_get(v_s_1943_, 7);
v_denoteEntries_1952_ = lean_ctor_get(v_s_1943_, 8);
v_nextId_1953_ = lean_ctor_get(v_s_1943_, 9);
v_steps_1954_ = lean_ctor_get(v_s_1943_, 10);
v_queue_1955_ = lean_ctor_get(v_s_1943_, 11);
v_basis_1956_ = lean_ctor_get(v_s_1943_, 12);
v_diseqs_1957_ = lean_ctor_get(v_s_1943_, 13);
v_recheck_1958_ = lean_ctor_get_uint8(v_s_1943_, sizeof(void*)*17);
v_invSet_1959_ = lean_ctor_get(v_s_1943_, 14);
v_powIdentityVarCount_1960_ = lean_ctor_get(v_s_1943_, 15);
v_numEq0_x3f_1961_ = lean_ctor_get(v_s_1943_, 16);
v_numEq0Updated_1962_ = lean_ctor_get_uint8(v_s_1943_, sizeof(void*)*17 + 1);
v_isSharedCheck_1970_ = !lean_is_exclusive(v_s_1943_);
if (v_isSharedCheck_1970_ == 0)
{
v___x_1964_ = v_s_1943_;
v_isShared_1965_ = v_isSharedCheck_1970_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_numEq0_x3f_1961_);
lean_inc(v_powIdentityVarCount_1960_);
lean_inc(v_invSet_1959_);
lean_inc(v_diseqs_1957_);
lean_inc(v_basis_1956_);
lean_inc(v_queue_1955_);
lean_inc(v_steps_1954_);
lean_inc(v_nextId_1953_);
lean_inc(v_denoteEntries_1952_);
lean_inc(v_powIdentityInst_x3f_1951_);
lean_inc(v_fieldInst_x3f_1950_);
lean_inc(v_noZeroDivInst_x3f_1949_);
lean_inc(v_commRingInst_1948_);
lean_inc(v_commSemiringInst_1947_);
lean_inc(v_semiringId_x3f_1946_);
lean_inc(v_invFn_x3f_1945_);
lean_inc(v_toRing_1944_);
lean_dec(v_s_1943_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_1970_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
lean_object* v___x_1966_; lean_object* v___x_1968_; 
v___x_1966_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_val_1942_, v_queue_1955_);
if (v_isShared_1965_ == 0)
{
lean_ctor_set(v___x_1964_, 11, v___x_1966_);
v___x_1968_ = v___x_1964_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v_toRing_1944_);
lean_ctor_set(v_reuseFailAlloc_1969_, 1, v_invFn_x3f_1945_);
lean_ctor_set(v_reuseFailAlloc_1969_, 2, v_semiringId_x3f_1946_);
lean_ctor_set(v_reuseFailAlloc_1969_, 3, v_commSemiringInst_1947_);
lean_ctor_set(v_reuseFailAlloc_1969_, 4, v_commRingInst_1948_);
lean_ctor_set(v_reuseFailAlloc_1969_, 5, v_noZeroDivInst_x3f_1949_);
lean_ctor_set(v_reuseFailAlloc_1969_, 6, v_fieldInst_x3f_1950_);
lean_ctor_set(v_reuseFailAlloc_1969_, 7, v_powIdentityInst_x3f_1951_);
lean_ctor_set(v_reuseFailAlloc_1969_, 8, v_denoteEntries_1952_);
lean_ctor_set(v_reuseFailAlloc_1969_, 9, v_nextId_1953_);
lean_ctor_set(v_reuseFailAlloc_1969_, 10, v_steps_1954_);
lean_ctor_set(v_reuseFailAlloc_1969_, 11, v___x_1966_);
lean_ctor_set(v_reuseFailAlloc_1969_, 12, v_basis_1956_);
lean_ctor_set(v_reuseFailAlloc_1969_, 13, v_diseqs_1957_);
lean_ctor_set(v_reuseFailAlloc_1969_, 14, v_invSet_1959_);
lean_ctor_set(v_reuseFailAlloc_1969_, 15, v_powIdentityVarCount_1960_);
lean_ctor_set(v_reuseFailAlloc_1969_, 16, v_numEq0_x3f_1961_);
lean_ctor_set_uint8(v_reuseFailAlloc_1969_, sizeof(void*)*17, v_recheck_1958_);
lean_ctor_set_uint8(v_reuseFailAlloc_1969_, sizeof(void*)*17 + 1, v_numEq0Updated_1962_);
v___x_1968_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
return v___x_1968_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___lam__0___boxed(lean_object* v_val_1971_, lean_object* v_s_1972_){
_start:
{
lean_object* v_res_1973_; 
v_res_1973_ = l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___lam__0(v_val_1971_, v_s_1972_);
lean_dec_ref(v_val_1971_);
return v_res_1973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f(lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_){
_start:
{
lean_object* v___x_1986_; 
v___x_1986_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_, v_a_1979_, v_a_1980_, v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_);
if (lean_obj_tag(v___x_1986_) == 0)
{
lean_object* v_a_1987_; lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_2026_; 
v_a_1987_ = lean_ctor_get(v___x_1986_, 0);
v_isSharedCheck_2026_ = !lean_is_exclusive(v___x_1986_);
if (v_isSharedCheck_2026_ == 0)
{
v___x_1989_ = v___x_1986_;
v_isShared_1990_ = v_isSharedCheck_2026_;
goto v_resetjp_1988_;
}
else
{
lean_inc(v_a_1987_);
lean_dec(v___x_1986_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_2026_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
lean_object* v_queue_1991_; lean_object* v___x_1992_; 
v_queue_1991_ = lean_ctor_get(v_a_1987_, 11);
lean_inc(v_queue_1991_);
lean_dec(v_a_1987_);
v___x_1992_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_queue_1991_);
lean_dec(v_queue_1991_);
if (lean_obj_tag(v___x_1992_) == 1)
{
lean_object* v_val_1993_; lean_object* v___f_1994_; lean_object* v___x_1995_; 
lean_del_object(v___x_1989_);
v_val_1993_ = lean_ctor_get(v___x_1992_, 0);
lean_inc(v_val_1993_);
v___f_1994_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1994_, 0, v_val_1993_);
v___x_1995_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_1994_, v_a_1974_, v_a_1975_);
if (lean_obj_tag(v___x_1995_) == 0)
{
lean_object* v___x_1996_; lean_object* v___x_1997_; 
lean_dec_ref_known(v___x_1995_, 1);
v___x_1996_ = lean_unsigned_to_nat(1u);
v___x_1997_ = l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg(v___x_1996_, v_a_1975_);
if (lean_obj_tag(v___x_1997_) == 0)
{
lean_object* v___x_1999_; uint8_t v_isShared_2000_; uint8_t v_isSharedCheck_2004_; 
v_isSharedCheck_2004_ = !lean_is_exclusive(v___x_1997_);
if (v_isSharedCheck_2004_ == 0)
{
lean_object* v_unused_2005_; 
v_unused_2005_ = lean_ctor_get(v___x_1997_, 0);
lean_dec(v_unused_2005_);
v___x_1999_ = v___x_1997_;
v_isShared_2000_ = v_isSharedCheck_2004_;
goto v_resetjp_1998_;
}
else
{
lean_dec(v___x_1997_);
v___x_1999_ = lean_box(0);
v_isShared_2000_ = v_isSharedCheck_2004_;
goto v_resetjp_1998_;
}
v_resetjp_1998_:
{
lean_object* v___x_2002_; 
if (v_isShared_2000_ == 0)
{
lean_ctor_set(v___x_1999_, 0, v___x_1992_);
v___x_2002_ = v___x_1999_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v___x_1992_);
v___x_2002_ = v_reuseFailAlloc_2003_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
return v___x_2002_;
}
}
}
else
{
lean_object* v_a_2006_; lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2013_; 
lean_dec_ref_known(v___x_1992_, 1);
v_a_2006_ = lean_ctor_get(v___x_1997_, 0);
v_isSharedCheck_2013_ = !lean_is_exclusive(v___x_1997_);
if (v_isSharedCheck_2013_ == 0)
{
v___x_2008_ = v___x_1997_;
v_isShared_2009_ = v_isSharedCheck_2013_;
goto v_resetjp_2007_;
}
else
{
lean_inc(v_a_2006_);
lean_dec(v___x_1997_);
v___x_2008_ = lean_box(0);
v_isShared_2009_ = v_isSharedCheck_2013_;
goto v_resetjp_2007_;
}
v_resetjp_2007_:
{
lean_object* v___x_2011_; 
if (v_isShared_2009_ == 0)
{
v___x_2011_ = v___x_2008_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v_a_2006_);
v___x_2011_ = v_reuseFailAlloc_2012_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
return v___x_2011_;
}
}
}
}
else
{
lean_object* v_a_2014_; lean_object* v___x_2016_; uint8_t v_isShared_2017_; uint8_t v_isSharedCheck_2021_; 
lean_dec_ref_known(v___x_1992_, 1);
v_a_2014_ = lean_ctor_get(v___x_1995_, 0);
v_isSharedCheck_2021_ = !lean_is_exclusive(v___x_1995_);
if (v_isSharedCheck_2021_ == 0)
{
v___x_2016_ = v___x_1995_;
v_isShared_2017_ = v_isSharedCheck_2021_;
goto v_resetjp_2015_;
}
else
{
lean_inc(v_a_2014_);
lean_dec(v___x_1995_);
v___x_2016_ = lean_box(0);
v_isShared_2017_ = v_isSharedCheck_2021_;
goto v_resetjp_2015_;
}
v_resetjp_2015_:
{
lean_object* v___x_2019_; 
if (v_isShared_2017_ == 0)
{
v___x_2019_ = v___x_2016_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v_a_2014_);
v___x_2019_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
return v___x_2019_;
}
}
}
}
else
{
lean_object* v___x_2022_; lean_object* v___x_2024_; 
lean_dec(v___x_1992_);
v___x_2022_ = lean_box(0);
if (v_isShared_1990_ == 0)
{
lean_ctor_set(v___x_1989_, 0, v___x_2022_);
v___x_2024_ = v___x_1989_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v___x_2022_);
v___x_2024_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
return v___x_2024_;
}
}
}
}
else
{
lean_object* v_a_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2034_; 
v_a_2027_ = lean_ctor_get(v___x_1986_, 0);
v_isSharedCheck_2034_ = !lean_is_exclusive(v___x_1986_);
if (v_isSharedCheck_2034_ == 0)
{
v___x_2029_ = v___x_1986_;
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_a_2027_);
lean_dec(v___x_1986_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
lean_object* v___x_2032_; 
if (v_isShared_2030_ == 0)
{
v___x_2032_ = v___x_2029_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v_a_2027_);
v___x_2032_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
return v___x_2032_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___boxed(lean_object* v_a_2035_, lean_object* v_a_2036_, lean_object* v_a_2037_, lean_object* v_a_2038_, lean_object* v_a_2039_, lean_object* v_a_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_, lean_object* v_a_2043_, lean_object* v_a_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_){
_start:
{
lean_object* v_res_2047_; 
v_res_2047_ = l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f(v_a_2035_, v_a_2036_, v_a_2037_, v_a_2038_, v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_);
lean_dec(v_a_2045_);
lean_dec_ref(v_a_2044_);
lean_dec(v_a_2043_);
lean_dec_ref(v_a_2042_);
lean_dec(v_a_2041_);
lean_dec_ref(v_a_2040_);
lean_dec(v_a_2039_);
lean_dec_ref(v_a_2038_);
lean_dec(v_a_2037_);
lean_dec(v_a_2036_);
lean_dec_ref(v_a_2035_);
return v_res_2047_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0(lean_object* v_00_u03b2_2048_, lean_object* v_k_2049_, lean_object* v_t_2050_, lean_object* v_h_2051_){
_start:
{
lean_object* v___x_2052_; 
v___x_2052_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_k_2049_, v_t_2050_);
return v___x_2052_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___boxed(lean_object* v_00_u03b2_2053_, lean_object* v_k_2054_, lean_object* v_t_2055_, lean_object* v_h_2056_){
_start:
{
lean_object* v_res_2057_; 
v_res_2057_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0(v_00_u03b2_2053_, v_k_2054_, v_t_2055_, v_h_2056_);
lean_dec_ref(v_k_2054_);
return v_res_2057_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_2058_, lean_object* v_x_2059_, lean_object* v_x_2060_, lean_object* v_x_2061_){
_start:
{
lean_object* v_ks_2062_; lean_object* v_vs_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2087_; 
v_ks_2062_ = lean_ctor_get(v_x_2058_, 0);
v_vs_2063_ = lean_ctor_get(v_x_2058_, 1);
v_isSharedCheck_2087_ = !lean_is_exclusive(v_x_2058_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2065_ = v_x_2058_;
v_isShared_2066_ = v_isSharedCheck_2087_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_vs_2063_);
lean_inc(v_ks_2062_);
lean_dec(v_x_2058_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2087_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v___x_2067_; uint8_t v___x_2068_; 
v___x_2067_ = lean_array_get_size(v_ks_2062_);
v___x_2068_ = lean_nat_dec_lt(v_x_2059_, v___x_2067_);
if (v___x_2068_ == 0)
{
lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2072_; 
lean_dec(v_x_2059_);
v___x_2069_ = lean_array_push(v_ks_2062_, v_x_2060_);
v___x_2070_ = lean_array_push(v_vs_2063_, v_x_2061_);
if (v_isShared_2066_ == 0)
{
lean_ctor_set(v___x_2065_, 1, v___x_2070_);
lean_ctor_set(v___x_2065_, 0, v___x_2069_);
v___x_2072_ = v___x_2065_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v___x_2069_);
lean_ctor_set(v_reuseFailAlloc_2073_, 1, v___x_2070_);
v___x_2072_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
return v___x_2072_;
}
}
else
{
lean_object* v_k_x27_2074_; uint8_t v___x_2075_; 
v_k_x27_2074_ = lean_array_fget_borrowed(v_ks_2062_, v_x_2059_);
v___x_2075_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_2060_, v_k_x27_2074_);
if (v___x_2075_ == 0)
{
lean_object* v___x_2077_; 
if (v_isShared_2066_ == 0)
{
v___x_2077_ = v___x_2065_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v_ks_2062_);
lean_ctor_set(v_reuseFailAlloc_2081_, 1, v_vs_2063_);
v___x_2077_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
lean_object* v___x_2078_; lean_object* v___x_2079_; 
v___x_2078_ = lean_unsigned_to_nat(1u);
v___x_2079_ = lean_nat_add(v_x_2059_, v___x_2078_);
lean_dec(v_x_2059_);
v_x_2058_ = v___x_2077_;
v_x_2059_ = v___x_2079_;
goto _start;
}
}
else
{
lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2085_; 
v___x_2082_ = lean_array_fset(v_ks_2062_, v_x_2059_, v_x_2060_);
v___x_2083_ = lean_array_fset(v_vs_2063_, v_x_2059_, v_x_2061_);
lean_dec(v_x_2059_);
if (v_isShared_2066_ == 0)
{
lean_ctor_set(v___x_2065_, 1, v___x_2083_);
lean_ctor_set(v___x_2065_, 0, v___x_2082_);
v___x_2085_ = v___x_2065_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v___x_2082_);
lean_ctor_set(v_reuseFailAlloc_2086_, 1, v___x_2083_);
v___x_2085_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
return v___x_2085_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1___redArg(lean_object* v_n_2088_, lean_object* v_k_2089_, lean_object* v_v_2090_){
_start:
{
lean_object* v___x_2091_; lean_object* v___x_2092_; 
v___x_2091_ = lean_unsigned_to_nat(0u);
v___x_2092_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1_spec__2___redArg(v_n_2088_, v___x_2091_, v_k_2089_, v_v_2090_);
return v___x_2092_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2093_; 
v___x_2093_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_2093_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(lean_object* v_x_2094_, size_t v_x_2095_, size_t v_x_2096_, lean_object* v_x_2097_, lean_object* v_x_2098_){
_start:
{
if (lean_obj_tag(v_x_2094_) == 0)
{
lean_object* v_es_2099_; size_t v___x_2100_; size_t v___x_2101_; lean_object* v_j_2102_; lean_object* v___x_2103_; uint8_t v___x_2104_; 
v_es_2099_ = lean_ctor_get(v_x_2094_, 0);
v___x_2100_ = ((size_t)31ULL);
v___x_2101_ = lean_usize_land(v_x_2095_, v___x_2100_);
v_j_2102_ = lean_usize_to_nat(v___x_2101_);
v___x_2103_ = lean_array_get_size(v_es_2099_);
v___x_2104_ = lean_nat_dec_lt(v_j_2102_, v___x_2103_);
if (v___x_2104_ == 0)
{
lean_dec(v_j_2102_);
lean_dec(v_x_2098_);
lean_dec_ref(v_x_2097_);
return v_x_2094_;
}
else
{
lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2143_; 
lean_inc_ref(v_es_2099_);
v_isSharedCheck_2143_ = !lean_is_exclusive(v_x_2094_);
if (v_isSharedCheck_2143_ == 0)
{
lean_object* v_unused_2144_; 
v_unused_2144_ = lean_ctor_get(v_x_2094_, 0);
lean_dec(v_unused_2144_);
v___x_2106_ = v_x_2094_;
v_isShared_2107_ = v_isSharedCheck_2143_;
goto v_resetjp_2105_;
}
else
{
lean_dec(v_x_2094_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2143_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
lean_object* v_v_2108_; lean_object* v___x_2109_; lean_object* v_xs_x27_2110_; lean_object* v___y_2112_; 
v_v_2108_ = lean_array_fget(v_es_2099_, v_j_2102_);
v___x_2109_ = lean_box(0);
v_xs_x27_2110_ = lean_array_fset(v_es_2099_, v_j_2102_, v___x_2109_);
switch(lean_obj_tag(v_v_2108_))
{
case 0:
{
lean_object* v_key_2117_; lean_object* v_val_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2128_; 
v_key_2117_ = lean_ctor_get(v_v_2108_, 0);
v_val_2118_ = lean_ctor_get(v_v_2108_, 1);
v_isSharedCheck_2128_ = !lean_is_exclusive(v_v_2108_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2120_ = v_v_2108_;
v_isShared_2121_ = v_isSharedCheck_2128_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_val_2118_);
lean_inc(v_key_2117_);
lean_dec(v_v_2108_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2128_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
uint8_t v___x_2122_; 
v___x_2122_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_2097_, v_key_2117_);
if (v___x_2122_ == 0)
{
lean_object* v___x_2123_; lean_object* v___x_2124_; 
lean_del_object(v___x_2120_);
v___x_2123_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2117_, v_val_2118_, v_x_2097_, v_x_2098_);
v___x_2124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2124_, 0, v___x_2123_);
v___y_2112_ = v___x_2124_;
goto v___jp_2111_;
}
else
{
lean_object* v___x_2126_; 
lean_dec(v_val_2118_);
lean_dec(v_key_2117_);
if (v_isShared_2121_ == 0)
{
lean_ctor_set(v___x_2120_, 1, v_x_2098_);
lean_ctor_set(v___x_2120_, 0, v_x_2097_);
v___x_2126_ = v___x_2120_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v_x_2097_);
lean_ctor_set(v_reuseFailAlloc_2127_, 1, v_x_2098_);
v___x_2126_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
v___y_2112_ = v___x_2126_;
goto v___jp_2111_;
}
}
}
}
case 1:
{
lean_object* v_node_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2141_; 
v_node_2129_ = lean_ctor_get(v_v_2108_, 0);
v_isSharedCheck_2141_ = !lean_is_exclusive(v_v_2108_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2131_ = v_v_2108_;
v_isShared_2132_ = v_isSharedCheck_2141_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_node_2129_);
lean_dec(v_v_2108_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2141_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
size_t v___x_2133_; size_t v___x_2134_; size_t v___x_2135_; size_t v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2139_; 
v___x_2133_ = ((size_t)5ULL);
v___x_2134_ = lean_usize_shift_right(v_x_2095_, v___x_2133_);
v___x_2135_ = ((size_t)1ULL);
v___x_2136_ = lean_usize_add(v_x_2096_, v___x_2135_);
v___x_2137_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_node_2129_, v___x_2134_, v___x_2136_, v_x_2097_, v_x_2098_);
if (v_isShared_2132_ == 0)
{
lean_ctor_set(v___x_2131_, 0, v___x_2137_);
v___x_2139_ = v___x_2131_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v___x_2137_);
v___x_2139_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
v___y_2112_ = v___x_2139_;
goto v___jp_2111_;
}
}
}
default: 
{
lean_object* v___x_2142_; 
v___x_2142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2142_, 0, v_x_2097_);
lean_ctor_set(v___x_2142_, 1, v_x_2098_);
v___y_2112_ = v___x_2142_;
goto v___jp_2111_;
}
}
v___jp_2111_:
{
lean_object* v___x_2113_; lean_object* v___x_2115_; 
v___x_2113_ = lean_array_fset(v_xs_x27_2110_, v_j_2102_, v___y_2112_);
lean_dec(v_j_2102_);
if (v_isShared_2107_ == 0)
{
lean_ctor_set(v___x_2106_, 0, v___x_2113_);
v___x_2115_ = v___x_2106_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v___x_2113_);
v___x_2115_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
return v___x_2115_;
}
}
}
}
}
else
{
lean_object* v_ks_2145_; lean_object* v_vs_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2166_; 
v_ks_2145_ = lean_ctor_get(v_x_2094_, 0);
v_vs_2146_ = lean_ctor_get(v_x_2094_, 1);
v_isSharedCheck_2166_ = !lean_is_exclusive(v_x_2094_);
if (v_isSharedCheck_2166_ == 0)
{
v___x_2148_ = v_x_2094_;
v_isShared_2149_ = v_isSharedCheck_2166_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_vs_2146_);
lean_inc(v_ks_2145_);
lean_dec(v_x_2094_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2166_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v___x_2151_; 
if (v_isShared_2149_ == 0)
{
v___x_2151_ = v___x_2148_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v_ks_2145_);
lean_ctor_set(v_reuseFailAlloc_2165_, 1, v_vs_2146_);
v___x_2151_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
lean_object* v_newNode_2152_; uint8_t v___y_2154_; size_t v___x_2160_; uint8_t v___x_2161_; 
v_newNode_2152_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1___redArg(v___x_2151_, v_x_2097_, v_x_2098_);
v___x_2160_ = ((size_t)7ULL);
v___x_2161_ = lean_usize_dec_le(v___x_2160_, v_x_2096_);
if (v___x_2161_ == 0)
{
lean_object* v___x_2162_; lean_object* v___x_2163_; uint8_t v___x_2164_; 
v___x_2162_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2152_);
v___x_2163_ = lean_unsigned_to_nat(4u);
v___x_2164_ = lean_nat_dec_lt(v___x_2162_, v___x_2163_);
lean_dec(v___x_2162_);
v___y_2154_ = v___x_2164_;
goto v___jp_2153_;
}
else
{
v___y_2154_ = v___x_2161_;
goto v___jp_2153_;
}
v___jp_2153_:
{
if (v___y_2154_ == 0)
{
lean_object* v_ks_2155_; lean_object* v_vs_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; 
v_ks_2155_ = lean_ctor_get(v_newNode_2152_, 0);
lean_inc_ref(v_ks_2155_);
v_vs_2156_ = lean_ctor_get(v_newNode_2152_, 1);
lean_inc_ref(v_vs_2156_);
lean_dec_ref(v_newNode_2152_);
v___x_2157_ = lean_unsigned_to_nat(0u);
v___x_2158_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0);
v___x_2159_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg(v_x_2096_, v_ks_2155_, v_vs_2156_, v___x_2157_, v___x_2158_);
lean_dec_ref(v_vs_2156_);
lean_dec_ref(v_ks_2155_);
return v___x_2159_;
}
else
{
return v_newNode_2152_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg(size_t v_depth_2167_, lean_object* v_keys_2168_, lean_object* v_vals_2169_, lean_object* v_i_2170_, lean_object* v_entries_2171_){
_start:
{
lean_object* v___x_2172_; uint8_t v___x_2173_; 
v___x_2172_ = lean_array_get_size(v_keys_2168_);
v___x_2173_ = lean_nat_dec_lt(v_i_2170_, v___x_2172_);
if (v___x_2173_ == 0)
{
lean_dec(v_i_2170_);
return v_entries_2171_;
}
else
{
lean_object* v_k_2174_; lean_object* v_v_2175_; uint64_t v___x_2176_; size_t v_h_2177_; size_t v___x_2178_; lean_object* v___x_2179_; size_t v___x_2180_; size_t v___x_2181_; size_t v___x_2182_; size_t v_h_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; 
v_k_2174_ = lean_array_fget_borrowed(v_keys_2168_, v_i_2170_);
v_v_2175_ = lean_array_fget_borrowed(v_vals_2169_, v_i_2170_);
v___x_2176_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_2174_);
v_h_2177_ = lean_uint64_to_usize(v___x_2176_);
v___x_2178_ = ((size_t)5ULL);
v___x_2179_ = lean_unsigned_to_nat(1u);
v___x_2180_ = ((size_t)1ULL);
v___x_2181_ = lean_usize_sub(v_depth_2167_, v___x_2180_);
v___x_2182_ = lean_usize_mul(v___x_2178_, v___x_2181_);
v_h_2183_ = lean_usize_shift_right(v_h_2177_, v___x_2182_);
v___x_2184_ = lean_nat_add(v_i_2170_, v___x_2179_);
lean_dec(v_i_2170_);
lean_inc(v_v_2175_);
lean_inc(v_k_2174_);
v___x_2185_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_entries_2171_, v_h_2183_, v_depth_2167_, v_k_2174_, v_v_2175_);
v_i_2170_ = v___x_2184_;
v_entries_2171_ = v___x_2185_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_2187_, lean_object* v_keys_2188_, lean_object* v_vals_2189_, lean_object* v_i_2190_, lean_object* v_entries_2191_){
_start:
{
size_t v_depth_boxed_2192_; lean_object* v_res_2193_; 
v_depth_boxed_2192_ = lean_unbox_usize(v_depth_2187_);
lean_dec(v_depth_2187_);
v_res_2193_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg(v_depth_boxed_2192_, v_keys_2188_, v_vals_2189_, v_i_2190_, v_entries_2191_);
lean_dec_ref(v_vals_2189_);
lean_dec_ref(v_keys_2188_);
return v_res_2193_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___boxed(lean_object* v_x_2194_, lean_object* v_x_2195_, lean_object* v_x_2196_, lean_object* v_x_2197_, lean_object* v_x_2198_){
_start:
{
size_t v_x_7232__boxed_2199_; size_t v_x_7233__boxed_2200_; lean_object* v_res_2201_; 
v_x_7232__boxed_2199_ = lean_unbox_usize(v_x_2195_);
lean_dec(v_x_2195_);
v_x_7233__boxed_2200_ = lean_unbox_usize(v_x_2196_);
lean_dec(v_x_2196_);
v_res_2201_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_x_2194_, v_x_7232__boxed_2199_, v_x_7233__boxed_2200_, v_x_2197_, v_x_2198_);
return v_res_2201_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0___redArg(lean_object* v_x_2202_, lean_object* v_x_2203_, lean_object* v_x_2204_){
_start:
{
uint64_t v___x_2205_; size_t v___x_2206_; size_t v___x_2207_; lean_object* v___x_2208_; 
v___x_2205_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_2203_);
v___x_2206_ = lean_uint64_to_usize(v___x_2205_);
v___x_2207_ = ((size_t)1ULL);
v___x_2208_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_x_2202_, v___x_2206_, v___x_2207_, v_x_2203_, v_x_2204_);
return v___x_2208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___lam__0(lean_object* v_e_2209_, lean_object* v_ringId_2210_, lean_object* v_s_2211_){
_start:
{
lean_object* v_rings_2212_; lean_object* v_typeIdOf_2213_; lean_object* v_exprToRingId_2214_; lean_object* v_semirings_2215_; lean_object* v_stypeIdOf_2216_; lean_object* v_exprToSemiringId_2217_; lean_object* v_ncRings_2218_; lean_object* v_exprToNCRingId_2219_; lean_object* v_nctypeIdOf_2220_; lean_object* v_ncSemirings_2221_; lean_object* v_exprToNCSemiringId_2222_; lean_object* v_ncstypeIdOf_2223_; lean_object* v_steps_2224_; uint8_t v_reportedMaxDegreeIssue_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2233_; 
v_rings_2212_ = lean_ctor_get(v_s_2211_, 0);
v_typeIdOf_2213_ = lean_ctor_get(v_s_2211_, 1);
v_exprToRingId_2214_ = lean_ctor_get(v_s_2211_, 2);
v_semirings_2215_ = lean_ctor_get(v_s_2211_, 3);
v_stypeIdOf_2216_ = lean_ctor_get(v_s_2211_, 4);
v_exprToSemiringId_2217_ = lean_ctor_get(v_s_2211_, 5);
v_ncRings_2218_ = lean_ctor_get(v_s_2211_, 6);
v_exprToNCRingId_2219_ = lean_ctor_get(v_s_2211_, 7);
v_nctypeIdOf_2220_ = lean_ctor_get(v_s_2211_, 8);
v_ncSemirings_2221_ = lean_ctor_get(v_s_2211_, 9);
v_exprToNCSemiringId_2222_ = lean_ctor_get(v_s_2211_, 10);
v_ncstypeIdOf_2223_ = lean_ctor_get(v_s_2211_, 11);
v_steps_2224_ = lean_ctor_get(v_s_2211_, 12);
v_reportedMaxDegreeIssue_2225_ = lean_ctor_get_uint8(v_s_2211_, sizeof(void*)*13);
v_isSharedCheck_2233_ = !lean_is_exclusive(v_s_2211_);
if (v_isSharedCheck_2233_ == 0)
{
v___x_2227_ = v_s_2211_;
v_isShared_2228_ = v_isSharedCheck_2233_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_steps_2224_);
lean_inc(v_ncstypeIdOf_2223_);
lean_inc(v_exprToNCSemiringId_2222_);
lean_inc(v_ncSemirings_2221_);
lean_inc(v_nctypeIdOf_2220_);
lean_inc(v_exprToNCRingId_2219_);
lean_inc(v_ncRings_2218_);
lean_inc(v_exprToSemiringId_2217_);
lean_inc(v_stypeIdOf_2216_);
lean_inc(v_semirings_2215_);
lean_inc(v_exprToRingId_2214_);
lean_inc(v_typeIdOf_2213_);
lean_inc(v_rings_2212_);
lean_dec(v_s_2211_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2233_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v___x_2229_; lean_object* v___x_2231_; 
v___x_2229_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0___redArg(v_exprToRingId_2214_, v_e_2209_, v_ringId_2210_);
if (v_isShared_2228_ == 0)
{
lean_ctor_set(v___x_2227_, 2, v___x_2229_);
v___x_2231_ = v___x_2227_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v_rings_2212_);
lean_ctor_set(v_reuseFailAlloc_2232_, 1, v_typeIdOf_2213_);
lean_ctor_set(v_reuseFailAlloc_2232_, 2, v___x_2229_);
lean_ctor_set(v_reuseFailAlloc_2232_, 3, v_semirings_2215_);
lean_ctor_set(v_reuseFailAlloc_2232_, 4, v_stypeIdOf_2216_);
lean_ctor_set(v_reuseFailAlloc_2232_, 5, v_exprToSemiringId_2217_);
lean_ctor_set(v_reuseFailAlloc_2232_, 6, v_ncRings_2218_);
lean_ctor_set(v_reuseFailAlloc_2232_, 7, v_exprToNCRingId_2219_);
lean_ctor_set(v_reuseFailAlloc_2232_, 8, v_nctypeIdOf_2220_);
lean_ctor_set(v_reuseFailAlloc_2232_, 9, v_ncSemirings_2221_);
lean_ctor_set(v_reuseFailAlloc_2232_, 10, v_exprToNCSemiringId_2222_);
lean_ctor_set(v_reuseFailAlloc_2232_, 11, v_ncstypeIdOf_2223_);
lean_ctor_set(v_reuseFailAlloc_2232_, 12, v_steps_2224_);
lean_ctor_set_uint8(v_reuseFailAlloc_2232_, sizeof(void*)*13, v_reportedMaxDegreeIssue_2225_);
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
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__1(void){
_start:
{
lean_object* v___x_2235_; lean_object* v___x_2236_; 
v___x_2235_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__0));
v___x_2236_ = l_Lean_stringToMessageData(v___x_2235_);
return v___x_2236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(lean_object* v_e_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_){
_start:
{
lean_object* v___x_2250_; 
v___x_2250_ = l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg(v_e_2237_, v_a_2239_, v_a_2244_);
if (lean_obj_tag(v___x_2250_) == 0)
{
lean_object* v_a_2251_; 
v_a_2251_ = lean_ctor_get(v___x_2250_, 0);
lean_inc(v_a_2251_);
lean_dec_ref_known(v___x_2250_, 1);
if (lean_obj_tag(v_a_2251_) == 1)
{
lean_object* v_ringId_2252_; lean_object* v_val_2253_; uint8_t v___x_2254_; 
v_ringId_2252_ = lean_ctor_get(v_a_2238_, 0);
v_val_2253_ = lean_ctor_get(v_a_2251_, 0);
lean_inc(v_val_2253_);
lean_dec_ref_known(v_a_2251_, 1);
v___x_2254_ = lean_nat_dec_eq(v_val_2253_, v_ringId_2252_);
lean_dec(v_val_2253_);
if (v___x_2254_ == 0)
{
lean_object* v___x_2255_; 
v___x_2255_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_2240_);
if (lean_obj_tag(v___x_2255_) == 0)
{
lean_object* v_a_2256_; uint8_t v___x_2257_; 
v_a_2256_ = lean_ctor_get(v___x_2255_, 0);
lean_inc(v_a_2256_);
lean_dec_ref_known(v___x_2255_, 1);
v___x_2257_ = lean_unbox(v_a_2256_);
lean_dec(v_a_2256_);
if (v___x_2257_ == 0)
{
lean_dec_ref(v_e_2237_);
goto v___jp_2247_;
}
else
{
lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; 
v___x_2258_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__1);
v___x_2259_ = l_Lean_indentExpr(v_e_2237_);
v___x_2260_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2260_, 0, v___x_2258_);
lean_ctor_set(v___x_2260_, 1, v___x_2259_);
v___x_2261_ = l_Lean_Meta_Sym_reportIssue(v___x_2260_, v_a_2240_, v_a_2241_, v_a_2242_, v_a_2243_, v_a_2244_, v_a_2245_);
if (lean_obj_tag(v___x_2261_) == 0)
{
lean_dec_ref_known(v___x_2261_, 1);
goto v___jp_2247_;
}
else
{
return v___x_2261_;
}
}
}
else
{
lean_object* v_a_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2269_; 
lean_dec_ref(v_e_2237_);
v_a_2262_ = lean_ctor_get(v___x_2255_, 0);
v_isSharedCheck_2269_ = !lean_is_exclusive(v___x_2255_);
if (v_isSharedCheck_2269_ == 0)
{
v___x_2264_ = v___x_2255_;
v_isShared_2265_ = v_isSharedCheck_2269_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_a_2262_);
lean_dec(v___x_2255_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2269_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v___x_2267_; 
if (v_isShared_2265_ == 0)
{
v___x_2267_ = v___x_2264_;
goto v_reusejp_2266_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v_a_2262_);
v___x_2267_ = v_reuseFailAlloc_2268_;
goto v_reusejp_2266_;
}
v_reusejp_2266_:
{
return v___x_2267_;
}
}
}
}
else
{
lean_dec_ref(v_e_2237_);
goto v___jp_2247_;
}
}
else
{
lean_object* v_ringId_2270_; lean_object* v___f_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; 
lean_dec(v_a_2251_);
v_ringId_2270_ = lean_ctor_get(v_a_2238_, 0);
lean_inc(v_ringId_2270_);
v___f_2271_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2271_, 0, v_e_2237_);
lean_closure_set(v___f_2271_, 1, v_ringId_2270_);
v___x_2272_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_2273_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2272_, v___f_2271_, v_a_2239_);
return v___x_2273_;
}
}
else
{
lean_object* v_a_2274_; lean_object* v___x_2276_; uint8_t v_isShared_2277_; uint8_t v_isSharedCheck_2281_; 
lean_dec_ref(v_e_2237_);
v_a_2274_ = lean_ctor_get(v___x_2250_, 0);
v_isSharedCheck_2281_ = !lean_is_exclusive(v___x_2250_);
if (v_isSharedCheck_2281_ == 0)
{
v___x_2276_ = v___x_2250_;
v_isShared_2277_ = v_isSharedCheck_2281_;
goto v_resetjp_2275_;
}
else
{
lean_inc(v_a_2274_);
lean_dec(v___x_2250_);
v___x_2276_ = lean_box(0);
v_isShared_2277_ = v_isSharedCheck_2281_;
goto v_resetjp_2275_;
}
v_resetjp_2275_:
{
lean_object* v___x_2279_; 
if (v_isShared_2277_ == 0)
{
v___x_2279_ = v___x_2276_;
goto v_reusejp_2278_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v_a_2274_);
v___x_2279_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2278_;
}
v_reusejp_2278_:
{
return v___x_2279_;
}
}
}
v___jp_2247_:
{
lean_object* v___x_2248_; lean_object* v___x_2249_; 
v___x_2248_ = lean_box(0);
v___x_2249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2249_, 0, v___x_2248_);
return v___x_2249_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___boxed(lean_object* v_e_2282_, lean_object* v_a_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_){
_start:
{
lean_object* v_res_2292_; 
v_res_2292_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(v_e_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_);
lean_dec(v_a_2290_);
lean_dec_ref(v_a_2289_);
lean_dec(v_a_2288_);
lean_dec_ref(v_a_2287_);
lean_dec(v_a_2286_);
lean_dec_ref(v_a_2285_);
lean_dec(v_a_2284_);
lean_dec_ref(v_a_2283_);
return v_res_2292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId(lean_object* v_e_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_){
_start:
{
lean_object* v___x_2306_; 
v___x_2306_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(v_e_2293_, v_a_2294_, v_a_2295_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_);
return v___x_2306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___boxed(lean_object* v_e_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_, lean_object* v_a_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_, lean_object* v_a_2318_, lean_object* v_a_2319_){
_start:
{
lean_object* v_res_2320_; 
v_res_2320_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId(v_e_2307_, v_a_2308_, v_a_2309_, v_a_2310_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_, v_a_2317_, v_a_2318_);
lean_dec(v_a_2318_);
lean_dec_ref(v_a_2317_);
lean_dec(v_a_2316_);
lean_dec_ref(v_a_2315_);
lean_dec(v_a_2314_);
lean_dec_ref(v_a_2313_);
lean_dec(v_a_2312_);
lean_dec_ref(v_a_2311_);
lean_dec(v_a_2310_);
lean_dec(v_a_2309_);
lean_dec_ref(v_a_2308_);
return v_res_2320_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0(lean_object* v_00_u03b2_2321_, lean_object* v_x_2322_, lean_object* v_x_2323_, lean_object* v_x_2324_){
_start:
{
lean_object* v___x_2325_; 
v___x_2325_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0___redArg(v_x_2322_, v_x_2323_, v_x_2324_);
return v___x_2325_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0(lean_object* v_00_u03b2_2326_, lean_object* v_x_2327_, size_t v_x_2328_, size_t v_x_2329_, lean_object* v_x_2330_, lean_object* v_x_2331_){
_start:
{
lean_object* v___x_2332_; 
v___x_2332_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_x_2327_, v_x_2328_, v_x_2329_, v_x_2330_, v_x_2331_);
return v___x_2332_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2333_, lean_object* v_x_2334_, lean_object* v_x_2335_, lean_object* v_x_2336_, lean_object* v_x_2337_, lean_object* v_x_2338_){
_start:
{
size_t v_x_7511__boxed_2339_; size_t v_x_7512__boxed_2340_; lean_object* v_res_2341_; 
v_x_7511__boxed_2339_ = lean_unbox_usize(v_x_2335_);
lean_dec(v_x_2335_);
v_x_7512__boxed_2340_ = lean_unbox_usize(v_x_2336_);
lean_dec(v_x_2336_);
v_res_2341_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0(v_00_u03b2_2333_, v_x_2334_, v_x_7511__boxed_2339_, v_x_7512__boxed_2340_, v_x_2337_, v_x_2338_);
return v_res_2341_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2342_, lean_object* v_n_2343_, lean_object* v_k_2344_, lean_object* v_v_2345_){
_start:
{
lean_object* v___x_2346_; 
v___x_2346_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1___redArg(v_n_2343_, v_k_2344_, v_v_2345_);
return v___x_2346_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_2347_, size_t v_depth_2348_, lean_object* v_keys_2349_, lean_object* v_vals_2350_, lean_object* v_heq_2351_, lean_object* v_i_2352_, lean_object* v_entries_2353_){
_start:
{
lean_object* v___x_2354_; 
v___x_2354_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg(v_depth_2348_, v_keys_2349_, v_vals_2350_, v_i_2352_, v_entries_2353_);
return v___x_2354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2355_, lean_object* v_depth_2356_, lean_object* v_keys_2357_, lean_object* v_vals_2358_, lean_object* v_heq_2359_, lean_object* v_i_2360_, lean_object* v_entries_2361_){
_start:
{
size_t v_depth_boxed_2362_; lean_object* v_res_2363_; 
v_depth_boxed_2362_ = lean_unbox_usize(v_depth_2356_);
lean_dec(v_depth_2356_);
v_res_2363_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2(v_00_u03b2_2355_, v_depth_boxed_2362_, v_keys_2357_, v_vals_2358_, v_heq_2359_, v_i_2360_, v_entries_2361_);
lean_dec_ref(v_vals_2358_);
lean_dec_ref(v_keys_2357_);
return v_res_2363_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2364_, lean_object* v_x_2365_, lean_object* v_x_2366_, lean_object* v_x_2367_, lean_object* v_x_2368_){
_start:
{
lean_object* v___x_2369_; 
v___x_2369_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1_spec__2___redArg(v_x_2365_, v_x_2366_, v_x_2367_, v_x_2368_);
return v___x_2369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__0(lean_object* v_e_2370_, lean_object* v___f_2371_, lean_object* v___f_2372_, lean_object* v_size_2373_, lean_object* v_s_2374_){
_start:
{
lean_object* v_id_2375_; lean_object* v_type_2376_; lean_object* v_u_2377_; lean_object* v_ringInst_2378_; lean_object* v_semiringInst_2379_; lean_object* v_charInst_x3f_2380_; lean_object* v_addFn_x3f_2381_; lean_object* v_mulFn_x3f_2382_; lean_object* v_subFn_x3f_2383_; lean_object* v_negFn_x3f_2384_; lean_object* v_powFn_x3f_2385_; lean_object* v_intCastFn_x3f_2386_; lean_object* v_natCastFn_x3f_2387_; lean_object* v_one_x3f_2388_; lean_object* v_vars_2389_; lean_object* v_varMap_2390_; lean_object* v_denote_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2400_; 
v_id_2375_ = lean_ctor_get(v_s_2374_, 0);
v_type_2376_ = lean_ctor_get(v_s_2374_, 1);
v_u_2377_ = lean_ctor_get(v_s_2374_, 2);
v_ringInst_2378_ = lean_ctor_get(v_s_2374_, 3);
v_semiringInst_2379_ = lean_ctor_get(v_s_2374_, 4);
v_charInst_x3f_2380_ = lean_ctor_get(v_s_2374_, 5);
v_addFn_x3f_2381_ = lean_ctor_get(v_s_2374_, 6);
v_mulFn_x3f_2382_ = lean_ctor_get(v_s_2374_, 7);
v_subFn_x3f_2383_ = lean_ctor_get(v_s_2374_, 8);
v_negFn_x3f_2384_ = lean_ctor_get(v_s_2374_, 9);
v_powFn_x3f_2385_ = lean_ctor_get(v_s_2374_, 10);
v_intCastFn_x3f_2386_ = lean_ctor_get(v_s_2374_, 11);
v_natCastFn_x3f_2387_ = lean_ctor_get(v_s_2374_, 12);
v_one_x3f_2388_ = lean_ctor_get(v_s_2374_, 13);
v_vars_2389_ = lean_ctor_get(v_s_2374_, 14);
v_varMap_2390_ = lean_ctor_get(v_s_2374_, 15);
v_denote_2391_ = lean_ctor_get(v_s_2374_, 16);
v_isSharedCheck_2400_ = !lean_is_exclusive(v_s_2374_);
if (v_isSharedCheck_2400_ == 0)
{
v___x_2393_ = v_s_2374_;
v_isShared_2394_ = v_isSharedCheck_2400_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_denote_2391_);
lean_inc(v_varMap_2390_);
lean_inc(v_vars_2389_);
lean_inc(v_one_x3f_2388_);
lean_inc(v_natCastFn_x3f_2387_);
lean_inc(v_intCastFn_x3f_2386_);
lean_inc(v_powFn_x3f_2385_);
lean_inc(v_negFn_x3f_2384_);
lean_inc(v_subFn_x3f_2383_);
lean_inc(v_mulFn_x3f_2382_);
lean_inc(v_addFn_x3f_2381_);
lean_inc(v_charInst_x3f_2380_);
lean_inc(v_semiringInst_2379_);
lean_inc(v_ringInst_2378_);
lean_inc(v_u_2377_);
lean_inc(v_type_2376_);
lean_inc(v_id_2375_);
lean_dec(v_s_2374_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2400_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2398_; 
lean_inc_ref(v_e_2370_);
v___x_2395_ = l_Lean_PersistentArray_push___redArg(v_vars_2389_, v_e_2370_);
v___x_2396_ = l_Lean_PersistentHashMap_insert___redArg(v___f_2371_, v___f_2372_, v_varMap_2390_, v_e_2370_, v_size_2373_);
if (v_isShared_2394_ == 0)
{
lean_ctor_set(v___x_2393_, 15, v___x_2396_);
lean_ctor_set(v___x_2393_, 14, v___x_2395_);
v___x_2398_ = v___x_2393_;
goto v_reusejp_2397_;
}
else
{
lean_object* v_reuseFailAlloc_2399_; 
v_reuseFailAlloc_2399_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_2399_, 0, v_id_2375_);
lean_ctor_set(v_reuseFailAlloc_2399_, 1, v_type_2376_);
lean_ctor_set(v_reuseFailAlloc_2399_, 2, v_u_2377_);
lean_ctor_set(v_reuseFailAlloc_2399_, 3, v_ringInst_2378_);
lean_ctor_set(v_reuseFailAlloc_2399_, 4, v_semiringInst_2379_);
lean_ctor_set(v_reuseFailAlloc_2399_, 5, v_charInst_x3f_2380_);
lean_ctor_set(v_reuseFailAlloc_2399_, 6, v_addFn_x3f_2381_);
lean_ctor_set(v_reuseFailAlloc_2399_, 7, v_mulFn_x3f_2382_);
lean_ctor_set(v_reuseFailAlloc_2399_, 8, v_subFn_x3f_2383_);
lean_ctor_set(v_reuseFailAlloc_2399_, 9, v_negFn_x3f_2384_);
lean_ctor_set(v_reuseFailAlloc_2399_, 10, v_powFn_x3f_2385_);
lean_ctor_set(v_reuseFailAlloc_2399_, 11, v_intCastFn_x3f_2386_);
lean_ctor_set(v_reuseFailAlloc_2399_, 12, v_natCastFn_x3f_2387_);
lean_ctor_set(v_reuseFailAlloc_2399_, 13, v_one_x3f_2388_);
lean_ctor_set(v_reuseFailAlloc_2399_, 14, v___x_2395_);
lean_ctor_set(v_reuseFailAlloc_2399_, 15, v___x_2396_);
lean_ctor_set(v_reuseFailAlloc_2399_, 16, v_denote_2391_);
v___x_2398_ = v_reuseFailAlloc_2399_;
goto v_reusejp_2397_;
}
v_reusejp_2397_:
{
return v___x_2398_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__1(lean_object* v_toPure_2401_, lean_object* v_size_2402_, lean_object* v_____r_2403_){
_start:
{
lean_object* v___x_2404_; 
v___x_2404_ = lean_apply_2(v_toPure_2401_, lean_box(0), v_size_2402_);
return v___x_2404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__2(lean_object* v_e_2405_, lean_object* v_inst_2406_, lean_object* v_toBind_2407_, lean_object* v___f_2408_, lean_object* v_____r_2409_){
_start:
{
lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; 
v___x_2410_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_2411_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_SolverExtension_markTerm___boxed), 14, 3);
lean_closure_set(v___x_2411_, 0, lean_box(0));
lean_closure_set(v___x_2411_, 1, v___x_2410_);
lean_closure_set(v___x_2411_, 2, v_e_2405_);
v___x_2412_ = lean_apply_2(v_inst_2406_, lean_box(0), v___x_2411_);
v___x_2413_ = lean_apply_4(v_toBind_2407_, lean_box(0), lean_box(0), v___x_2412_, v___f_2408_);
return v___x_2413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__3(lean_object* v_inst_2414_, lean_object* v_e_2415_, lean_object* v_toBind_2416_, lean_object* v___f_2417_, lean_object* v_____r_2418_){
_start:
{
lean_object* v___x_2419_; lean_object* v___x_2420_; 
v___x_2419_ = lean_apply_1(v_inst_2414_, v_e_2415_);
v___x_2420_ = lean_apply_4(v_toBind_2416_, lean_box(0), lean_box(0), v___x_2419_, v___f_2417_);
return v___x_2420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__4(lean_object* v___f_2421_, lean_object* v___f_2422_, lean_object* v_e_2423_, lean_object* v_toPure_2424_, lean_object* v_inst_2425_, lean_object* v_toBind_2426_, lean_object* v_inst_2427_, lean_object* v_modifyRing_2428_, lean_object* v_s_2429_){
_start:
{
lean_object* v_vars_2430_; lean_object* v_varMap_2431_; lean_object* v___x_2432_; 
v_vars_2430_ = lean_ctor_get(v_s_2429_, 14);
lean_inc_ref(v_vars_2430_);
v_varMap_2431_ = lean_ctor_get(v_s_2429_, 15);
lean_inc_ref(v_varMap_2431_);
lean_dec_ref(v_s_2429_);
lean_inc_ref(v_e_2423_);
lean_inc_ref(v___f_2422_);
lean_inc_ref(v___f_2421_);
v___x_2432_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_2421_, v___f_2422_, v_varMap_2431_, v_e_2423_);
lean_dec_ref(v_varMap_2431_);
if (lean_obj_tag(v___x_2432_) == 1)
{
lean_object* v_val_2433_; lean_object* v___x_2434_; 
lean_dec_ref(v_vars_2430_);
lean_dec(v_modifyRing_2428_);
lean_dec(v_inst_2427_);
lean_dec(v_toBind_2426_);
lean_dec(v_inst_2425_);
lean_dec_ref(v_e_2423_);
lean_dec_ref(v___f_2422_);
lean_dec_ref(v___f_2421_);
v_val_2433_ = lean_ctor_get(v___x_2432_, 0);
lean_inc(v_val_2433_);
lean_dec_ref_known(v___x_2432_, 1);
v___x_2434_ = lean_apply_2(v_toPure_2424_, lean_box(0), v_val_2433_);
return v___x_2434_;
}
else
{
lean_object* v_size_2435_; lean_object* v___f_2436_; lean_object* v___f_2437_; lean_object* v___f_2438_; lean_object* v___f_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; 
lean_dec(v___x_2432_);
v_size_2435_ = lean_ctor_get(v_vars_2430_, 2);
lean_inc_n(v_size_2435_, 2);
lean_dec_ref(v_vars_2430_);
lean_inc_ref_n(v_e_2423_, 2);
v___f_2436_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2436_, 0, v_e_2423_);
lean_closure_set(v___f_2436_, 1, v___f_2421_);
lean_closure_set(v___f_2436_, 2, v___f_2422_);
lean_closure_set(v___f_2436_, 3, v_size_2435_);
v___f_2437_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2437_, 0, v_toPure_2424_);
lean_closure_set(v___f_2437_, 1, v_size_2435_);
lean_inc_n(v_toBind_2426_, 2);
v___f_2438_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2438_, 0, v_e_2423_);
lean_closure_set(v___f_2438_, 1, v_inst_2425_);
lean_closure_set(v___f_2438_, 2, v_toBind_2426_);
lean_closure_set(v___f_2438_, 3, v___f_2437_);
v___f_2439_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__3), 5, 4);
lean_closure_set(v___f_2439_, 0, v_inst_2427_);
lean_closure_set(v___f_2439_, 1, v_e_2423_);
lean_closure_set(v___f_2439_, 2, v_toBind_2426_);
lean_closure_set(v___f_2439_, 3, v___f_2438_);
v___x_2440_ = lean_apply_1(v_modifyRing_2428_, v___f_2436_);
v___x_2441_ = lean_apply_4(v_toBind_2426_, lean_box(0), lean_box(0), v___x_2440_, v___f_2439_);
return v___x_2441_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg(lean_object* v_inst_2444_, lean_object* v_inst_2445_, lean_object* v_inst_2446_, lean_object* v_inst_2447_, lean_object* v_e_2448_){
_start:
{
lean_object* v_toApplicative_2449_; lean_object* v_toBind_2450_; lean_object* v_getRing_2451_; lean_object* v_modifyRing_2452_; lean_object* v_toPure_2453_; lean_object* v___f_2454_; lean_object* v___f_2455_; lean_object* v___f_2456_; lean_object* v___x_2457_; 
v_toApplicative_2449_ = lean_ctor_get(v_inst_2445_, 0);
lean_inc_ref(v_toApplicative_2449_);
v_toBind_2450_ = lean_ctor_get(v_inst_2445_, 1);
lean_inc_n(v_toBind_2450_, 2);
lean_dec_ref(v_inst_2445_);
v_getRing_2451_ = lean_ctor_get(v_inst_2446_, 0);
lean_inc(v_getRing_2451_);
v_modifyRing_2452_ = lean_ctor_get(v_inst_2446_, 1);
lean_inc(v_modifyRing_2452_);
lean_dec_ref(v_inst_2446_);
v_toPure_2453_ = lean_ctor_get(v_toApplicative_2449_, 1);
lean_inc(v_toPure_2453_);
lean_dec_ref(v_toApplicative_2449_);
v___f_2454_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___closed__0));
v___f_2455_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___closed__1));
v___f_2456_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__4), 9, 8);
lean_closure_set(v___f_2456_, 0, v___f_2454_);
lean_closure_set(v___f_2456_, 1, v___f_2455_);
lean_closure_set(v___f_2456_, 2, v_e_2448_);
lean_closure_set(v___f_2456_, 3, v_toPure_2453_);
lean_closure_set(v___f_2456_, 4, v_inst_2444_);
lean_closure_set(v___f_2456_, 5, v_toBind_2450_);
lean_closure_set(v___f_2456_, 6, v_inst_2447_);
lean_closure_set(v___f_2456_, 7, v_modifyRing_2452_);
v___x_2457_ = lean_apply_4(v_toBind_2450_, lean_box(0), lean_box(0), v_getRing_2451_, v___f_2456_);
return v___x_2457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore(lean_object* v_m_2458_, lean_object* v_inst_2459_, lean_object* v_inst_2460_, lean_object* v_inst_2461_, lean_object* v_inst_2462_, lean_object* v_e_2463_){
_start:
{
lean_object* v___x_2464_; 
v___x_2464_ = l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg(v_inst_2459_, v_inst_2460_, v_inst_2461_, v_inst_2462_, v_e_2463_);
return v___x_2464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___lam__0(lean_object* v_e_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_){
_start:
{
lean_object* v___x_2478_; 
v___x_2478_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(v_e_2465_, v___y_2466_, v___y_2467_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_);
return v___x_2478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___lam__0___boxed(lean_object* v_e_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_){
_start:
{
lean_object* v_res_2492_; 
v_res_2492_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___lam__0(v_e_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_);
lean_dec(v___y_2490_);
lean_dec_ref(v___y_2489_);
lean_dec(v___y_2488_);
lean_dec_ref(v___y_2487_);
lean_dec(v___y_2486_);
lean_dec_ref(v___y_2485_);
lean_dec(v___y_2484_);
lean_dec_ref(v___y_2483_);
lean_dec(v___y_2482_);
lean_dec(v___y_2481_);
lean_dec_ref(v___y_2480_);
return v_res_2492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkVar_spec__0___lam__0(lean_object* v_e_2495_, lean_object* v_size_2496_, lean_object* v_s_2497_){
_start:
{
lean_object* v_toRing_2498_; lean_object* v_invFn_x3f_2499_; lean_object* v_semiringId_x3f_2500_; lean_object* v_commSemiringInst_2501_; lean_object* v_commRingInst_2502_; lean_object* v_noZeroDivInst_x3f_2503_; lean_object* v_fieldInst_x3f_2504_; lean_object* v_powIdentityInst_x3f_2505_; lean_object* v_denoteEntries_2506_; lean_object* v_nextId_2507_; lean_object* v_steps_2508_; lean_object* v_queue_2509_; lean_object* v_basis_2510_; lean_object* v_diseqs_2511_; uint8_t v_recheck_2512_; lean_object* v_invSet_2513_; lean_object* v_powIdentityVarCount_2514_; lean_object* v_numEq0_x3f_2515_; uint8_t v_numEq0Updated_2516_; lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2549_; 
v_toRing_2498_ = lean_ctor_get(v_s_2497_, 0);
v_invFn_x3f_2499_ = lean_ctor_get(v_s_2497_, 1);
v_semiringId_x3f_2500_ = lean_ctor_get(v_s_2497_, 2);
v_commSemiringInst_2501_ = lean_ctor_get(v_s_2497_, 3);
v_commRingInst_2502_ = lean_ctor_get(v_s_2497_, 4);
v_noZeroDivInst_x3f_2503_ = lean_ctor_get(v_s_2497_, 5);
v_fieldInst_x3f_2504_ = lean_ctor_get(v_s_2497_, 6);
v_powIdentityInst_x3f_2505_ = lean_ctor_get(v_s_2497_, 7);
v_denoteEntries_2506_ = lean_ctor_get(v_s_2497_, 8);
v_nextId_2507_ = lean_ctor_get(v_s_2497_, 9);
v_steps_2508_ = lean_ctor_get(v_s_2497_, 10);
v_queue_2509_ = lean_ctor_get(v_s_2497_, 11);
v_basis_2510_ = lean_ctor_get(v_s_2497_, 12);
v_diseqs_2511_ = lean_ctor_get(v_s_2497_, 13);
v_recheck_2512_ = lean_ctor_get_uint8(v_s_2497_, sizeof(void*)*17);
v_invSet_2513_ = lean_ctor_get(v_s_2497_, 14);
v_powIdentityVarCount_2514_ = lean_ctor_get(v_s_2497_, 15);
v_numEq0_x3f_2515_ = lean_ctor_get(v_s_2497_, 16);
v_numEq0Updated_2516_ = lean_ctor_get_uint8(v_s_2497_, sizeof(void*)*17 + 1);
v_isSharedCheck_2549_ = !lean_is_exclusive(v_s_2497_);
if (v_isSharedCheck_2549_ == 0)
{
v___x_2518_ = v_s_2497_;
v_isShared_2519_ = v_isSharedCheck_2549_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_numEq0_x3f_2515_);
lean_inc(v_powIdentityVarCount_2514_);
lean_inc(v_invSet_2513_);
lean_inc(v_diseqs_2511_);
lean_inc(v_basis_2510_);
lean_inc(v_queue_2509_);
lean_inc(v_steps_2508_);
lean_inc(v_nextId_2507_);
lean_inc(v_denoteEntries_2506_);
lean_inc(v_powIdentityInst_x3f_2505_);
lean_inc(v_fieldInst_x3f_2504_);
lean_inc(v_noZeroDivInst_x3f_2503_);
lean_inc(v_commRingInst_2502_);
lean_inc(v_commSemiringInst_2501_);
lean_inc(v_semiringId_x3f_2500_);
lean_inc(v_invFn_x3f_2499_);
lean_inc(v_toRing_2498_);
lean_dec(v_s_2497_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2549_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
lean_object* v_id_2520_; lean_object* v_type_2521_; lean_object* v_u_2522_; lean_object* v_ringInst_2523_; lean_object* v_semiringInst_2524_; lean_object* v_charInst_x3f_2525_; lean_object* v_addFn_x3f_2526_; lean_object* v_mulFn_x3f_2527_; lean_object* v_subFn_x3f_2528_; lean_object* v_negFn_x3f_2529_; lean_object* v_powFn_x3f_2530_; lean_object* v_intCastFn_x3f_2531_; lean_object* v_natCastFn_x3f_2532_; lean_object* v_one_x3f_2533_; lean_object* v_vars_2534_; lean_object* v_varMap_2535_; lean_object* v_denote_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2548_; 
v_id_2520_ = lean_ctor_get(v_toRing_2498_, 0);
v_type_2521_ = lean_ctor_get(v_toRing_2498_, 1);
v_u_2522_ = lean_ctor_get(v_toRing_2498_, 2);
v_ringInst_2523_ = lean_ctor_get(v_toRing_2498_, 3);
v_semiringInst_2524_ = lean_ctor_get(v_toRing_2498_, 4);
v_charInst_x3f_2525_ = lean_ctor_get(v_toRing_2498_, 5);
v_addFn_x3f_2526_ = lean_ctor_get(v_toRing_2498_, 6);
v_mulFn_x3f_2527_ = lean_ctor_get(v_toRing_2498_, 7);
v_subFn_x3f_2528_ = lean_ctor_get(v_toRing_2498_, 8);
v_negFn_x3f_2529_ = lean_ctor_get(v_toRing_2498_, 9);
v_powFn_x3f_2530_ = lean_ctor_get(v_toRing_2498_, 10);
v_intCastFn_x3f_2531_ = lean_ctor_get(v_toRing_2498_, 11);
v_natCastFn_x3f_2532_ = lean_ctor_get(v_toRing_2498_, 12);
v_one_x3f_2533_ = lean_ctor_get(v_toRing_2498_, 13);
v_vars_2534_ = lean_ctor_get(v_toRing_2498_, 14);
v_varMap_2535_ = lean_ctor_get(v_toRing_2498_, 15);
v_denote_2536_ = lean_ctor_get(v_toRing_2498_, 16);
v_isSharedCheck_2548_ = !lean_is_exclusive(v_toRing_2498_);
if (v_isSharedCheck_2548_ == 0)
{
v___x_2538_ = v_toRing_2498_;
v_isShared_2539_ = v_isSharedCheck_2548_;
goto v_resetjp_2537_;
}
else
{
lean_inc(v_denote_2536_);
lean_inc(v_varMap_2535_);
lean_inc(v_vars_2534_);
lean_inc(v_one_x3f_2533_);
lean_inc(v_natCastFn_x3f_2532_);
lean_inc(v_intCastFn_x3f_2531_);
lean_inc(v_powFn_x3f_2530_);
lean_inc(v_negFn_x3f_2529_);
lean_inc(v_subFn_x3f_2528_);
lean_inc(v_mulFn_x3f_2527_);
lean_inc(v_addFn_x3f_2526_);
lean_inc(v_charInst_x3f_2525_);
lean_inc(v_semiringInst_2524_);
lean_inc(v_ringInst_2523_);
lean_inc(v_u_2522_);
lean_inc(v_type_2521_);
lean_inc(v_id_2520_);
lean_dec(v_toRing_2498_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2548_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2543_; 
lean_inc_ref(v_e_2495_);
v___x_2540_ = l_Lean_PersistentArray_push___redArg(v_vars_2534_, v_e_2495_);
v___x_2541_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0___redArg(v_varMap_2535_, v_e_2495_, v_size_2496_);
if (v_isShared_2539_ == 0)
{
lean_ctor_set(v___x_2538_, 15, v___x_2541_);
lean_ctor_set(v___x_2538_, 14, v___x_2540_);
v___x_2543_ = v___x_2538_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2547_; 
v_reuseFailAlloc_2547_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_2547_, 0, v_id_2520_);
lean_ctor_set(v_reuseFailAlloc_2547_, 1, v_type_2521_);
lean_ctor_set(v_reuseFailAlloc_2547_, 2, v_u_2522_);
lean_ctor_set(v_reuseFailAlloc_2547_, 3, v_ringInst_2523_);
lean_ctor_set(v_reuseFailAlloc_2547_, 4, v_semiringInst_2524_);
lean_ctor_set(v_reuseFailAlloc_2547_, 5, v_charInst_x3f_2525_);
lean_ctor_set(v_reuseFailAlloc_2547_, 6, v_addFn_x3f_2526_);
lean_ctor_set(v_reuseFailAlloc_2547_, 7, v_mulFn_x3f_2527_);
lean_ctor_set(v_reuseFailAlloc_2547_, 8, v_subFn_x3f_2528_);
lean_ctor_set(v_reuseFailAlloc_2547_, 9, v_negFn_x3f_2529_);
lean_ctor_set(v_reuseFailAlloc_2547_, 10, v_powFn_x3f_2530_);
lean_ctor_set(v_reuseFailAlloc_2547_, 11, v_intCastFn_x3f_2531_);
lean_ctor_set(v_reuseFailAlloc_2547_, 12, v_natCastFn_x3f_2532_);
lean_ctor_set(v_reuseFailAlloc_2547_, 13, v_one_x3f_2533_);
lean_ctor_set(v_reuseFailAlloc_2547_, 14, v___x_2540_);
lean_ctor_set(v_reuseFailAlloc_2547_, 15, v___x_2541_);
lean_ctor_set(v_reuseFailAlloc_2547_, 16, v_denote_2536_);
v___x_2543_ = v_reuseFailAlloc_2547_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
lean_object* v___x_2545_; 
if (v_isShared_2519_ == 0)
{
lean_ctor_set(v___x_2518_, 0, v___x_2543_);
v___x_2545_ = v___x_2518_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v___x_2543_);
lean_ctor_set(v_reuseFailAlloc_2546_, 1, v_invFn_x3f_2499_);
lean_ctor_set(v_reuseFailAlloc_2546_, 2, v_semiringId_x3f_2500_);
lean_ctor_set(v_reuseFailAlloc_2546_, 3, v_commSemiringInst_2501_);
lean_ctor_set(v_reuseFailAlloc_2546_, 4, v_commRingInst_2502_);
lean_ctor_set(v_reuseFailAlloc_2546_, 5, v_noZeroDivInst_x3f_2503_);
lean_ctor_set(v_reuseFailAlloc_2546_, 6, v_fieldInst_x3f_2504_);
lean_ctor_set(v_reuseFailAlloc_2546_, 7, v_powIdentityInst_x3f_2505_);
lean_ctor_set(v_reuseFailAlloc_2546_, 8, v_denoteEntries_2506_);
lean_ctor_set(v_reuseFailAlloc_2546_, 9, v_nextId_2507_);
lean_ctor_set(v_reuseFailAlloc_2546_, 10, v_steps_2508_);
lean_ctor_set(v_reuseFailAlloc_2546_, 11, v_queue_2509_);
lean_ctor_set(v_reuseFailAlloc_2546_, 12, v_basis_2510_);
lean_ctor_set(v_reuseFailAlloc_2546_, 13, v_diseqs_2511_);
lean_ctor_set(v_reuseFailAlloc_2546_, 14, v_invSet_2513_);
lean_ctor_set(v_reuseFailAlloc_2546_, 15, v_powIdentityVarCount_2514_);
lean_ctor_set(v_reuseFailAlloc_2546_, 16, v_numEq0_x3f_2515_);
lean_ctor_set_uint8(v_reuseFailAlloc_2546_, sizeof(void*)*17, v_recheck_2512_);
lean_ctor_set_uint8(v_reuseFailAlloc_2546_, sizeof(void*)*17 + 1, v_numEq0Updated_2516_);
v___x_2545_ = v_reuseFailAlloc_2546_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
return v___x_2545_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkVar_spec__0(lean_object* v_e_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_){
_start:
{
lean_object* v___x_2563_; 
v___x_2563_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_);
if (lean_obj_tag(v___x_2563_) == 0)
{
lean_object* v_a_2564_; lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2614_; 
v_a_2564_ = lean_ctor_get(v___x_2563_, 0);
v_isSharedCheck_2614_ = !lean_is_exclusive(v___x_2563_);
if (v_isSharedCheck_2614_ == 0)
{
v___x_2566_ = v___x_2563_;
v_isShared_2567_ = v_isSharedCheck_2614_;
goto v_resetjp_2565_;
}
else
{
lean_inc(v_a_2564_);
lean_dec(v___x_2563_);
v___x_2566_ = lean_box(0);
v_isShared_2567_ = v_isSharedCheck_2614_;
goto v_resetjp_2565_;
}
v_resetjp_2565_:
{
lean_object* v_toRing_2568_; lean_object* v_vars_2569_; lean_object* v_varMap_2570_; lean_object* v___x_2571_; 
v_toRing_2568_ = lean_ctor_get(v_a_2564_, 0);
lean_inc_ref(v_toRing_2568_);
lean_dec(v_a_2564_);
v_vars_2569_ = lean_ctor_get(v_toRing_2568_, 14);
lean_inc_ref(v_vars_2569_);
v_varMap_2570_ = lean_ctor_get(v_toRing_2568_, 15);
lean_inc_ref(v_varMap_2570_);
lean_dec_ref(v_toRing_2568_);
v___x_2571_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(v_varMap_2570_, v_e_2550_);
lean_dec_ref(v_varMap_2570_);
if (lean_obj_tag(v___x_2571_) == 1)
{
lean_object* v_val_2572_; lean_object* v___x_2574_; 
lean_dec_ref(v_vars_2569_);
lean_dec_ref(v_e_2550_);
v_val_2572_ = lean_ctor_get(v___x_2571_, 0);
lean_inc(v_val_2572_);
lean_dec_ref_known(v___x_2571_, 1);
if (v_isShared_2567_ == 0)
{
lean_ctor_set(v___x_2566_, 0, v_val_2572_);
v___x_2574_ = v___x_2566_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v_val_2572_);
v___x_2574_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
return v___x_2574_;
}
}
else
{
lean_object* v_size_2576_; lean_object* v___f_2577_; lean_object* v___x_2578_; 
lean_dec(v___x_2571_);
lean_del_object(v___x_2566_);
v_size_2576_ = lean_ctor_get(v_vars_2569_, 2);
lean_inc_n(v_size_2576_, 2);
lean_dec_ref(v_vars_2569_);
lean_inc_ref(v_e_2550_);
v___f_2577_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkVar_spec__0___lam__0), 3, 2);
lean_closure_set(v___f_2577_, 0, v_e_2550_);
lean_closure_set(v___f_2577_, 1, v_size_2576_);
v___x_2578_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_2577_, v___y_2551_, v___y_2552_);
if (lean_obj_tag(v___x_2578_) == 0)
{
lean_object* v___x_2579_; 
lean_dec_ref_known(v___x_2578_, 1);
lean_inc_ref(v_e_2550_);
v___x_2579_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(v_e_2550_, v___y_2551_, v___y_2552_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_);
if (lean_obj_tag(v___x_2579_) == 0)
{
lean_object* v___x_2580_; lean_object* v___x_2581_; 
lean_dec_ref_known(v___x_2579_, 1);
v___x_2580_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_2581_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_2580_, v_e_2550_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_);
if (lean_obj_tag(v___x_2581_) == 0)
{
lean_object* v___x_2583_; uint8_t v_isShared_2584_; uint8_t v_isSharedCheck_2588_; 
v_isSharedCheck_2588_ = !lean_is_exclusive(v___x_2581_);
if (v_isSharedCheck_2588_ == 0)
{
lean_object* v_unused_2589_; 
v_unused_2589_ = lean_ctor_get(v___x_2581_, 0);
lean_dec(v_unused_2589_);
v___x_2583_ = v___x_2581_;
v_isShared_2584_ = v_isSharedCheck_2588_;
goto v_resetjp_2582_;
}
else
{
lean_dec(v___x_2581_);
v___x_2583_ = lean_box(0);
v_isShared_2584_ = v_isSharedCheck_2588_;
goto v_resetjp_2582_;
}
v_resetjp_2582_:
{
lean_object* v___x_2586_; 
if (v_isShared_2584_ == 0)
{
lean_ctor_set(v___x_2583_, 0, v_size_2576_);
v___x_2586_ = v___x_2583_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v_size_2576_);
v___x_2586_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
return v___x_2586_;
}
}
}
else
{
lean_object* v_a_2590_; lean_object* v___x_2592_; uint8_t v_isShared_2593_; uint8_t v_isSharedCheck_2597_; 
lean_dec(v_size_2576_);
v_a_2590_ = lean_ctor_get(v___x_2581_, 0);
v_isSharedCheck_2597_ = !lean_is_exclusive(v___x_2581_);
if (v_isSharedCheck_2597_ == 0)
{
v___x_2592_ = v___x_2581_;
v_isShared_2593_ = v_isSharedCheck_2597_;
goto v_resetjp_2591_;
}
else
{
lean_inc(v_a_2590_);
lean_dec(v___x_2581_);
v___x_2592_ = lean_box(0);
v_isShared_2593_ = v_isSharedCheck_2597_;
goto v_resetjp_2591_;
}
v_resetjp_2591_:
{
lean_object* v___x_2595_; 
if (v_isShared_2593_ == 0)
{
v___x_2595_ = v___x_2592_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v_a_2590_);
v___x_2595_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
return v___x_2595_;
}
}
}
}
else
{
lean_object* v_a_2598_; lean_object* v___x_2600_; uint8_t v_isShared_2601_; uint8_t v_isSharedCheck_2605_; 
lean_dec(v_size_2576_);
lean_dec_ref(v_e_2550_);
v_a_2598_ = lean_ctor_get(v___x_2579_, 0);
v_isSharedCheck_2605_ = !lean_is_exclusive(v___x_2579_);
if (v_isSharedCheck_2605_ == 0)
{
v___x_2600_ = v___x_2579_;
v_isShared_2601_ = v_isSharedCheck_2605_;
goto v_resetjp_2599_;
}
else
{
lean_inc(v_a_2598_);
lean_dec(v___x_2579_);
v___x_2600_ = lean_box(0);
v_isShared_2601_ = v_isSharedCheck_2605_;
goto v_resetjp_2599_;
}
v_resetjp_2599_:
{
lean_object* v___x_2603_; 
if (v_isShared_2601_ == 0)
{
v___x_2603_ = v___x_2600_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v_a_2598_);
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
lean_dec(v_size_2576_);
lean_dec_ref(v_e_2550_);
v_a_2606_ = lean_ctor_get(v___x_2578_, 0);
v_isSharedCheck_2613_ = !lean_is_exclusive(v___x_2578_);
if (v_isSharedCheck_2613_ == 0)
{
v___x_2608_ = v___x_2578_;
v_isShared_2609_ = v_isSharedCheck_2613_;
goto v_resetjp_2607_;
}
else
{
lean_inc(v_a_2606_);
lean_dec(v___x_2578_);
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
}
}
else
{
lean_object* v_a_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2622_; 
lean_dec_ref(v_e_2550_);
v_a_2615_ = lean_ctor_get(v___x_2563_, 0);
v_isSharedCheck_2622_ = !lean_is_exclusive(v___x_2563_);
if (v_isSharedCheck_2622_ == 0)
{
v___x_2617_ = v___x_2563_;
v_isShared_2618_ = v_isSharedCheck_2622_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_a_2615_);
lean_dec(v___x_2563_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2622_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
lean_object* v___x_2620_; 
if (v_isShared_2618_ == 0)
{
v___x_2620_ = v___x_2617_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v_a_2615_);
v___x_2620_ = v_reuseFailAlloc_2621_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
return v___x_2620_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkVar_spec__0___boxed(lean_object* v_e_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_){
_start:
{
lean_object* v_res_2636_; 
v_res_2636_ = l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkVar_spec__0(v_e_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_);
lean_dec(v___y_2634_);
lean_dec_ref(v___y_2633_);
lean_dec(v___y_2632_);
lean_dec_ref(v___y_2631_);
lean_dec(v___y_2630_);
lean_dec_ref(v___y_2629_);
lean_dec(v___y_2628_);
lean_dec_ref(v___y_2627_);
lean_dec(v___y_2626_);
lean_dec(v___y_2625_);
lean_dec_ref(v___y_2624_);
return v_res_2636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVar(lean_object* v_e_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_){
_start:
{
lean_object* v___x_2650_; 
v___x_2650_ = l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkVar_spec__0(v_e_2637_, v_a_2638_, v_a_2639_, v_a_2640_, v_a_2641_, v_a_2642_, v_a_2643_, v_a_2644_, v_a_2645_, v_a_2646_, v_a_2647_, v_a_2648_);
return v___x_2650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVar___boxed(lean_object* v_e_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_){
_start:
{
lean_object* v_res_2664_; 
v_res_2664_ = l_Lean_Meta_Grind_Arith_CommRing_mkVar(v_e_2651_, v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_, v_a_2656_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_, v_a_2662_);
lean_dec(v_a_2662_);
lean_dec_ref(v_a_2661_);
lean_dec(v_a_2660_);
lean_dec_ref(v_a_2659_);
lean_dec(v_a_2658_);
lean_dec_ref(v_a_2657_);
lean_dec(v_a_2656_);
lean_dec_ref(v_a_2655_);
lean_dec(v_a_2654_);
lean_dec(v_a_2653_);
lean_dec_ref(v_a_2652_);
return v_res_2664_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_SynthInstance(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadRing(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Arith_Poly(uint8_t builtin);
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
res = runtime_initialize_Lean_Meta_Sym_Arith_Poly(builtin);
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
lean_object* initialize_Lean_Meta_Sym_Arith_Poly(uint8_t builtin);
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
res = initialize_Lean_Meta_Sym_Arith_Poly(builtin);
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
