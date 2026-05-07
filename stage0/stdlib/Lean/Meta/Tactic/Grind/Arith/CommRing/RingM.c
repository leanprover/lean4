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
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
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
v_ringMaxDegree_115_ = lean_ctor_get(v_a_111_, 6);
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
lean_dec_ref(v___x_131_);
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
lean_dec_ref(v___x_418_);
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
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_808_; size_t v___x_809_; size_t v___x_810_; 
v___x_808_ = ((size_t)5ULL);
v___x_809_ = ((size_t)1ULL);
v___x_810_ = lean_usize_shift_left(v___x_809_, v___x_808_);
return v___x_810_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_811_; size_t v___x_812_; size_t v___x_813_; 
v___x_811_ = ((size_t)1ULL);
v___x_812_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__0);
v___x_813_ = lean_usize_sub(v___x_812_, v___x_811_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg(lean_object* v_x_814_, size_t v_x_815_, lean_object* v_x_816_){
_start:
{
if (lean_obj_tag(v_x_814_) == 0)
{
lean_object* v_es_817_; lean_object* v___x_818_; size_t v___x_819_; size_t v___x_820_; size_t v___x_821_; lean_object* v_j_822_; lean_object* v___x_823_; 
v_es_817_ = lean_ctor_get(v_x_814_, 0);
v___x_818_ = lean_box(2);
v___x_819_ = ((size_t)5ULL);
v___x_820_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__1);
v___x_821_ = lean_usize_land(v_x_815_, v___x_820_);
v_j_822_ = lean_usize_to_nat(v___x_821_);
v___x_823_ = lean_array_get_borrowed(v___x_818_, v_es_817_, v_j_822_);
lean_dec(v_j_822_);
switch(lean_obj_tag(v___x_823_))
{
case 0:
{
lean_object* v_key_824_; lean_object* v_val_825_; uint8_t v___x_826_; 
v_key_824_ = lean_ctor_get(v___x_823_, 0);
v_val_825_ = lean_ctor_get(v___x_823_, 1);
v___x_826_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_816_, v_key_824_);
if (v___x_826_ == 0)
{
lean_object* v___x_827_; 
v___x_827_ = lean_box(0);
return v___x_827_;
}
else
{
lean_object* v___x_828_; 
lean_inc(v_val_825_);
v___x_828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_828_, 0, v_val_825_);
return v___x_828_;
}
}
case 1:
{
lean_object* v_node_829_; size_t v___x_830_; 
v_node_829_ = lean_ctor_get(v___x_823_, 0);
v___x_830_ = lean_usize_shift_right(v_x_815_, v___x_819_);
v_x_814_ = v_node_829_;
v_x_815_ = v___x_830_;
goto _start;
}
default: 
{
lean_object* v___x_832_; 
v___x_832_ = lean_box(0);
return v___x_832_;
}
}
}
else
{
lean_object* v_ks_833_; lean_object* v_vs_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
v_ks_833_ = lean_ctor_get(v_x_814_, 0);
v_vs_834_ = lean_ctor_get(v_x_814_, 1);
v___x_835_ = lean_unsigned_to_nat(0u);
v___x_836_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_833_, v_vs_834_, v___x_835_, v_x_816_);
return v___x_836_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_837_, lean_object* v_x_838_, lean_object* v_x_839_){
_start:
{
size_t v_x_867__boxed_840_; lean_object* v_res_841_; 
v_x_867__boxed_840_ = lean_unbox_usize(v_x_838_);
lean_dec(v_x_838_);
v_res_841_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg(v_x_837_, v_x_867__boxed_840_, v_x_839_);
lean_dec_ref(v_x_839_);
lean_dec_ref(v_x_837_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(lean_object* v_x_842_, lean_object* v_x_843_){
_start:
{
uint64_t v___x_844_; size_t v___x_845_; lean_object* v___x_846_; 
v___x_844_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_843_);
v___x_845_ = lean_uint64_to_usize(v___x_844_);
v___x_846_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg(v_x_842_, v___x_845_, v_x_843_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg___boxed(lean_object* v_x_847_, lean_object* v_x_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(v_x_847_, v_x_848_);
lean_dec_ref(v_x_848_);
lean_dec_ref(v_x_847_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg(lean_object* v_e_850_, lean_object* v_a_851_, lean_object* v_a_852_){
_start:
{
lean_object* v___x_854_; 
v___x_854_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_851_, v_a_852_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_object* v_a_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_864_; 
v_a_855_ = lean_ctor_get(v___x_854_, 0);
v_isSharedCheck_864_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_864_ == 0)
{
v___x_857_ = v___x_854_;
v_isShared_858_ = v_isSharedCheck_864_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_a_855_);
lean_dec(v___x_854_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_864_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v_exprToRingId_859_; lean_object* v___x_860_; lean_object* v___x_862_; 
v_exprToRingId_859_ = lean_ctor_get(v_a_855_, 2);
lean_inc_ref(v_exprToRingId_859_);
lean_dec(v_a_855_);
v___x_860_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(v_exprToRingId_859_, v_e_850_);
lean_dec_ref(v_exprToRingId_859_);
if (v_isShared_858_ == 0)
{
lean_ctor_set(v___x_857_, 0, v___x_860_);
v___x_862_ = v___x_857_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v___x_860_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
return v___x_862_;
}
}
}
else
{
lean_object* v_a_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_872_; 
v_a_865_ = lean_ctor_get(v___x_854_, 0);
v_isSharedCheck_872_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_872_ == 0)
{
v___x_867_ = v___x_854_;
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_a_865_);
lean_dec(v___x_854_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_870_; 
if (v_isShared_868_ == 0)
{
v___x_870_ = v___x_867_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v_a_865_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg___boxed(lean_object* v_e_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg(v_e_873_, v_a_874_, v_a_875_);
lean_dec_ref(v_a_875_);
lean_dec(v_a_874_);
lean_dec_ref(v_e_873_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f(lean_object* v_e_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_){
_start:
{
lean_object* v___x_890_; 
v___x_890_ = l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg(v_e_878_, v_a_879_, v_a_887_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___boxed(lean_object* v_e_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f(v_e_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_);
lean_dec(v_a_901_);
lean_dec_ref(v_a_900_);
lean_dec(v_a_899_);
lean_dec_ref(v_a_898_);
lean_dec(v_a_897_);
lean_dec_ref(v_a_896_);
lean_dec(v_a_895_);
lean_dec_ref(v_a_894_);
lean_dec(v_a_893_);
lean_dec(v_a_892_);
lean_dec_ref(v_e_891_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0(lean_object* v_00_u03b2_904_, lean_object* v_x_905_, lean_object* v_x_906_){
_start:
{
lean_object* v___x_907_; 
v___x_907_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(v_x_905_, v_x_906_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___boxed(lean_object* v_00_u03b2_908_, lean_object* v_x_909_, lean_object* v_x_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0(v_00_u03b2_908_, v_x_909_, v_x_910_);
lean_dec_ref(v_x_910_);
lean_dec_ref(v_x_909_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_912_, lean_object* v_x_913_, size_t v_x_914_, lean_object* v_x_915_){
_start:
{
lean_object* v___x_916_; 
v___x_916_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg(v_x_913_, v_x_914_, v_x_915_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_917_, lean_object* v_x_918_, lean_object* v_x_919_, lean_object* v_x_920_){
_start:
{
size_t v_x_984__boxed_921_; lean_object* v_res_922_; 
v_x_984__boxed_921_ = lean_unbox_usize(v_x_919_);
lean_dec(v_x_919_);
v_res_922_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0(v_00_u03b2_917_, v_x_918_, v_x_984__boxed_921_, v_x_920_);
lean_dec_ref(v_x_920_);
lean_dec_ref(v_x_918_);
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_923_, lean_object* v_keys_924_, lean_object* v_vals_925_, lean_object* v_heq_926_, lean_object* v_i_927_, lean_object* v_k_928_){
_start:
{
lean_object* v___x_929_; 
v___x_929_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_924_, v_vals_925_, v_i_927_, v_k_928_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_930_, lean_object* v_keys_931_, lean_object* v_vals_932_, lean_object* v_heq_933_, lean_object* v_i_934_, lean_object* v_k_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_930_, v_keys_931_, v_vals_932_, v_heq_933_, v_i_934_, v_k_935_);
lean_dec_ref(v_k_935_);
lean_dec_ref(v_vals_932_);
lean_dec_ref(v_keys_931_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg___lam__0(lean_object* v_toPure_937_, lean_object* v_____do__lift_938_){
_start:
{
lean_object* v_charInst_x3f_942_; 
v_charInst_x3f_942_ = lean_ctor_get(v_____do__lift_938_, 5);
lean_inc(v_charInst_x3f_942_);
lean_dec_ref(v_____do__lift_938_);
if (lean_obj_tag(v_charInst_x3f_942_) == 1)
{
lean_object* v_val_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_954_; 
v_val_943_ = lean_ctor_get(v_charInst_x3f_942_, 0);
v_isSharedCheck_954_ = !lean_is_exclusive(v_charInst_x3f_942_);
if (v_isSharedCheck_954_ == 0)
{
v___x_945_ = v_charInst_x3f_942_;
v_isShared_946_ = v_isSharedCheck_954_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_val_943_);
lean_dec(v_charInst_x3f_942_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_954_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v_snd_947_; lean_object* v___x_948_; uint8_t v___x_949_; 
v_snd_947_ = lean_ctor_get(v_val_943_, 1);
lean_inc(v_snd_947_);
lean_dec(v_val_943_);
v___x_948_ = lean_unsigned_to_nat(0u);
v___x_949_ = lean_nat_dec_eq(v_snd_947_, v___x_948_);
if (v___x_949_ == 0)
{
lean_object* v___x_951_; 
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 0, v_snd_947_);
v___x_951_ = v___x_945_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v_snd_947_);
v___x_951_ = v_reuseFailAlloc_953_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
lean_object* v___x_952_; 
v___x_952_ = lean_apply_2(v_toPure_937_, lean_box(0), v___x_951_);
return v___x_952_;
}
}
else
{
lean_dec(v_snd_947_);
lean_del_object(v___x_945_);
goto v___jp_939_;
}
}
}
else
{
lean_dec(v_charInst_x3f_942_);
goto v___jp_939_;
}
v___jp_939_:
{
lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_940_ = lean_box(0);
v___x_941_ = lean_apply_2(v_toPure_937_, lean_box(0), v___x_940_);
return v___x_941_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg(lean_object* v_inst_955_, lean_object* v_inst_956_){
_start:
{
lean_object* v_toApplicative_957_; lean_object* v_toBind_958_; lean_object* v_getRing_959_; lean_object* v_toPure_960_; lean_object* v___f_961_; lean_object* v___x_962_; 
v_toApplicative_957_ = lean_ctor_get(v_inst_955_, 0);
lean_inc_ref(v_toApplicative_957_);
v_toBind_958_ = lean_ctor_get(v_inst_955_, 1);
lean_inc(v_toBind_958_);
lean_dec_ref(v_inst_955_);
v_getRing_959_ = lean_ctor_get(v_inst_956_, 0);
lean_inc(v_getRing_959_);
lean_dec_ref(v_inst_956_);
v_toPure_960_ = lean_ctor_get(v_toApplicative_957_, 1);
lean_inc(v_toPure_960_);
lean_dec_ref(v_toApplicative_957_);
v___f_961_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_961_, 0, v_toPure_960_);
v___x_962_ = lean_apply_4(v_toBind_958_, lean_box(0), lean_box(0), v_getRing_959_, v___f_961_);
return v___x_962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f(lean_object* v_m_963_, lean_object* v_inst_964_, lean_object* v_inst_965_){
_start:
{
lean_object* v___x_966_; 
v___x_966_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroChar_x3f___redArg(v_inst_964_, v_inst_965_);
return v___x_966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f___redArg___lam__0(lean_object* v_toPure_967_, lean_object* v_____do__lift_968_){
_start:
{
lean_object* v_charInst_x3f_972_; 
v_charInst_x3f_972_ = lean_ctor_get(v_____do__lift_968_, 5);
lean_inc(v_charInst_x3f_972_);
lean_dec_ref(v_____do__lift_968_);
if (lean_obj_tag(v_charInst_x3f_972_) == 1)
{
lean_object* v_val_973_; lean_object* v_snd_974_; lean_object* v___x_975_; uint8_t v___x_976_; 
v_val_973_ = lean_ctor_get(v_charInst_x3f_972_, 0);
v_snd_974_ = lean_ctor_get(v_val_973_, 1);
v___x_975_ = lean_unsigned_to_nat(0u);
v___x_976_ = lean_nat_dec_eq(v_snd_974_, v___x_975_);
if (v___x_976_ == 0)
{
lean_object* v___x_977_; 
v___x_977_ = lean_apply_2(v_toPure_967_, lean_box(0), v_charInst_x3f_972_);
return v___x_977_;
}
else
{
lean_dec_ref(v_charInst_x3f_972_);
goto v___jp_969_;
}
}
else
{
lean_dec(v_charInst_x3f_972_);
goto v___jp_969_;
}
v___jp_969_:
{
lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_970_ = lean_box(0);
v___x_971_ = lean_apply_2(v_toPure_967_, lean_box(0), v___x_970_);
return v___x_971_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f___redArg(lean_object* v_inst_978_, lean_object* v_inst_979_){
_start:
{
lean_object* v_toApplicative_980_; lean_object* v_toBind_981_; lean_object* v_getRing_982_; lean_object* v_toPure_983_; lean_object* v___f_984_; lean_object* v___x_985_; 
v_toApplicative_980_ = lean_ctor_get(v_inst_978_, 0);
lean_inc_ref(v_toApplicative_980_);
v_toBind_981_ = lean_ctor_get(v_inst_978_, 1);
lean_inc(v_toBind_981_);
lean_dec_ref(v_inst_978_);
v_getRing_982_ = lean_ctor_get(v_inst_979_, 0);
lean_inc(v_getRing_982_);
lean_dec_ref(v_inst_979_);
v_toPure_983_ = lean_ctor_get(v_toApplicative_980_, 1);
lean_inc(v_toPure_983_);
lean_dec_ref(v_toApplicative_980_);
v___f_984_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f___redArg___lam__0), 2, 1);
lean_closure_set(v___f_984_, 0, v_toPure_983_);
v___x_985_ = lean_apply_4(v_toBind_981_, lean_box(0), lean_box(0), v_getRing_982_, v___f_984_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f(lean_object* v_m_986_, lean_object* v_inst_987_, lean_object* v_inst_988_){
_start:
{
lean_object* v___x_989_; 
v___x_989_ = l_Lean_Meta_Grind_Arith_CommRing_nonzeroCharInst_x3f___redArg(v_inst_987_, v_inst_988_);
return v___x_989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisorsInst_x3f(lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_){
_start:
{
lean_object* v___x_1002_; 
v___x_1002_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_, v_a_995_, v_a_996_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
if (lean_obj_tag(v___x_1002_) == 0)
{
lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1011_; 
v_a_1003_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_1005_ = v___x_1002_;
v_isShared_1006_ = v_isSharedCheck_1011_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v___x_1002_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1011_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v_noZeroDivInst_x3f_1007_; lean_object* v___x_1009_; 
v_noZeroDivInst_x3f_1007_ = lean_ctor_get(v_a_1003_, 5);
lean_inc(v_noZeroDivInst_x3f_1007_);
lean_dec(v_a_1003_);
if (v_isShared_1006_ == 0)
{
lean_ctor_set(v___x_1005_, 0, v_noZeroDivInst_x3f_1007_);
v___x_1009_ = v___x_1005_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v_noZeroDivInst_x3f_1007_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
}
else
{
lean_object* v_a_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1019_; 
v_a_1012_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_1014_ = v___x_1002_;
v_isShared_1015_ = v_isSharedCheck_1019_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_a_1012_);
lean_dec(v___x_1002_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1019_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v___x_1017_; 
if (v_isShared_1015_ == 0)
{
v___x_1017_ = v___x_1014_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v_a_1012_);
v___x_1017_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
return v___x_1017_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisorsInst_x3f___boxed(lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_){
_start:
{
lean_object* v_res_1032_; 
v_res_1032_ = l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisorsInst_x3f(v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_);
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
lean_dec_ref(v_a_1020_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisors(lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_){
_start:
{
lean_object* v___x_1045_; 
v___x_1045_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_);
if (lean_obj_tag(v___x_1045_) == 0)
{
lean_object* v_a_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1061_; 
v_a_1046_ = lean_ctor_get(v___x_1045_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v___x_1045_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1048_ = v___x_1045_;
v_isShared_1049_ = v_isSharedCheck_1061_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_a_1046_);
lean_dec(v___x_1045_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1061_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v_noZeroDivInst_x3f_1050_; 
v_noZeroDivInst_x3f_1050_ = lean_ctor_get(v_a_1046_, 5);
lean_inc(v_noZeroDivInst_x3f_1050_);
lean_dec(v_a_1046_);
if (lean_obj_tag(v_noZeroDivInst_x3f_1050_) == 0)
{
uint8_t v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1054_; 
v___x_1051_ = 0;
v___x_1052_ = lean_box(v___x_1051_);
if (v_isShared_1049_ == 0)
{
lean_ctor_set(v___x_1048_, 0, v___x_1052_);
v___x_1054_ = v___x_1048_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v___x_1052_);
v___x_1054_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
return v___x_1054_;
}
}
else
{
uint8_t v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1059_; 
lean_dec_ref(v_noZeroDivInst_x3f_1050_);
v___x_1056_ = 1;
v___x_1057_ = lean_box(v___x_1056_);
if (v_isShared_1049_ == 0)
{
lean_ctor_set(v___x_1048_, 0, v___x_1057_);
v___x_1059_ = v___x_1048_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v___x_1057_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
}
}
else
{
lean_object* v_a_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1069_; 
v_a_1062_ = lean_ctor_get(v___x_1045_, 0);
v_isSharedCheck_1069_ = !lean_is_exclusive(v___x_1045_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1064_ = v___x_1045_;
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_a_1062_);
lean_dec(v___x_1045_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1067_; 
if (v_isShared_1065_ == 0)
{
v___x_1067_ = v___x_1064_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v_a_1062_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisors___boxed(lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_){
_start:
{
lean_object* v_res_1082_; 
v_res_1082_ = l_Lean_Meta_Grind_Arith_CommRing_noZeroDivisors(v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_);
lean_dec(v_a_1080_);
lean_dec_ref(v_a_1079_);
lean_dec(v_a_1078_);
lean_dec_ref(v_a_1077_);
lean_dec(v_a_1076_);
lean_dec_ref(v_a_1075_);
lean_dec(v_a_1074_);
lean_dec_ref(v_a_1073_);
lean_dec(v_a_1072_);
lean_dec(v_a_1071_);
lean_dec_ref(v_a_1070_);
return v_res_1082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_hasChar(lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_){
_start:
{
lean_object* v___x_1095_; 
v___x_1095_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_);
if (lean_obj_tag(v___x_1095_) == 0)
{
lean_object* v_a_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1112_; 
v_a_1096_ = lean_ctor_get(v___x_1095_, 0);
v_isSharedCheck_1112_ = !lean_is_exclusive(v___x_1095_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1098_ = v___x_1095_;
v_isShared_1099_ = v_isSharedCheck_1112_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_a_1096_);
lean_dec(v___x_1095_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1112_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v_toRing_1100_; lean_object* v_charInst_x3f_1101_; 
v_toRing_1100_ = lean_ctor_get(v_a_1096_, 0);
lean_inc_ref(v_toRing_1100_);
lean_dec(v_a_1096_);
v_charInst_x3f_1101_ = lean_ctor_get(v_toRing_1100_, 5);
lean_inc(v_charInst_x3f_1101_);
lean_dec_ref(v_toRing_1100_);
if (lean_obj_tag(v_charInst_x3f_1101_) == 0)
{
uint8_t v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1105_; 
v___x_1102_ = 0;
v___x_1103_ = lean_box(v___x_1102_);
if (v_isShared_1099_ == 0)
{
lean_ctor_set(v___x_1098_, 0, v___x_1103_);
v___x_1105_ = v___x_1098_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v___x_1103_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
else
{
uint8_t v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1110_; 
lean_dec_ref(v_charInst_x3f_1101_);
v___x_1107_ = 1;
v___x_1108_ = lean_box(v___x_1107_);
if (v_isShared_1099_ == 0)
{
lean_ctor_set(v___x_1098_, 0, v___x_1108_);
v___x_1110_ = v___x_1098_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v___x_1108_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
return v___x_1110_;
}
}
}
}
else
{
lean_object* v_a_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1120_; 
v_a_1113_ = lean_ctor_get(v___x_1095_, 0);
v_isSharedCheck_1120_ = !lean_is_exclusive(v___x_1095_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1115_ = v___x_1095_;
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_a_1113_);
lean_dec(v___x_1095_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1118_; 
if (v_isShared_1116_ == 0)
{
v___x_1118_ = v___x_1115_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v_a_1113_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_hasChar___boxed(lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = l_Lean_Meta_Grind_Arith_CommRing_hasChar(v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_);
lean_dec(v_a_1131_);
lean_dec_ref(v_a_1130_);
lean_dec(v_a_1129_);
lean_dec_ref(v_a_1128_);
lean_dec(v_a_1127_);
lean_dec_ref(v_a_1126_);
lean_dec(v_a_1125_);
lean_dec_ref(v_a_1124_);
lean_dec(v_a_1123_);
lean_dec(v_a_1122_);
lean_dec_ref(v_a_1121_);
return v_res_1133_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__1(void){
_start:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1135_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__0));
v___x_1136_ = l_Lean_stringToMessageData(v___x_1135_);
return v___x_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCharInst(lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_){
_start:
{
lean_object* v___x_1149_; 
v___x_1149_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_);
if (lean_obj_tag(v___x_1149_) == 0)
{
lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1162_; 
v_a_1150_ = lean_ctor_get(v___x_1149_, 0);
v_isSharedCheck_1162_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1162_ == 0)
{
v___x_1152_ = v___x_1149_;
v_isShared_1153_ = v_isSharedCheck_1162_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1149_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1162_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v_toRing_1154_; lean_object* v_charInst_x3f_1155_; 
v_toRing_1154_ = lean_ctor_get(v_a_1150_, 0);
lean_inc_ref(v_toRing_1154_);
lean_dec(v_a_1150_);
v_charInst_x3f_1155_ = lean_ctor_get(v_toRing_1154_, 5);
lean_inc(v_charInst_x3f_1155_);
lean_dec_ref(v_toRing_1154_);
if (lean_obj_tag(v_charInst_x3f_1155_) == 1)
{
lean_object* v_val_1156_; lean_object* v___x_1158_; 
v_val_1156_ = lean_ctor_get(v_charInst_x3f_1155_, 0);
lean_inc(v_val_1156_);
lean_dec_ref(v_charInst_x3f_1155_);
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 0, v_val_1156_);
v___x_1158_ = v___x_1152_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_val_1156_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
else
{
lean_object* v___x_1160_; lean_object* v___x_1161_; 
lean_dec(v_charInst_x3f_1155_);
lean_del_object(v___x_1152_);
v___x_1160_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_getCharInst___closed__1);
v___x_1161_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing_spec__0___redArg(v___x_1160_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_);
return v___x_1161_;
}
}
}
else
{
lean_object* v_a_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1170_; 
v_a_1163_ = lean_ctor_get(v___x_1149_, 0);
v_isSharedCheck_1170_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1165_ = v___x_1149_;
v_isShared_1166_ = v_isSharedCheck_1170_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_a_1163_);
lean_dec(v___x_1149_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1170_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v___x_1168_; 
if (v_isShared_1166_ == 0)
{
v___x_1168_ = v___x_1165_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v_a_1163_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
return v___x_1168_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getCharInst___boxed(lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_){
_start:
{
lean_object* v_res_1183_; 
v_res_1183_ = l_Lean_Meta_Grind_Arith_CommRing_getCharInst(v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_);
lean_dec(v_a_1181_);
lean_dec_ref(v_a_1180_);
lean_dec(v_a_1179_);
lean_dec_ref(v_a_1178_);
lean_dec(v_a_1177_);
lean_dec_ref(v_a_1176_);
lean_dec(v_a_1175_);
lean_dec_ref(v_a_1174_);
lean_dec(v_a_1173_);
lean_dec(v_a_1172_);
lean_dec_ref(v_a_1171_);
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isField(lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_){
_start:
{
lean_object* v___x_1196_; 
v___x_1196_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_);
if (lean_obj_tag(v___x_1196_) == 0)
{
lean_object* v_a_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1212_; 
v_a_1197_ = lean_ctor_get(v___x_1196_, 0);
v_isSharedCheck_1212_ = !lean_is_exclusive(v___x_1196_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1199_ = v___x_1196_;
v_isShared_1200_ = v_isSharedCheck_1212_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_a_1197_);
lean_dec(v___x_1196_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1212_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v_fieldInst_x3f_1201_; 
v_fieldInst_x3f_1201_ = lean_ctor_get(v_a_1197_, 6);
lean_inc(v_fieldInst_x3f_1201_);
lean_dec(v_a_1197_);
if (lean_obj_tag(v_fieldInst_x3f_1201_) == 0)
{
uint8_t v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1205_; 
v___x_1202_ = 0;
v___x_1203_ = lean_box(v___x_1202_);
if (v_isShared_1200_ == 0)
{
lean_ctor_set(v___x_1199_, 0, v___x_1203_);
v___x_1205_ = v___x_1199_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v___x_1203_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
else
{
uint8_t v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1210_; 
lean_dec_ref(v_fieldInst_x3f_1201_);
v___x_1207_ = 1;
v___x_1208_ = lean_box(v___x_1207_);
if (v_isShared_1200_ == 0)
{
lean_ctor_set(v___x_1199_, 0, v___x_1208_);
v___x_1210_ = v___x_1199_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v___x_1208_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
return v___x_1210_;
}
}
}
}
else
{
lean_object* v_a_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1220_; 
v_a_1213_ = lean_ctor_get(v___x_1196_, 0);
v_isSharedCheck_1220_ = !lean_is_exclusive(v___x_1196_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1215_ = v___x_1196_;
v_isShared_1216_ = v_isSharedCheck_1220_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_a_1213_);
lean_dec(v___x_1196_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1220_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v___x_1218_; 
if (v_isShared_1216_ == 0)
{
v___x_1218_ = v___x_1215_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v_a_1213_);
v___x_1218_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
return v___x_1218_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isField___boxed(lean_object* v_a_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_){
_start:
{
lean_object* v_res_1233_; 
v_res_1233_ = l_Lean_Meta_Grind_Arith_CommRing_isField(v_a_1221_, v_a_1222_, v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_);
lean_dec(v_a_1231_);
lean_dec_ref(v_a_1230_);
lean_dec(v_a_1229_);
lean_dec_ref(v_a_1228_);
lean_dec(v_a_1227_);
lean_dec_ref(v_a_1226_);
lean_dec(v_a_1225_);
lean_dec_ref(v_a_1224_);
lean_dec(v_a_1223_);
lean_dec(v_a_1222_);
lean_dec_ref(v_a_1221_);
return v_res_1233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty(lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_){
_start:
{
lean_object* v___x_1246_; 
v___x_1246_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1234_, v_a_1235_, v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_, v_a_1244_);
if (lean_obj_tag(v___x_1246_) == 0)
{
lean_object* v_a_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1262_; 
v_a_1247_ = lean_ctor_get(v___x_1246_, 0);
v_isSharedCheck_1262_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1262_ == 0)
{
v___x_1249_ = v___x_1246_;
v_isShared_1250_ = v_isSharedCheck_1262_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_a_1247_);
lean_dec(v___x_1246_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1262_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v_queue_1251_; 
v_queue_1251_ = lean_ctor_get(v_a_1247_, 11);
lean_inc(v_queue_1251_);
lean_dec(v_a_1247_);
if (lean_obj_tag(v_queue_1251_) == 0)
{
uint8_t v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1255_; 
lean_dec_ref(v_queue_1251_);
v___x_1252_ = 0;
v___x_1253_ = lean_box(v___x_1252_);
if (v_isShared_1250_ == 0)
{
lean_ctor_set(v___x_1249_, 0, v___x_1253_);
v___x_1255_ = v___x_1249_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v___x_1253_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
else
{
uint8_t v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1260_; 
v___x_1257_ = 1;
v___x_1258_ = lean_box(v___x_1257_);
if (v_isShared_1250_ == 0)
{
lean_ctor_set(v___x_1249_, 0, v___x_1258_);
v___x_1260_ = v___x_1249_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v___x_1258_);
v___x_1260_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
return v___x_1260_;
}
}
}
}
else
{
lean_object* v_a_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1270_; 
v_a_1263_ = lean_ctor_get(v___x_1246_, 0);
v_isSharedCheck_1270_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1265_ = v___x_1246_;
v_isShared_1266_ = v_isSharedCheck_1270_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_a_1263_);
lean_dec(v___x_1246_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1270_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v___x_1268_; 
if (v_isShared_1266_ == 0)
{
v___x_1268_ = v___x_1265_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v_a_1263_);
v___x_1268_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
return v___x_1268_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty___boxed(lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_){
_start:
{
lean_object* v_res_1283_; 
v_res_1283_ = l_Lean_Meta_Grind_Arith_CommRing_isQueueEmpty(v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_);
lean_dec(v_a_1281_);
lean_dec_ref(v_a_1280_);
lean_dec(v_a_1279_);
lean_dec_ref(v_a_1278_);
lean_dec(v_a_1277_);
lean_dec_ref(v_a_1276_);
lean_dec(v_a_1275_);
lean_dec_ref(v_a_1274_);
lean_dec(v_a_1273_);
lean_dec(v_a_1272_);
lean_dec_ref(v_a_1271_);
return v_res_1283_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(lean_object* v_k_1284_, lean_object* v_t_1285_){
_start:
{
if (lean_obj_tag(v_t_1285_) == 0)
{
lean_object* v_k_1286_; lean_object* v_v_1287_; lean_object* v_l_1288_; lean_object* v_r_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1943_; 
v_k_1286_ = lean_ctor_get(v_t_1285_, 1);
v_v_1287_ = lean_ctor_get(v_t_1285_, 2);
v_l_1288_ = lean_ctor_get(v_t_1285_, 3);
v_r_1289_ = lean_ctor_get(v_t_1285_, 4);
v_isSharedCheck_1943_ = !lean_is_exclusive(v_t_1285_);
if (v_isSharedCheck_1943_ == 0)
{
lean_object* v_unused_1944_; 
v_unused_1944_ = lean_ctor_get(v_t_1285_, 0);
lean_dec(v_unused_1944_);
v___x_1291_ = v_t_1285_;
v_isShared_1292_ = v_isSharedCheck_1943_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_r_1289_);
lean_inc(v_l_1288_);
lean_inc(v_v_1287_);
lean_inc(v_k_1286_);
lean_dec(v_t_1285_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1943_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
uint8_t v___x_1293_; 
v___x_1293_ = l_Lean_Meta_Grind_Arith_CommRing_EqCnstr_compare(v_k_1284_, v_k_1286_);
switch(v___x_1293_)
{
case 0:
{
lean_object* v_impl_1294_; lean_object* v___x_1295_; 
v_impl_1294_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_k_1284_, v_l_1288_);
v___x_1295_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1294_) == 0)
{
if (lean_obj_tag(v_r_1289_) == 0)
{
lean_object* v_size_1296_; lean_object* v_size_1297_; lean_object* v_k_1298_; lean_object* v_v_1299_; lean_object* v_l_1300_; lean_object* v_r_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; uint8_t v___x_1304_; 
v_size_1296_ = lean_ctor_get(v_impl_1294_, 0);
lean_inc(v_size_1296_);
v_size_1297_ = lean_ctor_get(v_r_1289_, 0);
v_k_1298_ = lean_ctor_get(v_r_1289_, 1);
v_v_1299_ = lean_ctor_get(v_r_1289_, 2);
v_l_1300_ = lean_ctor_get(v_r_1289_, 3);
lean_inc(v_l_1300_);
v_r_1301_ = lean_ctor_get(v_r_1289_, 4);
v___x_1302_ = lean_unsigned_to_nat(3u);
v___x_1303_ = lean_nat_mul(v___x_1302_, v_size_1296_);
v___x_1304_ = lean_nat_dec_lt(v___x_1303_, v_size_1297_);
lean_dec(v___x_1303_);
if (v___x_1304_ == 0)
{
lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1308_; 
lean_dec(v_l_1300_);
v___x_1305_ = lean_nat_add(v___x_1295_, v_size_1296_);
lean_dec(v_size_1296_);
v___x_1306_ = lean_nat_add(v___x_1305_, v_size_1297_);
lean_dec(v___x_1305_);
if (v_isShared_1292_ == 0)
{
lean_ctor_set(v___x_1291_, 3, v_impl_1294_);
lean_ctor_set(v___x_1291_, 0, v___x_1306_);
v___x_1308_ = v___x_1291_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v___x_1306_);
lean_ctor_set(v_reuseFailAlloc_1309_, 1, v_k_1286_);
lean_ctor_set(v_reuseFailAlloc_1309_, 2, v_v_1287_);
lean_ctor_set(v_reuseFailAlloc_1309_, 3, v_impl_1294_);
lean_ctor_set(v_reuseFailAlloc_1309_, 4, v_r_1289_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
return v___x_1308_;
}
}
else
{
lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1373_; 
lean_inc(v_r_1301_);
lean_inc(v_v_1299_);
lean_inc(v_k_1298_);
lean_inc(v_size_1297_);
v_isSharedCheck_1373_ = !lean_is_exclusive(v_r_1289_);
if (v_isSharedCheck_1373_ == 0)
{
lean_object* v_unused_1374_; lean_object* v_unused_1375_; lean_object* v_unused_1376_; lean_object* v_unused_1377_; lean_object* v_unused_1378_; 
v_unused_1374_ = lean_ctor_get(v_r_1289_, 4);
lean_dec(v_unused_1374_);
v_unused_1375_ = lean_ctor_get(v_r_1289_, 3);
lean_dec(v_unused_1375_);
v_unused_1376_ = lean_ctor_get(v_r_1289_, 2);
lean_dec(v_unused_1376_);
v_unused_1377_ = lean_ctor_get(v_r_1289_, 1);
lean_dec(v_unused_1377_);
v_unused_1378_ = lean_ctor_get(v_r_1289_, 0);
lean_dec(v_unused_1378_);
v___x_1311_ = v_r_1289_;
v_isShared_1312_ = v_isSharedCheck_1373_;
goto v_resetjp_1310_;
}
else
{
lean_dec(v_r_1289_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1373_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v_size_1313_; lean_object* v_k_1314_; lean_object* v_v_1315_; lean_object* v_l_1316_; lean_object* v_r_1317_; lean_object* v_size_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; uint8_t v___x_1321_; 
v_size_1313_ = lean_ctor_get(v_l_1300_, 0);
v_k_1314_ = lean_ctor_get(v_l_1300_, 1);
v_v_1315_ = lean_ctor_get(v_l_1300_, 2);
v_l_1316_ = lean_ctor_get(v_l_1300_, 3);
v_r_1317_ = lean_ctor_get(v_l_1300_, 4);
v_size_1318_ = lean_ctor_get(v_r_1301_, 0);
v___x_1319_ = lean_unsigned_to_nat(2u);
v___x_1320_ = lean_nat_mul(v___x_1319_, v_size_1318_);
v___x_1321_ = lean_nat_dec_lt(v_size_1313_, v___x_1320_);
lean_dec(v___x_1320_);
if (v___x_1321_ == 0)
{
lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1349_; 
lean_inc(v_r_1317_);
lean_inc(v_l_1316_);
lean_inc(v_v_1315_);
lean_inc(v_k_1314_);
v_isSharedCheck_1349_ = !lean_is_exclusive(v_l_1300_);
if (v_isSharedCheck_1349_ == 0)
{
lean_object* v_unused_1350_; lean_object* v_unused_1351_; lean_object* v_unused_1352_; lean_object* v_unused_1353_; lean_object* v_unused_1354_; 
v_unused_1350_ = lean_ctor_get(v_l_1300_, 4);
lean_dec(v_unused_1350_);
v_unused_1351_ = lean_ctor_get(v_l_1300_, 3);
lean_dec(v_unused_1351_);
v_unused_1352_ = lean_ctor_get(v_l_1300_, 2);
lean_dec(v_unused_1352_);
v_unused_1353_ = lean_ctor_get(v_l_1300_, 1);
lean_dec(v_unused_1353_);
v_unused_1354_ = lean_ctor_get(v_l_1300_, 0);
lean_dec(v_unused_1354_);
v___x_1323_ = v_l_1300_;
v_isShared_1324_ = v_isSharedCheck_1349_;
goto v_resetjp_1322_;
}
else
{
lean_dec(v_l_1300_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1349_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___y_1328_; lean_object* v___y_1329_; lean_object* v___y_1330_; lean_object* v___y_1339_; 
v___x_1325_ = lean_nat_add(v___x_1295_, v_size_1296_);
lean_dec(v_size_1296_);
v___x_1326_ = lean_nat_add(v___x_1325_, v_size_1297_);
lean_dec(v_size_1297_);
if (lean_obj_tag(v_l_1316_) == 0)
{
lean_object* v_size_1347_; 
v_size_1347_ = lean_ctor_get(v_l_1316_, 0);
lean_inc(v_size_1347_);
v___y_1339_ = v_size_1347_;
goto v___jp_1338_;
}
else
{
lean_object* v___x_1348_; 
v___x_1348_ = lean_unsigned_to_nat(0u);
v___y_1339_ = v___x_1348_;
goto v___jp_1338_;
}
v___jp_1327_:
{
lean_object* v___x_1331_; lean_object* v___x_1333_; 
v___x_1331_ = lean_nat_add(v___y_1328_, v___y_1330_);
lean_dec(v___y_1330_);
lean_dec(v___y_1328_);
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 4, v_r_1301_);
lean_ctor_set(v___x_1323_, 3, v_r_1317_);
lean_ctor_set(v___x_1323_, 2, v_v_1299_);
lean_ctor_set(v___x_1323_, 1, v_k_1298_);
lean_ctor_set(v___x_1323_, 0, v___x_1331_);
v___x_1333_ = v___x_1323_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v___x_1331_);
lean_ctor_set(v_reuseFailAlloc_1337_, 1, v_k_1298_);
lean_ctor_set(v_reuseFailAlloc_1337_, 2, v_v_1299_);
lean_ctor_set(v_reuseFailAlloc_1337_, 3, v_r_1317_);
lean_ctor_set(v_reuseFailAlloc_1337_, 4, v_r_1301_);
v___x_1333_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
lean_object* v___x_1335_; 
if (v_isShared_1312_ == 0)
{
lean_ctor_set(v___x_1311_, 4, v___x_1333_);
lean_ctor_set(v___x_1311_, 3, v___y_1329_);
lean_ctor_set(v___x_1311_, 2, v_v_1315_);
lean_ctor_set(v___x_1311_, 1, v_k_1314_);
lean_ctor_set(v___x_1311_, 0, v___x_1326_);
v___x_1335_ = v___x_1311_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v___x_1326_);
lean_ctor_set(v_reuseFailAlloc_1336_, 1, v_k_1314_);
lean_ctor_set(v_reuseFailAlloc_1336_, 2, v_v_1315_);
lean_ctor_set(v_reuseFailAlloc_1336_, 3, v___y_1329_);
lean_ctor_set(v_reuseFailAlloc_1336_, 4, v___x_1333_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
return v___x_1335_;
}
}
}
v___jp_1338_:
{
lean_object* v___x_1340_; lean_object* v___x_1342_; 
v___x_1340_ = lean_nat_add(v___x_1325_, v___y_1339_);
lean_dec(v___y_1339_);
lean_dec(v___x_1325_);
if (v_isShared_1292_ == 0)
{
lean_ctor_set(v___x_1291_, 4, v_l_1316_);
lean_ctor_set(v___x_1291_, 3, v_impl_1294_);
lean_ctor_set(v___x_1291_, 0, v___x_1340_);
v___x_1342_ = v___x_1291_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v___x_1340_);
lean_ctor_set(v_reuseFailAlloc_1346_, 1, v_k_1286_);
lean_ctor_set(v_reuseFailAlloc_1346_, 2, v_v_1287_);
lean_ctor_set(v_reuseFailAlloc_1346_, 3, v_impl_1294_);
lean_ctor_set(v_reuseFailAlloc_1346_, 4, v_l_1316_);
v___x_1342_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
lean_object* v___x_1343_; 
v___x_1343_ = lean_nat_add(v___x_1295_, v_size_1318_);
if (lean_obj_tag(v_r_1317_) == 0)
{
lean_object* v_size_1344_; 
v_size_1344_ = lean_ctor_get(v_r_1317_, 0);
lean_inc(v_size_1344_);
v___y_1328_ = v___x_1343_;
v___y_1329_ = v___x_1342_;
v___y_1330_ = v_size_1344_;
goto v___jp_1327_;
}
else
{
lean_object* v___x_1345_; 
v___x_1345_ = lean_unsigned_to_nat(0u);
v___y_1328_ = v___x_1343_;
v___y_1329_ = v___x_1342_;
v___y_1330_ = v___x_1345_;
goto v___jp_1327_;
}
}
}
}
}
else
{
lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1359_; 
lean_del_object(v___x_1291_);
v___x_1355_ = lean_nat_add(v___x_1295_, v_size_1296_);
lean_dec(v_size_1296_);
v___x_1356_ = lean_nat_add(v___x_1355_, v_size_1297_);
lean_dec(v_size_1297_);
v___x_1357_ = lean_nat_add(v___x_1355_, v_size_1313_);
lean_dec(v___x_1355_);
lean_inc_ref(v_impl_1294_);
if (v_isShared_1312_ == 0)
{
lean_ctor_set(v___x_1311_, 4, v_l_1300_);
lean_ctor_set(v___x_1311_, 3, v_impl_1294_);
lean_ctor_set(v___x_1311_, 2, v_v_1287_);
lean_ctor_set(v___x_1311_, 1, v_k_1286_);
lean_ctor_set(v___x_1311_, 0, v___x_1357_);
v___x_1359_ = v___x_1311_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v___x_1357_);
lean_ctor_set(v_reuseFailAlloc_1372_, 1, v_k_1286_);
lean_ctor_set(v_reuseFailAlloc_1372_, 2, v_v_1287_);
lean_ctor_set(v_reuseFailAlloc_1372_, 3, v_impl_1294_);
lean_ctor_set(v_reuseFailAlloc_1372_, 4, v_l_1300_);
v___x_1359_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1366_; 
v_isSharedCheck_1366_ = !lean_is_exclusive(v_impl_1294_);
if (v_isSharedCheck_1366_ == 0)
{
lean_object* v_unused_1367_; lean_object* v_unused_1368_; lean_object* v_unused_1369_; lean_object* v_unused_1370_; lean_object* v_unused_1371_; 
v_unused_1367_ = lean_ctor_get(v_impl_1294_, 4);
lean_dec(v_unused_1367_);
v_unused_1368_ = lean_ctor_get(v_impl_1294_, 3);
lean_dec(v_unused_1368_);
v_unused_1369_ = lean_ctor_get(v_impl_1294_, 2);
lean_dec(v_unused_1369_);
v_unused_1370_ = lean_ctor_get(v_impl_1294_, 1);
lean_dec(v_unused_1370_);
v_unused_1371_ = lean_ctor_get(v_impl_1294_, 0);
lean_dec(v_unused_1371_);
v___x_1361_ = v_impl_1294_;
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
else
{
lean_dec(v_impl_1294_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v___x_1364_; 
if (v_isShared_1362_ == 0)
{
lean_ctor_set(v___x_1361_, 4, v_r_1301_);
lean_ctor_set(v___x_1361_, 3, v___x_1359_);
lean_ctor_set(v___x_1361_, 2, v_v_1299_);
lean_ctor_set(v___x_1361_, 1, v_k_1298_);
lean_ctor_set(v___x_1361_, 0, v___x_1356_);
v___x_1364_ = v___x_1361_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v___x_1356_);
lean_ctor_set(v_reuseFailAlloc_1365_, 1, v_k_1298_);
lean_ctor_set(v_reuseFailAlloc_1365_, 2, v_v_1299_);
lean_ctor_set(v_reuseFailAlloc_1365_, 3, v___x_1359_);
lean_ctor_set(v_reuseFailAlloc_1365_, 4, v_r_1301_);
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
}
else
{
lean_object* v_size_1379_; lean_object* v___x_1380_; lean_object* v___x_1382_; 
v_size_1379_ = lean_ctor_get(v_impl_1294_, 0);
lean_inc(v_size_1379_);
v___x_1380_ = lean_nat_add(v___x_1295_, v_size_1379_);
lean_dec(v_size_1379_);
if (v_isShared_1292_ == 0)
{
lean_ctor_set(v___x_1291_, 3, v_impl_1294_);
lean_ctor_set(v___x_1291_, 0, v___x_1380_);
v___x_1382_ = v___x_1291_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v___x_1380_);
lean_ctor_set(v_reuseFailAlloc_1383_, 1, v_k_1286_);
lean_ctor_set(v_reuseFailAlloc_1383_, 2, v_v_1287_);
lean_ctor_set(v_reuseFailAlloc_1383_, 3, v_impl_1294_);
lean_ctor_set(v_reuseFailAlloc_1383_, 4, v_r_1289_);
v___x_1382_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
return v___x_1382_;
}
}
}
else
{
if (lean_obj_tag(v_r_1289_) == 0)
{
lean_object* v_l_1384_; 
v_l_1384_ = lean_ctor_get(v_r_1289_, 3);
lean_inc(v_l_1384_);
if (lean_obj_tag(v_l_1384_) == 0)
{
lean_object* v_r_1385_; 
v_r_1385_ = lean_ctor_get(v_r_1289_, 4);
lean_inc(v_r_1385_);
if (lean_obj_tag(v_r_1385_) == 0)
{
lean_object* v_size_1386_; lean_object* v_k_1387_; lean_object* v_v_1388_; lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1401_; 
v_size_1386_ = lean_ctor_get(v_r_1289_, 0);
v_k_1387_ = lean_ctor_get(v_r_1289_, 1);
v_v_1388_ = lean_ctor_get(v_r_1289_, 2);
v_isSharedCheck_1401_ = !lean_is_exclusive(v_r_1289_);
if (v_isSharedCheck_1401_ == 0)
{
lean_object* v_unused_1402_; lean_object* v_unused_1403_; 
v_unused_1402_ = lean_ctor_get(v_r_1289_, 4);
lean_dec(v_unused_1402_);
v_unused_1403_ = lean_ctor_get(v_r_1289_, 3);
lean_dec(v_unused_1403_);
v___x_1390_ = v_r_1289_;
v_isShared_1391_ = v_isSharedCheck_1401_;
goto v_resetjp_1389_;
}
else
{
lean_inc(v_v_1388_);
lean_inc(v_k_1387_);
lean_inc(v_size_1386_);
lean_dec(v_r_1289_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1401_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
lean_object* v_size_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1396_; 
v_size_1392_ = lean_ctor_get(v_l_1384_, 0);
v___x_1393_ = lean_nat_add(v___x_1295_, v_size_1386_);
lean_dec(v_size_1386_);
v___x_1394_ = lean_nat_add(v___x_1295_, v_size_1392_);
if (v_isShared_1391_ == 0)
{
lean_ctor_set(v___x_1390_, 4, v_l_1384_);
lean_ctor_set(v___x_1390_, 3, v_impl_1294_);
lean_ctor_set(v___x_1390_, 2, v_v_1287_);
lean_ctor_set(v___x_1390_, 1, v_k_1286_);
lean_ctor_set(v___x_1390_, 0, v___x_1394_);
v___x_1396_ = v___x_1390_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v___x_1394_);
lean_ctor_set(v_reuseFailAlloc_1400_, 1, v_k_1286_);
lean_ctor_set(v_reuseFailAlloc_1400_, 2, v_v_1287_);
lean_ctor_set(v_reuseFailAlloc_1400_, 3, v_impl_1294_);
lean_ctor_set(v_reuseFailAlloc_1400_, 4, v_l_1384_);
v___x_1396_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
lean_object* v___x_1398_; 
if (v_isShared_1292_ == 0)
{
lean_ctor_set(v___x_1291_, 4, v_r_1385_);
lean_ctor_set(v___x_1291_, 3, v___x_1396_);
lean_ctor_set(v___x_1291_, 2, v_v_1388_);
lean_ctor_set(v___x_1291_, 1, v_k_1387_);
lean_ctor_set(v___x_1291_, 0, v___x_1393_);
v___x_1398_ = v___x_1291_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v___x_1393_);
lean_ctor_set(v_reuseFailAlloc_1399_, 1, v_k_1387_);
lean_ctor_set(v_reuseFailAlloc_1399_, 2, v_v_1388_);
lean_ctor_set(v_reuseFailAlloc_1399_, 3, v___x_1396_);
lean_ctor_set(v_reuseFailAlloc_1399_, 4, v_r_1385_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
}
}
else
{
lean_object* v_k_1404_; lean_object* v_v_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1428_; 
v_k_1404_ = lean_ctor_get(v_r_1289_, 1);
v_v_1405_ = lean_ctor_get(v_r_1289_, 2);
v_isSharedCheck_1428_ = !lean_is_exclusive(v_r_1289_);
if (v_isSharedCheck_1428_ == 0)
{
lean_object* v_unused_1429_; lean_object* v_unused_1430_; lean_object* v_unused_1431_; 
v_unused_1429_ = lean_ctor_get(v_r_1289_, 4);
lean_dec(v_unused_1429_);
v_unused_1430_ = lean_ctor_get(v_r_1289_, 3);
lean_dec(v_unused_1430_);
v_unused_1431_ = lean_ctor_get(v_r_1289_, 0);
lean_dec(v_unused_1431_);
v___x_1407_ = v_r_1289_;
v_isShared_1408_ = v_isSharedCheck_1428_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_v_1405_);
lean_inc(v_k_1404_);
lean_dec(v_r_1289_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1428_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v_k_1409_; lean_object* v_v_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1424_; 
v_k_1409_ = lean_ctor_get(v_l_1384_, 1);
v_v_1410_ = lean_ctor_get(v_l_1384_, 2);
v_isSharedCheck_1424_ = !lean_is_exclusive(v_l_1384_);
if (v_isSharedCheck_1424_ == 0)
{
lean_object* v_unused_1425_; lean_object* v_unused_1426_; lean_object* v_unused_1427_; 
v_unused_1425_ = lean_ctor_get(v_l_1384_, 4);
lean_dec(v_unused_1425_);
v_unused_1426_ = lean_ctor_get(v_l_1384_, 3);
lean_dec(v_unused_1426_);
v_unused_1427_ = lean_ctor_get(v_l_1384_, 0);
lean_dec(v_unused_1427_);
v___x_1412_ = v_l_1384_;
v_isShared_1413_ = v_isSharedCheck_1424_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_v_1410_);
lean_inc(v_k_1409_);
lean_dec(v_l_1384_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1424_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v___x_1414_; lean_object* v___x_1416_; 
v___x_1414_ = lean_unsigned_to_nat(3u);
if (v_isShared_1413_ == 0)
{
lean_ctor_set(v___x_1412_, 4, v_r_1385_);
lean_ctor_set(v___x_1412_, 3, v_r_1385_);
lean_ctor_set(v___x_1412_, 2, v_v_1287_);
lean_ctor_set(v___x_1412_, 1, v_k_1286_);
lean_ctor_set(v___x_1412_, 0, v___x_1295_);
v___x_1416_ = v___x_1412_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v___x_1295_);
lean_ctor_set(v_reuseFailAlloc_1423_, 1, v_k_1286_);
lean_ctor_set(v_reuseFailAlloc_1423_, 2, v_v_1287_);
lean_ctor_set(v_reuseFailAlloc_1423_, 3, v_r_1385_);
lean_ctor_set(v_reuseFailAlloc_1423_, 4, v_r_1385_);
v___x_1416_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
lean_object* v___x_1418_; 
if (v_isShared_1408_ == 0)
{
lean_ctor_set(v___x_1407_, 3, v_r_1385_);
lean_ctor_set(v___x_1407_, 0, v___x_1295_);
v___x_1418_ = v___x_1407_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v___x_1295_);
lean_ctor_set(v_reuseFailAlloc_1422_, 1, v_k_1404_);
lean_ctor_set(v_reuseFailAlloc_1422_, 2, v_v_1405_);
lean_ctor_set(v_reuseFailAlloc_1422_, 3, v_r_1385_);
lean_ctor_set(v_reuseFailAlloc_1422_, 4, v_r_1385_);
v___x_1418_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
lean_object* v___x_1420_; 
if (v_isShared_1292_ == 0)
{
lean_ctor_set(v___x_1291_, 4, v___x_1418_);
lean_ctor_set(v___x_1291_, 3, v___x_1416_);
lean_ctor_set(v___x_1291_, 2, v_v_1410_);
lean_ctor_set(v___x_1291_, 1, v_k_1409_);
lean_ctor_set(v___x_1291_, 0, v___x_1414_);
v___x_1420_ = v___x_1291_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v___x_1414_);
lean_ctor_set(v_reuseFailAlloc_1421_, 1, v_k_1409_);
lean_ctor_set(v_reuseFailAlloc_1421_, 2, v_v_1410_);
lean_ctor_set(v_reuseFailAlloc_1421_, 3, v___x_1416_);
lean_ctor_set(v_reuseFailAlloc_1421_, 4, v___x_1418_);
v___x_1420_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
return v___x_1420_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_1432_; 
v_r_1432_ = lean_ctor_get(v_r_1289_, 4);
lean_inc(v_r_1432_);
if (lean_obj_tag(v_r_1432_) == 0)
{
lean_object* v_k_1433_; lean_object* v_v_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1445_; 
v_k_1433_ = lean_ctor_get(v_r_1289_, 1);
v_v_1434_ = lean_ctor_get(v_r_1289_, 2);
v_isSharedCheck_1445_ = !lean_is_exclusive(v_r_1289_);
if (v_isSharedCheck_1445_ == 0)
{
lean_object* v_unused_1446_; lean_object* v_unused_1447_; lean_object* v_unused_1448_; 
v_unused_1446_ = lean_ctor_get(v_r_1289_, 4);
lean_dec(v_unused_1446_);
v_unused_1447_ = lean_ctor_get(v_r_1289_, 3);
lean_dec(v_unused_1447_);
v_unused_1448_ = lean_ctor_get(v_r_1289_, 0);
lean_dec(v_unused_1448_);
v___x_1436_ = v_r_1289_;
v_isShared_1437_ = v_isSharedCheck_1445_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_v_1434_);
lean_inc(v_k_1433_);
lean_dec(v_r_1289_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1445_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v___x_1438_; lean_object* v___x_1440_; 
v___x_1438_ = lean_unsigned_to_nat(3u);
if (v_isShared_1437_ == 0)
{
lean_ctor_set(v___x_1436_, 4, v_l_1384_);
lean_ctor_set(v___x_1436_, 2, v_v_1287_);
lean_ctor_set(v___x_1436_, 1, v_k_1286_);
lean_ctor_set(v___x_1436_, 0, v___x_1295_);
v___x_1440_ = v___x_1436_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v___x_1295_);
lean_ctor_set(v_reuseFailAlloc_1444_, 1, v_k_1286_);
lean_ctor_set(v_reuseFailAlloc_1444_, 2, v_v_1287_);
lean_ctor_set(v_reuseFailAlloc_1444_, 3, v_l_1384_);
lean_ctor_set(v_reuseFailAlloc_1444_, 4, v_l_1384_);
v___x_1440_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
lean_object* v___x_1442_; 
if (v_isShared_1292_ == 0)
{
lean_ctor_set(v___x_1291_, 4, v_r_1432_);
lean_ctor_set(v___x_1291_, 3, v___x_1440_);
lean_ctor_set(v___x_1291_, 2, v_v_1434_);
lean_ctor_set(v___x_1291_, 1, v_k_1433_);
lean_ctor_set(v___x_1291_, 0, v___x_1438_);
v___x_1442_ = v___x_1291_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v___x_1438_);
lean_ctor_set(v_reuseFailAlloc_1443_, 1, v_k_1433_);
lean_ctor_set(v_reuseFailAlloc_1443_, 2, v_v_1434_);
lean_ctor_set(v_reuseFailAlloc_1443_, 3, v___x_1440_);
lean_ctor_set(v_reuseFailAlloc_1443_, 4, v_r_1432_);
v___x_1442_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
return v___x_1442_;
}
}
}
}
else
{
lean_object* v_size_1449_; lean_object* v_k_1450_; lean_object* v_v_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1462_; 
v_size_1449_ = lean_ctor_get(v_r_1289_, 0);
v_k_1450_ = lean_ctor_get(v_r_1289_, 1);
v_v_1451_ = lean_ctor_get(v_r_1289_, 2);
v_isSharedCheck_1462_ = !lean_is_exclusive(v_r_1289_);
if (v_isSharedCheck_1462_ == 0)
{
lean_object* v_unused_1463_; lean_object* v_unused_1464_; 
v_unused_1463_ = lean_ctor_get(v_r_1289_, 4);
lean_dec(v_unused_1463_);
v_unused_1464_ = lean_ctor_get(v_r_1289_, 3);
lean_dec(v_unused_1464_);
v___x_1453_ = v_r_1289_;
v_isShared_1454_ = v_isSharedCheck_1462_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_v_1451_);
lean_inc(v_k_1450_);
lean_inc(v_size_1449_);
lean_dec(v_r_1289_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1462_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1456_; 
if (v_isShared_1454_ == 0)
{
lean_ctor_set(v___x_1453_, 3, v_r_1432_);
v___x_1456_ = v___x_1453_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v_size_1449_);
lean_ctor_set(v_reuseFailAlloc_1461_, 1, v_k_1450_);
lean_ctor_set(v_reuseFailAlloc_1461_, 2, v_v_1451_);
lean_ctor_set(v_reuseFailAlloc_1461_, 3, v_r_1432_);
lean_ctor_set(v_reuseFailAlloc_1461_, 4, v_r_1432_);
v___x_1456_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
lean_object* v___x_1457_; lean_object* v___x_1459_; 
v___x_1457_ = lean_unsigned_to_nat(2u);
if (v_isShared_1292_ == 0)
{
lean_ctor_set(v___x_1291_, 4, v___x_1456_);
lean_ctor_set(v___x_1291_, 3, v_r_1432_);
lean_ctor_set(v___x_1291_, 0, v___x_1457_);
v___x_1459_ = v___x_1291_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1460_; 
v_reuseFailAlloc_1460_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1460_, 0, v___x_1457_);
lean_ctor_set(v_reuseFailAlloc_1460_, 1, v_k_1286_);
lean_ctor_set(v_reuseFailAlloc_1460_, 2, v_v_1287_);
lean_ctor_set(v_reuseFailAlloc_1460_, 3, v_r_1432_);
lean_ctor_set(v_reuseFailAlloc_1460_, 4, v___x_1456_);
v___x_1459_ = v_reuseFailAlloc_1460_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
return v___x_1459_;
}
}
}
}
}
}
else
{
lean_object* v___x_1466_; 
if (v_isShared_1292_ == 0)
{
lean_ctor_set(v___x_1291_, 3, v_r_1289_);
lean_ctor_set(v___x_1291_, 0, v___x_1295_);
v___x_1466_ = v___x_1291_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v___x_1295_);
lean_ctor_set(v_reuseFailAlloc_1467_, 1, v_k_1286_);
lean_ctor_set(v_reuseFailAlloc_1467_, 2, v_v_1287_);
lean_ctor_set(v_reuseFailAlloc_1467_, 3, v_r_1289_);
lean_ctor_set(v_reuseFailAlloc_1467_, 4, v_r_1289_);
v___x_1466_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
return v___x_1466_;
}
}
}
}
case 1:
{
lean_del_object(v___x_1291_);
lean_dec(v_v_1287_);
lean_dec(v_k_1286_);
if (lean_obj_tag(v_l_1288_) == 0)
{
if (lean_obj_tag(v_r_1289_) == 0)
{
lean_object* v_size_1468_; lean_object* v_k_1469_; lean_object* v_v_1470_; lean_object* v_l_1471_; lean_object* v_r_1472_; lean_object* v_size_1473_; lean_object* v_k_1474_; lean_object* v_v_1475_; lean_object* v_l_1476_; lean_object* v_r_1477_; lean_object* v___x_1478_; uint8_t v___x_1479_; 
v_size_1468_ = lean_ctor_get(v_l_1288_, 0);
v_k_1469_ = lean_ctor_get(v_l_1288_, 1);
v_v_1470_ = lean_ctor_get(v_l_1288_, 2);
v_l_1471_ = lean_ctor_get(v_l_1288_, 3);
v_r_1472_ = lean_ctor_get(v_l_1288_, 4);
lean_inc(v_r_1472_);
v_size_1473_ = lean_ctor_get(v_r_1289_, 0);
v_k_1474_ = lean_ctor_get(v_r_1289_, 1);
v_v_1475_ = lean_ctor_get(v_r_1289_, 2);
v_l_1476_ = lean_ctor_get(v_r_1289_, 3);
lean_inc(v_l_1476_);
v_r_1477_ = lean_ctor_get(v_r_1289_, 4);
v___x_1478_ = lean_unsigned_to_nat(1u);
v___x_1479_ = lean_nat_dec_lt(v_size_1468_, v_size_1473_);
if (v___x_1479_ == 0)
{
lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1615_; 
lean_inc(v_l_1471_);
lean_inc(v_v_1470_);
lean_inc(v_k_1469_);
v_isSharedCheck_1615_ = !lean_is_exclusive(v_l_1288_);
if (v_isSharedCheck_1615_ == 0)
{
lean_object* v_unused_1616_; lean_object* v_unused_1617_; lean_object* v_unused_1618_; lean_object* v_unused_1619_; lean_object* v_unused_1620_; 
v_unused_1616_ = lean_ctor_get(v_l_1288_, 4);
lean_dec(v_unused_1616_);
v_unused_1617_ = lean_ctor_get(v_l_1288_, 3);
lean_dec(v_unused_1617_);
v_unused_1618_ = lean_ctor_get(v_l_1288_, 2);
lean_dec(v_unused_1618_);
v_unused_1619_ = lean_ctor_get(v_l_1288_, 1);
lean_dec(v_unused_1619_);
v_unused_1620_ = lean_ctor_get(v_l_1288_, 0);
lean_dec(v_unused_1620_);
v___x_1481_ = v_l_1288_;
v_isShared_1482_ = v_isSharedCheck_1615_;
goto v_resetjp_1480_;
}
else
{
lean_dec(v_l_1288_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1615_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v___x_1483_; lean_object* v_tree_1484_; 
v___x_1483_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_1469_, v_v_1470_, v_l_1471_, v_r_1472_);
v_tree_1484_ = lean_ctor_get(v___x_1483_, 2);
lean_inc(v_tree_1484_);
if (lean_obj_tag(v_tree_1484_) == 0)
{
lean_object* v_k_1485_; lean_object* v_v_1486_; lean_object* v_size_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; uint8_t v___x_1490_; 
v_k_1485_ = lean_ctor_get(v___x_1483_, 0);
lean_inc(v_k_1485_);
v_v_1486_ = lean_ctor_get(v___x_1483_, 1);
lean_inc(v_v_1486_);
lean_dec_ref(v___x_1483_);
v_size_1487_ = lean_ctor_get(v_tree_1484_, 0);
v___x_1488_ = lean_unsigned_to_nat(3u);
v___x_1489_ = lean_nat_mul(v___x_1488_, v_size_1487_);
v___x_1490_ = lean_nat_dec_lt(v___x_1489_, v_size_1473_);
lean_dec(v___x_1489_);
if (v___x_1490_ == 0)
{
lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1494_; 
lean_dec(v_l_1476_);
v___x_1491_ = lean_nat_add(v___x_1478_, v_size_1487_);
v___x_1492_ = lean_nat_add(v___x_1491_, v_size_1473_);
lean_dec(v___x_1491_);
if (v_isShared_1482_ == 0)
{
lean_ctor_set(v___x_1481_, 4, v_r_1289_);
lean_ctor_set(v___x_1481_, 3, v_tree_1484_);
lean_ctor_set(v___x_1481_, 2, v_v_1486_);
lean_ctor_set(v___x_1481_, 1, v_k_1485_);
lean_ctor_set(v___x_1481_, 0, v___x_1492_);
v___x_1494_ = v___x_1481_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v___x_1492_);
lean_ctor_set(v_reuseFailAlloc_1495_, 1, v_k_1485_);
lean_ctor_set(v_reuseFailAlloc_1495_, 2, v_v_1486_);
lean_ctor_set(v_reuseFailAlloc_1495_, 3, v_tree_1484_);
lean_ctor_set(v_reuseFailAlloc_1495_, 4, v_r_1289_);
v___x_1494_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
return v___x_1494_;
}
}
else
{
lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1550_; 
lean_inc(v_r_1477_);
lean_inc(v_v_1475_);
lean_inc(v_k_1474_);
lean_inc(v_size_1473_);
v_isSharedCheck_1550_ = !lean_is_exclusive(v_r_1289_);
if (v_isSharedCheck_1550_ == 0)
{
lean_object* v_unused_1551_; lean_object* v_unused_1552_; lean_object* v_unused_1553_; lean_object* v_unused_1554_; lean_object* v_unused_1555_; 
v_unused_1551_ = lean_ctor_get(v_r_1289_, 4);
lean_dec(v_unused_1551_);
v_unused_1552_ = lean_ctor_get(v_r_1289_, 3);
lean_dec(v_unused_1552_);
v_unused_1553_ = lean_ctor_get(v_r_1289_, 2);
lean_dec(v_unused_1553_);
v_unused_1554_ = lean_ctor_get(v_r_1289_, 1);
lean_dec(v_unused_1554_);
v_unused_1555_ = lean_ctor_get(v_r_1289_, 0);
lean_dec(v_unused_1555_);
v___x_1497_ = v_r_1289_;
v_isShared_1498_ = v_isSharedCheck_1550_;
goto v_resetjp_1496_;
}
else
{
lean_dec(v_r_1289_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1550_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v_size_1499_; lean_object* v_k_1500_; lean_object* v_v_1501_; lean_object* v_l_1502_; lean_object* v_r_1503_; lean_object* v_size_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; uint8_t v___x_1507_; 
v_size_1499_ = lean_ctor_get(v_l_1476_, 0);
v_k_1500_ = lean_ctor_get(v_l_1476_, 1);
v_v_1501_ = lean_ctor_get(v_l_1476_, 2);
v_l_1502_ = lean_ctor_get(v_l_1476_, 3);
v_r_1503_ = lean_ctor_get(v_l_1476_, 4);
v_size_1504_ = lean_ctor_get(v_r_1477_, 0);
v___x_1505_ = lean_unsigned_to_nat(2u);
v___x_1506_ = lean_nat_mul(v___x_1505_, v_size_1504_);
v___x_1507_ = lean_nat_dec_lt(v_size_1499_, v___x_1506_);
lean_dec(v___x_1506_);
if (v___x_1507_ == 0)
{
lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1535_; 
lean_inc(v_r_1503_);
lean_inc(v_l_1502_);
lean_inc(v_v_1501_);
lean_inc(v_k_1500_);
v_isSharedCheck_1535_ = !lean_is_exclusive(v_l_1476_);
if (v_isSharedCheck_1535_ == 0)
{
lean_object* v_unused_1536_; lean_object* v_unused_1537_; lean_object* v_unused_1538_; lean_object* v_unused_1539_; lean_object* v_unused_1540_; 
v_unused_1536_ = lean_ctor_get(v_l_1476_, 4);
lean_dec(v_unused_1536_);
v_unused_1537_ = lean_ctor_get(v_l_1476_, 3);
lean_dec(v_unused_1537_);
v_unused_1538_ = lean_ctor_get(v_l_1476_, 2);
lean_dec(v_unused_1538_);
v_unused_1539_ = lean_ctor_get(v_l_1476_, 1);
lean_dec(v_unused_1539_);
v_unused_1540_ = lean_ctor_get(v_l_1476_, 0);
lean_dec(v_unused_1540_);
v___x_1509_ = v_l_1476_;
v_isShared_1510_ = v_isSharedCheck_1535_;
goto v_resetjp_1508_;
}
else
{
lean_dec(v_l_1476_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1535_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___y_1514_; lean_object* v___y_1515_; lean_object* v___y_1516_; lean_object* v___y_1525_; 
v___x_1511_ = lean_nat_add(v___x_1478_, v_size_1487_);
v___x_1512_ = lean_nat_add(v___x_1511_, v_size_1473_);
lean_dec(v_size_1473_);
if (lean_obj_tag(v_l_1502_) == 0)
{
lean_object* v_size_1533_; 
v_size_1533_ = lean_ctor_get(v_l_1502_, 0);
lean_inc(v_size_1533_);
v___y_1525_ = v_size_1533_;
goto v___jp_1524_;
}
else
{
lean_object* v___x_1534_; 
v___x_1534_ = lean_unsigned_to_nat(0u);
v___y_1525_ = v___x_1534_;
goto v___jp_1524_;
}
v___jp_1513_:
{
lean_object* v___x_1517_; lean_object* v___x_1519_; 
v___x_1517_ = lean_nat_add(v___y_1515_, v___y_1516_);
lean_dec(v___y_1516_);
lean_dec(v___y_1515_);
if (v_isShared_1510_ == 0)
{
lean_ctor_set(v___x_1509_, 4, v_r_1477_);
lean_ctor_set(v___x_1509_, 3, v_r_1503_);
lean_ctor_set(v___x_1509_, 2, v_v_1475_);
lean_ctor_set(v___x_1509_, 1, v_k_1474_);
lean_ctor_set(v___x_1509_, 0, v___x_1517_);
v___x_1519_ = v___x_1509_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v___x_1517_);
lean_ctor_set(v_reuseFailAlloc_1523_, 1, v_k_1474_);
lean_ctor_set(v_reuseFailAlloc_1523_, 2, v_v_1475_);
lean_ctor_set(v_reuseFailAlloc_1523_, 3, v_r_1503_);
lean_ctor_set(v_reuseFailAlloc_1523_, 4, v_r_1477_);
v___x_1519_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
lean_object* v___x_1521_; 
if (v_isShared_1498_ == 0)
{
lean_ctor_set(v___x_1497_, 4, v___x_1519_);
lean_ctor_set(v___x_1497_, 3, v___y_1514_);
lean_ctor_set(v___x_1497_, 2, v_v_1501_);
lean_ctor_set(v___x_1497_, 1, v_k_1500_);
lean_ctor_set(v___x_1497_, 0, v___x_1512_);
v___x_1521_ = v___x_1497_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1522_; 
v_reuseFailAlloc_1522_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1522_, 0, v___x_1512_);
lean_ctor_set(v_reuseFailAlloc_1522_, 1, v_k_1500_);
lean_ctor_set(v_reuseFailAlloc_1522_, 2, v_v_1501_);
lean_ctor_set(v_reuseFailAlloc_1522_, 3, v___y_1514_);
lean_ctor_set(v_reuseFailAlloc_1522_, 4, v___x_1519_);
v___x_1521_ = v_reuseFailAlloc_1522_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
return v___x_1521_;
}
}
}
v___jp_1524_:
{
lean_object* v___x_1526_; lean_object* v___x_1528_; 
v___x_1526_ = lean_nat_add(v___x_1511_, v___y_1525_);
lean_dec(v___y_1525_);
lean_dec(v___x_1511_);
if (v_isShared_1482_ == 0)
{
lean_ctor_set(v___x_1481_, 4, v_l_1502_);
lean_ctor_set(v___x_1481_, 3, v_tree_1484_);
lean_ctor_set(v___x_1481_, 2, v_v_1486_);
lean_ctor_set(v___x_1481_, 1, v_k_1485_);
lean_ctor_set(v___x_1481_, 0, v___x_1526_);
v___x_1528_ = v___x_1481_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v___x_1526_);
lean_ctor_set(v_reuseFailAlloc_1532_, 1, v_k_1485_);
lean_ctor_set(v_reuseFailAlloc_1532_, 2, v_v_1486_);
lean_ctor_set(v_reuseFailAlloc_1532_, 3, v_tree_1484_);
lean_ctor_set(v_reuseFailAlloc_1532_, 4, v_l_1502_);
v___x_1528_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
lean_object* v___x_1529_; 
v___x_1529_ = lean_nat_add(v___x_1478_, v_size_1504_);
if (lean_obj_tag(v_r_1503_) == 0)
{
lean_object* v_size_1530_; 
v_size_1530_ = lean_ctor_get(v_r_1503_, 0);
lean_inc(v_size_1530_);
v___y_1514_ = v___x_1528_;
v___y_1515_ = v___x_1529_;
v___y_1516_ = v_size_1530_;
goto v___jp_1513_;
}
else
{
lean_object* v___x_1531_; 
v___x_1531_ = lean_unsigned_to_nat(0u);
v___y_1514_ = v___x_1528_;
v___y_1515_ = v___x_1529_;
v___y_1516_ = v___x_1531_;
goto v___jp_1513_;
}
}
}
}
}
else
{
lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1545_; 
v___x_1541_ = lean_nat_add(v___x_1478_, v_size_1487_);
v___x_1542_ = lean_nat_add(v___x_1541_, v_size_1473_);
lean_dec(v_size_1473_);
v___x_1543_ = lean_nat_add(v___x_1541_, v_size_1499_);
lean_dec(v___x_1541_);
if (v_isShared_1498_ == 0)
{
lean_ctor_set(v___x_1497_, 4, v_l_1476_);
lean_ctor_set(v___x_1497_, 3, v_tree_1484_);
lean_ctor_set(v___x_1497_, 2, v_v_1486_);
lean_ctor_set(v___x_1497_, 1, v_k_1485_);
lean_ctor_set(v___x_1497_, 0, v___x_1543_);
v___x_1545_ = v___x_1497_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v___x_1543_);
lean_ctor_set(v_reuseFailAlloc_1549_, 1, v_k_1485_);
lean_ctor_set(v_reuseFailAlloc_1549_, 2, v_v_1486_);
lean_ctor_set(v_reuseFailAlloc_1549_, 3, v_tree_1484_);
lean_ctor_set(v_reuseFailAlloc_1549_, 4, v_l_1476_);
v___x_1545_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
lean_object* v___x_1547_; 
if (v_isShared_1482_ == 0)
{
lean_ctor_set(v___x_1481_, 4, v_r_1477_);
lean_ctor_set(v___x_1481_, 3, v___x_1545_);
lean_ctor_set(v___x_1481_, 2, v_v_1475_);
lean_ctor_set(v___x_1481_, 1, v_k_1474_);
lean_ctor_set(v___x_1481_, 0, v___x_1542_);
v___x_1547_ = v___x_1481_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v___x_1542_);
lean_ctor_set(v_reuseFailAlloc_1548_, 1, v_k_1474_);
lean_ctor_set(v_reuseFailAlloc_1548_, 2, v_v_1475_);
lean_ctor_set(v_reuseFailAlloc_1548_, 3, v___x_1545_);
lean_ctor_set(v_reuseFailAlloc_1548_, 4, v_r_1477_);
v___x_1547_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
return v___x_1547_;
}
}
}
}
}
}
else
{
lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1609_; 
lean_inc(v_r_1477_);
lean_inc(v_v_1475_);
lean_inc(v_k_1474_);
lean_inc(v_size_1473_);
v_isSharedCheck_1609_ = !lean_is_exclusive(v_r_1289_);
if (v_isSharedCheck_1609_ == 0)
{
lean_object* v_unused_1610_; lean_object* v_unused_1611_; lean_object* v_unused_1612_; lean_object* v_unused_1613_; lean_object* v_unused_1614_; 
v_unused_1610_ = lean_ctor_get(v_r_1289_, 4);
lean_dec(v_unused_1610_);
v_unused_1611_ = lean_ctor_get(v_r_1289_, 3);
lean_dec(v_unused_1611_);
v_unused_1612_ = lean_ctor_get(v_r_1289_, 2);
lean_dec(v_unused_1612_);
v_unused_1613_ = lean_ctor_get(v_r_1289_, 1);
lean_dec(v_unused_1613_);
v_unused_1614_ = lean_ctor_get(v_r_1289_, 0);
lean_dec(v_unused_1614_);
v___x_1557_ = v_r_1289_;
v_isShared_1558_ = v_isSharedCheck_1609_;
goto v_resetjp_1556_;
}
else
{
lean_dec(v_r_1289_);
v___x_1557_ = lean_box(0);
v_isShared_1558_ = v_isSharedCheck_1609_;
goto v_resetjp_1556_;
}
v_resetjp_1556_:
{
if (lean_obj_tag(v_l_1476_) == 0)
{
if (lean_obj_tag(v_r_1477_) == 0)
{
lean_object* v_k_1559_; lean_object* v_v_1560_; lean_object* v_size_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1565_; 
v_k_1559_ = lean_ctor_get(v___x_1483_, 0);
lean_inc(v_k_1559_);
v_v_1560_ = lean_ctor_get(v___x_1483_, 1);
lean_inc(v_v_1560_);
lean_dec_ref(v___x_1483_);
v_size_1561_ = lean_ctor_get(v_l_1476_, 0);
v___x_1562_ = lean_nat_add(v___x_1478_, v_size_1473_);
lean_dec(v_size_1473_);
v___x_1563_ = lean_nat_add(v___x_1478_, v_size_1561_);
if (v_isShared_1558_ == 0)
{
lean_ctor_set(v___x_1557_, 4, v_l_1476_);
lean_ctor_set(v___x_1557_, 3, v_tree_1484_);
lean_ctor_set(v___x_1557_, 2, v_v_1560_);
lean_ctor_set(v___x_1557_, 1, v_k_1559_);
lean_ctor_set(v___x_1557_, 0, v___x_1563_);
v___x_1565_ = v___x_1557_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v___x_1563_);
lean_ctor_set(v_reuseFailAlloc_1569_, 1, v_k_1559_);
lean_ctor_set(v_reuseFailAlloc_1569_, 2, v_v_1560_);
lean_ctor_set(v_reuseFailAlloc_1569_, 3, v_tree_1484_);
lean_ctor_set(v_reuseFailAlloc_1569_, 4, v_l_1476_);
v___x_1565_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
lean_object* v___x_1567_; 
if (v_isShared_1482_ == 0)
{
lean_ctor_set(v___x_1481_, 4, v_r_1477_);
lean_ctor_set(v___x_1481_, 3, v___x_1565_);
lean_ctor_set(v___x_1481_, 2, v_v_1475_);
lean_ctor_set(v___x_1481_, 1, v_k_1474_);
lean_ctor_set(v___x_1481_, 0, v___x_1562_);
v___x_1567_ = v___x_1481_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v___x_1562_);
lean_ctor_set(v_reuseFailAlloc_1568_, 1, v_k_1474_);
lean_ctor_set(v_reuseFailAlloc_1568_, 2, v_v_1475_);
lean_ctor_set(v_reuseFailAlloc_1568_, 3, v___x_1565_);
lean_ctor_set(v_reuseFailAlloc_1568_, 4, v_r_1477_);
v___x_1567_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
return v___x_1567_;
}
}
}
else
{
lean_object* v_k_1570_; lean_object* v_v_1571_; lean_object* v_k_1572_; lean_object* v_v_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1587_; 
lean_dec(v_size_1473_);
v_k_1570_ = lean_ctor_get(v___x_1483_, 0);
lean_inc(v_k_1570_);
v_v_1571_ = lean_ctor_get(v___x_1483_, 1);
lean_inc(v_v_1571_);
lean_dec_ref(v___x_1483_);
v_k_1572_ = lean_ctor_get(v_l_1476_, 1);
v_v_1573_ = lean_ctor_get(v_l_1476_, 2);
v_isSharedCheck_1587_ = !lean_is_exclusive(v_l_1476_);
if (v_isSharedCheck_1587_ == 0)
{
lean_object* v_unused_1588_; lean_object* v_unused_1589_; lean_object* v_unused_1590_; 
v_unused_1588_ = lean_ctor_get(v_l_1476_, 4);
lean_dec(v_unused_1588_);
v_unused_1589_ = lean_ctor_get(v_l_1476_, 3);
lean_dec(v_unused_1589_);
v_unused_1590_ = lean_ctor_get(v_l_1476_, 0);
lean_dec(v_unused_1590_);
v___x_1575_ = v_l_1476_;
v_isShared_1576_ = v_isSharedCheck_1587_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_v_1573_);
lean_inc(v_k_1572_);
lean_dec(v_l_1476_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1587_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v___x_1577_; lean_object* v___x_1579_; 
v___x_1577_ = lean_unsigned_to_nat(3u);
if (v_isShared_1576_ == 0)
{
lean_ctor_set(v___x_1575_, 4, v_r_1477_);
lean_ctor_set(v___x_1575_, 3, v_r_1477_);
lean_ctor_set(v___x_1575_, 2, v_v_1571_);
lean_ctor_set(v___x_1575_, 1, v_k_1570_);
lean_ctor_set(v___x_1575_, 0, v___x_1478_);
v___x_1579_ = v___x_1575_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v___x_1478_);
lean_ctor_set(v_reuseFailAlloc_1586_, 1, v_k_1570_);
lean_ctor_set(v_reuseFailAlloc_1586_, 2, v_v_1571_);
lean_ctor_set(v_reuseFailAlloc_1586_, 3, v_r_1477_);
lean_ctor_set(v_reuseFailAlloc_1586_, 4, v_r_1477_);
v___x_1579_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
lean_object* v___x_1581_; 
if (v_isShared_1558_ == 0)
{
lean_ctor_set(v___x_1557_, 3, v_r_1477_);
lean_ctor_set(v___x_1557_, 0, v___x_1478_);
v___x_1581_ = v___x_1557_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v___x_1478_);
lean_ctor_set(v_reuseFailAlloc_1585_, 1, v_k_1474_);
lean_ctor_set(v_reuseFailAlloc_1585_, 2, v_v_1475_);
lean_ctor_set(v_reuseFailAlloc_1585_, 3, v_r_1477_);
lean_ctor_set(v_reuseFailAlloc_1585_, 4, v_r_1477_);
v___x_1581_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
lean_object* v___x_1583_; 
if (v_isShared_1482_ == 0)
{
lean_ctor_set(v___x_1481_, 4, v___x_1581_);
lean_ctor_set(v___x_1481_, 3, v___x_1579_);
lean_ctor_set(v___x_1481_, 2, v_v_1573_);
lean_ctor_set(v___x_1481_, 1, v_k_1572_);
lean_ctor_set(v___x_1481_, 0, v___x_1577_);
v___x_1583_ = v___x_1481_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v___x_1577_);
lean_ctor_set(v_reuseFailAlloc_1584_, 1, v_k_1572_);
lean_ctor_set(v_reuseFailAlloc_1584_, 2, v_v_1573_);
lean_ctor_set(v_reuseFailAlloc_1584_, 3, v___x_1579_);
lean_ctor_set(v_reuseFailAlloc_1584_, 4, v___x_1581_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
return v___x_1583_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1477_) == 0)
{
lean_object* v_k_1591_; lean_object* v_v_1592_; lean_object* v___x_1593_; lean_object* v___x_1595_; 
lean_dec(v_size_1473_);
v_k_1591_ = lean_ctor_get(v___x_1483_, 0);
lean_inc(v_k_1591_);
v_v_1592_ = lean_ctor_get(v___x_1483_, 1);
lean_inc(v_v_1592_);
lean_dec_ref(v___x_1483_);
v___x_1593_ = lean_unsigned_to_nat(3u);
if (v_isShared_1558_ == 0)
{
lean_ctor_set(v___x_1557_, 4, v_l_1476_);
lean_ctor_set(v___x_1557_, 2, v_v_1592_);
lean_ctor_set(v___x_1557_, 1, v_k_1591_);
lean_ctor_set(v___x_1557_, 0, v___x_1478_);
v___x_1595_ = v___x_1557_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v___x_1478_);
lean_ctor_set(v_reuseFailAlloc_1599_, 1, v_k_1591_);
lean_ctor_set(v_reuseFailAlloc_1599_, 2, v_v_1592_);
lean_ctor_set(v_reuseFailAlloc_1599_, 3, v_l_1476_);
lean_ctor_set(v_reuseFailAlloc_1599_, 4, v_l_1476_);
v___x_1595_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
lean_object* v___x_1597_; 
if (v_isShared_1482_ == 0)
{
lean_ctor_set(v___x_1481_, 4, v_r_1477_);
lean_ctor_set(v___x_1481_, 3, v___x_1595_);
lean_ctor_set(v___x_1481_, 2, v_v_1475_);
lean_ctor_set(v___x_1481_, 1, v_k_1474_);
lean_ctor_set(v___x_1481_, 0, v___x_1593_);
v___x_1597_ = v___x_1481_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v___x_1593_);
lean_ctor_set(v_reuseFailAlloc_1598_, 1, v_k_1474_);
lean_ctor_set(v_reuseFailAlloc_1598_, 2, v_v_1475_);
lean_ctor_set(v_reuseFailAlloc_1598_, 3, v___x_1595_);
lean_ctor_set(v_reuseFailAlloc_1598_, 4, v_r_1477_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
return v___x_1597_;
}
}
}
else
{
lean_object* v_k_1600_; lean_object* v_v_1601_; lean_object* v___x_1603_; 
v_k_1600_ = lean_ctor_get(v___x_1483_, 0);
lean_inc(v_k_1600_);
v_v_1601_ = lean_ctor_get(v___x_1483_, 1);
lean_inc(v_v_1601_);
lean_dec_ref(v___x_1483_);
if (v_isShared_1558_ == 0)
{
lean_ctor_set(v___x_1557_, 3, v_r_1477_);
v___x_1603_ = v___x_1557_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v_size_1473_);
lean_ctor_set(v_reuseFailAlloc_1608_, 1, v_k_1474_);
lean_ctor_set(v_reuseFailAlloc_1608_, 2, v_v_1475_);
lean_ctor_set(v_reuseFailAlloc_1608_, 3, v_r_1477_);
lean_ctor_set(v_reuseFailAlloc_1608_, 4, v_r_1477_);
v___x_1603_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
lean_object* v___x_1604_; lean_object* v___x_1606_; 
v___x_1604_ = lean_unsigned_to_nat(2u);
if (v_isShared_1482_ == 0)
{
lean_ctor_set(v___x_1481_, 4, v___x_1603_);
lean_ctor_set(v___x_1481_, 3, v_r_1477_);
lean_ctor_set(v___x_1481_, 2, v_v_1601_);
lean_ctor_set(v___x_1481_, 1, v_k_1600_);
lean_ctor_set(v___x_1481_, 0, v___x_1604_);
v___x_1606_ = v___x_1481_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v___x_1604_);
lean_ctor_set(v_reuseFailAlloc_1607_, 1, v_k_1600_);
lean_ctor_set(v_reuseFailAlloc_1607_, 2, v_v_1601_);
lean_ctor_set(v_reuseFailAlloc_1607_, 3, v_r_1477_);
lean_ctor_set(v_reuseFailAlloc_1607_, 4, v___x_1603_);
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
}
else
{
lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1773_; 
lean_inc(v_r_1477_);
lean_inc(v_v_1475_);
lean_inc(v_k_1474_);
v_isSharedCheck_1773_ = !lean_is_exclusive(v_r_1289_);
if (v_isSharedCheck_1773_ == 0)
{
lean_object* v_unused_1774_; lean_object* v_unused_1775_; lean_object* v_unused_1776_; lean_object* v_unused_1777_; lean_object* v_unused_1778_; 
v_unused_1774_ = lean_ctor_get(v_r_1289_, 4);
lean_dec(v_unused_1774_);
v_unused_1775_ = lean_ctor_get(v_r_1289_, 3);
lean_dec(v_unused_1775_);
v_unused_1776_ = lean_ctor_get(v_r_1289_, 2);
lean_dec(v_unused_1776_);
v_unused_1777_ = lean_ctor_get(v_r_1289_, 1);
lean_dec(v_unused_1777_);
v_unused_1778_ = lean_ctor_get(v_r_1289_, 0);
lean_dec(v_unused_1778_);
v___x_1622_ = v_r_1289_;
v_isShared_1623_ = v_isSharedCheck_1773_;
goto v_resetjp_1621_;
}
else
{
lean_dec(v_r_1289_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1773_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1624_; lean_object* v_tree_1625_; 
v___x_1624_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_1474_, v_v_1475_, v_l_1476_, v_r_1477_);
v_tree_1625_ = lean_ctor_get(v___x_1624_, 2);
lean_inc(v_tree_1625_);
if (lean_obj_tag(v_tree_1625_) == 0)
{
lean_object* v_k_1626_; lean_object* v_v_1627_; lean_object* v_size_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; uint8_t v___x_1631_; 
v_k_1626_ = lean_ctor_get(v___x_1624_, 0);
lean_inc(v_k_1626_);
v_v_1627_ = lean_ctor_get(v___x_1624_, 1);
lean_inc(v_v_1627_);
lean_dec_ref(v___x_1624_);
v_size_1628_ = lean_ctor_get(v_tree_1625_, 0);
v___x_1629_ = lean_unsigned_to_nat(3u);
v___x_1630_ = lean_nat_mul(v___x_1629_, v_size_1628_);
v___x_1631_ = lean_nat_dec_lt(v___x_1630_, v_size_1468_);
lean_dec(v___x_1630_);
if (v___x_1631_ == 0)
{
lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1635_; 
lean_dec(v_r_1472_);
v___x_1632_ = lean_nat_add(v___x_1478_, v_size_1468_);
v___x_1633_ = lean_nat_add(v___x_1632_, v_size_1628_);
lean_dec(v___x_1632_);
if (v_isShared_1623_ == 0)
{
lean_ctor_set(v___x_1622_, 4, v_tree_1625_);
lean_ctor_set(v___x_1622_, 3, v_l_1288_);
lean_ctor_set(v___x_1622_, 2, v_v_1627_);
lean_ctor_set(v___x_1622_, 1, v_k_1626_);
lean_ctor_set(v___x_1622_, 0, v___x_1633_);
v___x_1635_ = v___x_1622_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v___x_1633_);
lean_ctor_set(v_reuseFailAlloc_1636_, 1, v_k_1626_);
lean_ctor_set(v_reuseFailAlloc_1636_, 2, v_v_1627_);
lean_ctor_set(v_reuseFailAlloc_1636_, 3, v_l_1288_);
lean_ctor_set(v_reuseFailAlloc_1636_, 4, v_tree_1625_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
return v___x_1635_;
}
}
else
{
lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1702_; 
lean_inc(v_l_1471_);
lean_inc(v_v_1470_);
lean_inc(v_k_1469_);
lean_inc(v_size_1468_);
v_isSharedCheck_1702_ = !lean_is_exclusive(v_l_1288_);
if (v_isSharedCheck_1702_ == 0)
{
lean_object* v_unused_1703_; lean_object* v_unused_1704_; lean_object* v_unused_1705_; lean_object* v_unused_1706_; lean_object* v_unused_1707_; 
v_unused_1703_ = lean_ctor_get(v_l_1288_, 4);
lean_dec(v_unused_1703_);
v_unused_1704_ = lean_ctor_get(v_l_1288_, 3);
lean_dec(v_unused_1704_);
v_unused_1705_ = lean_ctor_get(v_l_1288_, 2);
lean_dec(v_unused_1705_);
v_unused_1706_ = lean_ctor_get(v_l_1288_, 1);
lean_dec(v_unused_1706_);
v_unused_1707_ = lean_ctor_get(v_l_1288_, 0);
lean_dec(v_unused_1707_);
v___x_1638_ = v_l_1288_;
v_isShared_1639_ = v_isSharedCheck_1702_;
goto v_resetjp_1637_;
}
else
{
lean_dec(v_l_1288_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1702_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v_size_1640_; lean_object* v_size_1641_; lean_object* v_k_1642_; lean_object* v_v_1643_; lean_object* v_l_1644_; lean_object* v_r_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; uint8_t v___x_1648_; 
v_size_1640_ = lean_ctor_get(v_l_1471_, 0);
v_size_1641_ = lean_ctor_get(v_r_1472_, 0);
v_k_1642_ = lean_ctor_get(v_r_1472_, 1);
v_v_1643_ = lean_ctor_get(v_r_1472_, 2);
v_l_1644_ = lean_ctor_get(v_r_1472_, 3);
v_r_1645_ = lean_ctor_get(v_r_1472_, 4);
v___x_1646_ = lean_unsigned_to_nat(2u);
v___x_1647_ = lean_nat_mul(v___x_1646_, v_size_1640_);
v___x_1648_ = lean_nat_dec_lt(v_size_1641_, v___x_1647_);
lean_dec(v___x_1647_);
if (v___x_1648_ == 0)
{
lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1686_; 
lean_inc(v_r_1645_);
lean_inc(v_l_1644_);
lean_inc(v_v_1643_);
lean_inc(v_k_1642_);
lean_del_object(v___x_1638_);
v_isSharedCheck_1686_ = !lean_is_exclusive(v_r_1472_);
if (v_isSharedCheck_1686_ == 0)
{
lean_object* v_unused_1687_; lean_object* v_unused_1688_; lean_object* v_unused_1689_; lean_object* v_unused_1690_; lean_object* v_unused_1691_; 
v_unused_1687_ = lean_ctor_get(v_r_1472_, 4);
lean_dec(v_unused_1687_);
v_unused_1688_ = lean_ctor_get(v_r_1472_, 3);
lean_dec(v_unused_1688_);
v_unused_1689_ = lean_ctor_get(v_r_1472_, 2);
lean_dec(v_unused_1689_);
v_unused_1690_ = lean_ctor_get(v_r_1472_, 1);
lean_dec(v_unused_1690_);
v_unused_1691_ = lean_ctor_get(v_r_1472_, 0);
lean_dec(v_unused_1691_);
v___x_1650_ = v_r_1472_;
v_isShared_1651_ = v_isSharedCheck_1686_;
goto v_resetjp_1649_;
}
else
{
lean_dec(v_r_1472_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1686_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___y_1655_; lean_object* v___y_1656_; lean_object* v___y_1657_; lean_object* v___x_1674_; lean_object* v___y_1676_; 
v___x_1652_ = lean_nat_add(v___x_1478_, v_size_1468_);
lean_dec(v_size_1468_);
v___x_1653_ = lean_nat_add(v___x_1652_, v_size_1628_);
lean_dec(v___x_1652_);
v___x_1674_ = lean_nat_add(v___x_1478_, v_size_1640_);
if (lean_obj_tag(v_l_1644_) == 0)
{
lean_object* v_size_1684_; 
v_size_1684_ = lean_ctor_get(v_l_1644_, 0);
lean_inc(v_size_1684_);
v___y_1676_ = v_size_1684_;
goto v___jp_1675_;
}
else
{
lean_object* v___x_1685_; 
v___x_1685_ = lean_unsigned_to_nat(0u);
v___y_1676_ = v___x_1685_;
goto v___jp_1675_;
}
v___jp_1654_:
{
lean_object* v___x_1658_; lean_object* v___x_1660_; 
v___x_1658_ = lean_nat_add(v___y_1656_, v___y_1657_);
lean_dec(v___y_1657_);
lean_dec(v___y_1656_);
lean_inc_ref(v_tree_1625_);
if (v_isShared_1651_ == 0)
{
lean_ctor_set(v___x_1650_, 4, v_tree_1625_);
lean_ctor_set(v___x_1650_, 3, v_r_1645_);
lean_ctor_set(v___x_1650_, 2, v_v_1627_);
lean_ctor_set(v___x_1650_, 1, v_k_1626_);
lean_ctor_set(v___x_1650_, 0, v___x_1658_);
v___x_1660_ = v___x_1650_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v___x_1658_);
lean_ctor_set(v_reuseFailAlloc_1673_, 1, v_k_1626_);
lean_ctor_set(v_reuseFailAlloc_1673_, 2, v_v_1627_);
lean_ctor_set(v_reuseFailAlloc_1673_, 3, v_r_1645_);
lean_ctor_set(v_reuseFailAlloc_1673_, 4, v_tree_1625_);
v___x_1660_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1667_; 
v_isSharedCheck_1667_ = !lean_is_exclusive(v_tree_1625_);
if (v_isSharedCheck_1667_ == 0)
{
lean_object* v_unused_1668_; lean_object* v_unused_1669_; lean_object* v_unused_1670_; lean_object* v_unused_1671_; lean_object* v_unused_1672_; 
v_unused_1668_ = lean_ctor_get(v_tree_1625_, 4);
lean_dec(v_unused_1668_);
v_unused_1669_ = lean_ctor_get(v_tree_1625_, 3);
lean_dec(v_unused_1669_);
v_unused_1670_ = lean_ctor_get(v_tree_1625_, 2);
lean_dec(v_unused_1670_);
v_unused_1671_ = lean_ctor_get(v_tree_1625_, 1);
lean_dec(v_unused_1671_);
v_unused_1672_ = lean_ctor_get(v_tree_1625_, 0);
lean_dec(v_unused_1672_);
v___x_1662_ = v_tree_1625_;
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
else
{
lean_dec(v_tree_1625_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1665_; 
if (v_isShared_1663_ == 0)
{
lean_ctor_set(v___x_1662_, 4, v___x_1660_);
lean_ctor_set(v___x_1662_, 3, v___y_1655_);
lean_ctor_set(v___x_1662_, 2, v_v_1643_);
lean_ctor_set(v___x_1662_, 1, v_k_1642_);
lean_ctor_set(v___x_1662_, 0, v___x_1653_);
v___x_1665_ = v___x_1662_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v___x_1653_);
lean_ctor_set(v_reuseFailAlloc_1666_, 1, v_k_1642_);
lean_ctor_set(v_reuseFailAlloc_1666_, 2, v_v_1643_);
lean_ctor_set(v_reuseFailAlloc_1666_, 3, v___y_1655_);
lean_ctor_set(v_reuseFailAlloc_1666_, 4, v___x_1660_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
}
}
v___jp_1675_:
{
lean_object* v___x_1677_; lean_object* v___x_1679_; 
v___x_1677_ = lean_nat_add(v___x_1674_, v___y_1676_);
lean_dec(v___y_1676_);
lean_dec(v___x_1674_);
if (v_isShared_1623_ == 0)
{
lean_ctor_set(v___x_1622_, 4, v_l_1644_);
lean_ctor_set(v___x_1622_, 3, v_l_1471_);
lean_ctor_set(v___x_1622_, 2, v_v_1470_);
lean_ctor_set(v___x_1622_, 1, v_k_1469_);
lean_ctor_set(v___x_1622_, 0, v___x_1677_);
v___x_1679_ = v___x_1622_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1683_; 
v_reuseFailAlloc_1683_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1683_, 0, v___x_1677_);
lean_ctor_set(v_reuseFailAlloc_1683_, 1, v_k_1469_);
lean_ctor_set(v_reuseFailAlloc_1683_, 2, v_v_1470_);
lean_ctor_set(v_reuseFailAlloc_1683_, 3, v_l_1471_);
lean_ctor_set(v_reuseFailAlloc_1683_, 4, v_l_1644_);
v___x_1679_ = v_reuseFailAlloc_1683_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
lean_object* v___x_1680_; 
v___x_1680_ = lean_nat_add(v___x_1478_, v_size_1628_);
if (lean_obj_tag(v_r_1645_) == 0)
{
lean_object* v_size_1681_; 
v_size_1681_ = lean_ctor_get(v_r_1645_, 0);
lean_inc(v_size_1681_);
v___y_1655_ = v___x_1679_;
v___y_1656_ = v___x_1680_;
v___y_1657_ = v_size_1681_;
goto v___jp_1654_;
}
else
{
lean_object* v___x_1682_; 
v___x_1682_ = lean_unsigned_to_nat(0u);
v___y_1655_ = v___x_1679_;
v___y_1656_ = v___x_1680_;
v___y_1657_ = v___x_1682_;
goto v___jp_1654_;
}
}
}
}
}
else
{
lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1697_; 
v___x_1692_ = lean_nat_add(v___x_1478_, v_size_1468_);
lean_dec(v_size_1468_);
v___x_1693_ = lean_nat_add(v___x_1692_, v_size_1628_);
lean_dec(v___x_1692_);
v___x_1694_ = lean_nat_add(v___x_1478_, v_size_1628_);
v___x_1695_ = lean_nat_add(v___x_1694_, v_size_1641_);
lean_dec(v___x_1694_);
if (v_isShared_1623_ == 0)
{
lean_ctor_set(v___x_1622_, 4, v_tree_1625_);
lean_ctor_set(v___x_1622_, 3, v_r_1472_);
lean_ctor_set(v___x_1622_, 2, v_v_1627_);
lean_ctor_set(v___x_1622_, 1, v_k_1626_);
lean_ctor_set(v___x_1622_, 0, v___x_1695_);
v___x_1697_ = v___x_1622_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v___x_1695_);
lean_ctor_set(v_reuseFailAlloc_1701_, 1, v_k_1626_);
lean_ctor_set(v_reuseFailAlloc_1701_, 2, v_v_1627_);
lean_ctor_set(v_reuseFailAlloc_1701_, 3, v_r_1472_);
lean_ctor_set(v_reuseFailAlloc_1701_, 4, v_tree_1625_);
v___x_1697_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
lean_object* v___x_1699_; 
if (v_isShared_1639_ == 0)
{
lean_ctor_set(v___x_1638_, 4, v___x_1697_);
lean_ctor_set(v___x_1638_, 0, v___x_1693_);
v___x_1699_ = v___x_1638_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v___x_1693_);
lean_ctor_set(v_reuseFailAlloc_1700_, 1, v_k_1469_);
lean_ctor_set(v_reuseFailAlloc_1700_, 2, v_v_1470_);
lean_ctor_set(v_reuseFailAlloc_1700_, 3, v_l_1471_);
lean_ctor_set(v_reuseFailAlloc_1700_, 4, v___x_1697_);
v___x_1699_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
return v___x_1699_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_1471_) == 0)
{
lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1731_; 
lean_inc_ref(v_l_1471_);
lean_inc(v_v_1470_);
lean_inc(v_k_1469_);
lean_inc(v_size_1468_);
v_isSharedCheck_1731_ = !lean_is_exclusive(v_l_1288_);
if (v_isSharedCheck_1731_ == 0)
{
lean_object* v_unused_1732_; lean_object* v_unused_1733_; lean_object* v_unused_1734_; lean_object* v_unused_1735_; lean_object* v_unused_1736_; 
v_unused_1732_ = lean_ctor_get(v_l_1288_, 4);
lean_dec(v_unused_1732_);
v_unused_1733_ = lean_ctor_get(v_l_1288_, 3);
lean_dec(v_unused_1733_);
v_unused_1734_ = lean_ctor_get(v_l_1288_, 2);
lean_dec(v_unused_1734_);
v_unused_1735_ = lean_ctor_get(v_l_1288_, 1);
lean_dec(v_unused_1735_);
v_unused_1736_ = lean_ctor_get(v_l_1288_, 0);
lean_dec(v_unused_1736_);
v___x_1709_ = v_l_1288_;
v_isShared_1710_ = v_isSharedCheck_1731_;
goto v_resetjp_1708_;
}
else
{
lean_dec(v_l_1288_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1731_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
if (lean_obj_tag(v_r_1472_) == 0)
{
lean_object* v_k_1711_; lean_object* v_v_1712_; lean_object* v_size_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1717_; 
v_k_1711_ = lean_ctor_get(v___x_1624_, 0);
lean_inc(v_k_1711_);
v_v_1712_ = lean_ctor_get(v___x_1624_, 1);
lean_inc(v_v_1712_);
lean_dec_ref(v___x_1624_);
v_size_1713_ = lean_ctor_get(v_r_1472_, 0);
v___x_1714_ = lean_nat_add(v___x_1478_, v_size_1468_);
lean_dec(v_size_1468_);
v___x_1715_ = lean_nat_add(v___x_1478_, v_size_1713_);
if (v_isShared_1623_ == 0)
{
lean_ctor_set(v___x_1622_, 4, v_tree_1625_);
lean_ctor_set(v___x_1622_, 3, v_r_1472_);
lean_ctor_set(v___x_1622_, 2, v_v_1712_);
lean_ctor_set(v___x_1622_, 1, v_k_1711_);
lean_ctor_set(v___x_1622_, 0, v___x_1715_);
v___x_1717_ = v___x_1622_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v___x_1715_);
lean_ctor_set(v_reuseFailAlloc_1721_, 1, v_k_1711_);
lean_ctor_set(v_reuseFailAlloc_1721_, 2, v_v_1712_);
lean_ctor_set(v_reuseFailAlloc_1721_, 3, v_r_1472_);
lean_ctor_set(v_reuseFailAlloc_1721_, 4, v_tree_1625_);
v___x_1717_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
lean_object* v___x_1719_; 
if (v_isShared_1710_ == 0)
{
lean_ctor_set(v___x_1709_, 4, v___x_1717_);
lean_ctor_set(v___x_1709_, 0, v___x_1714_);
v___x_1719_ = v___x_1709_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v___x_1714_);
lean_ctor_set(v_reuseFailAlloc_1720_, 1, v_k_1469_);
lean_ctor_set(v_reuseFailAlloc_1720_, 2, v_v_1470_);
lean_ctor_set(v_reuseFailAlloc_1720_, 3, v_l_1471_);
lean_ctor_set(v_reuseFailAlloc_1720_, 4, v___x_1717_);
v___x_1719_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
return v___x_1719_;
}
}
}
else
{
lean_object* v_k_1722_; lean_object* v_v_1723_; lean_object* v___x_1724_; lean_object* v___x_1726_; 
lean_dec(v_size_1468_);
v_k_1722_ = lean_ctor_get(v___x_1624_, 0);
lean_inc(v_k_1722_);
v_v_1723_ = lean_ctor_get(v___x_1624_, 1);
lean_inc(v_v_1723_);
lean_dec_ref(v___x_1624_);
v___x_1724_ = lean_unsigned_to_nat(3u);
if (v_isShared_1623_ == 0)
{
lean_ctor_set(v___x_1622_, 4, v_r_1472_);
lean_ctor_set(v___x_1622_, 3, v_r_1472_);
lean_ctor_set(v___x_1622_, 2, v_v_1723_);
lean_ctor_set(v___x_1622_, 1, v_k_1722_);
lean_ctor_set(v___x_1622_, 0, v___x_1478_);
v___x_1726_ = v___x_1622_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v___x_1478_);
lean_ctor_set(v_reuseFailAlloc_1730_, 1, v_k_1722_);
lean_ctor_set(v_reuseFailAlloc_1730_, 2, v_v_1723_);
lean_ctor_set(v_reuseFailAlloc_1730_, 3, v_r_1472_);
lean_ctor_set(v_reuseFailAlloc_1730_, 4, v_r_1472_);
v___x_1726_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
lean_object* v___x_1728_; 
if (v_isShared_1710_ == 0)
{
lean_ctor_set(v___x_1709_, 4, v___x_1726_);
lean_ctor_set(v___x_1709_, 0, v___x_1724_);
v___x_1728_ = v___x_1709_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v___x_1724_);
lean_ctor_set(v_reuseFailAlloc_1729_, 1, v_k_1469_);
lean_ctor_set(v_reuseFailAlloc_1729_, 2, v_v_1470_);
lean_ctor_set(v_reuseFailAlloc_1729_, 3, v_l_1471_);
lean_ctor_set(v_reuseFailAlloc_1729_, 4, v___x_1726_);
v___x_1728_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
return v___x_1728_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1472_) == 0)
{
lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1761_; 
lean_inc(v_l_1471_);
lean_inc(v_v_1470_);
lean_inc(v_k_1469_);
v_isSharedCheck_1761_ = !lean_is_exclusive(v_l_1288_);
if (v_isSharedCheck_1761_ == 0)
{
lean_object* v_unused_1762_; lean_object* v_unused_1763_; lean_object* v_unused_1764_; lean_object* v_unused_1765_; lean_object* v_unused_1766_; 
v_unused_1762_ = lean_ctor_get(v_l_1288_, 4);
lean_dec(v_unused_1762_);
v_unused_1763_ = lean_ctor_get(v_l_1288_, 3);
lean_dec(v_unused_1763_);
v_unused_1764_ = lean_ctor_get(v_l_1288_, 2);
lean_dec(v_unused_1764_);
v_unused_1765_ = lean_ctor_get(v_l_1288_, 1);
lean_dec(v_unused_1765_);
v_unused_1766_ = lean_ctor_get(v_l_1288_, 0);
lean_dec(v_unused_1766_);
v___x_1738_ = v_l_1288_;
v_isShared_1739_ = v_isSharedCheck_1761_;
goto v_resetjp_1737_;
}
else
{
lean_dec(v_l_1288_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1761_;
goto v_resetjp_1737_;
}
v_resetjp_1737_:
{
lean_object* v_k_1740_; lean_object* v_v_1741_; lean_object* v_k_1742_; lean_object* v_v_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1757_; 
v_k_1740_ = lean_ctor_get(v___x_1624_, 0);
lean_inc(v_k_1740_);
v_v_1741_ = lean_ctor_get(v___x_1624_, 1);
lean_inc(v_v_1741_);
lean_dec_ref(v___x_1624_);
v_k_1742_ = lean_ctor_get(v_r_1472_, 1);
v_v_1743_ = lean_ctor_get(v_r_1472_, 2);
v_isSharedCheck_1757_ = !lean_is_exclusive(v_r_1472_);
if (v_isSharedCheck_1757_ == 0)
{
lean_object* v_unused_1758_; lean_object* v_unused_1759_; lean_object* v_unused_1760_; 
v_unused_1758_ = lean_ctor_get(v_r_1472_, 4);
lean_dec(v_unused_1758_);
v_unused_1759_ = lean_ctor_get(v_r_1472_, 3);
lean_dec(v_unused_1759_);
v_unused_1760_ = lean_ctor_get(v_r_1472_, 0);
lean_dec(v_unused_1760_);
v___x_1745_ = v_r_1472_;
v_isShared_1746_ = v_isSharedCheck_1757_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_v_1743_);
lean_inc(v_k_1742_);
lean_dec(v_r_1472_);
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
lean_ctor_set(v___x_1745_, 4, v_l_1471_);
lean_ctor_set(v___x_1745_, 3, v_l_1471_);
lean_ctor_set(v___x_1745_, 2, v_v_1470_);
lean_ctor_set(v___x_1745_, 1, v_k_1469_);
lean_ctor_set(v___x_1745_, 0, v___x_1478_);
v___x_1749_ = v___x_1745_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v___x_1478_);
lean_ctor_set(v_reuseFailAlloc_1756_, 1, v_k_1469_);
lean_ctor_set(v_reuseFailAlloc_1756_, 2, v_v_1470_);
lean_ctor_set(v_reuseFailAlloc_1756_, 3, v_l_1471_);
lean_ctor_set(v_reuseFailAlloc_1756_, 4, v_l_1471_);
v___x_1749_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
lean_object* v___x_1751_; 
if (v_isShared_1623_ == 0)
{
lean_ctor_set(v___x_1622_, 4, v_l_1471_);
lean_ctor_set(v___x_1622_, 3, v_l_1471_);
lean_ctor_set(v___x_1622_, 2, v_v_1741_);
lean_ctor_set(v___x_1622_, 1, v_k_1740_);
lean_ctor_set(v___x_1622_, 0, v___x_1478_);
v___x_1751_ = v___x_1622_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v___x_1478_);
lean_ctor_set(v_reuseFailAlloc_1755_, 1, v_k_1740_);
lean_ctor_set(v_reuseFailAlloc_1755_, 2, v_v_1741_);
lean_ctor_set(v_reuseFailAlloc_1755_, 3, v_l_1471_);
lean_ctor_set(v_reuseFailAlloc_1755_, 4, v_l_1471_);
v___x_1751_ = v_reuseFailAlloc_1755_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
lean_object* v___x_1753_; 
if (v_isShared_1739_ == 0)
{
lean_ctor_set(v___x_1738_, 4, v___x_1751_);
lean_ctor_set(v___x_1738_, 3, v___x_1749_);
lean_ctor_set(v___x_1738_, 2, v_v_1743_);
lean_ctor_set(v___x_1738_, 1, v_k_1742_);
lean_ctor_set(v___x_1738_, 0, v___x_1747_);
v___x_1753_ = v___x_1738_;
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
lean_object* v_k_1767_; lean_object* v_v_1768_; lean_object* v___x_1769_; lean_object* v___x_1771_; 
v_k_1767_ = lean_ctor_get(v___x_1624_, 0);
lean_inc(v_k_1767_);
v_v_1768_ = lean_ctor_get(v___x_1624_, 1);
lean_inc(v_v_1768_);
lean_dec_ref(v___x_1624_);
v___x_1769_ = lean_unsigned_to_nat(2u);
if (v_isShared_1623_ == 0)
{
lean_ctor_set(v___x_1622_, 4, v_r_1472_);
lean_ctor_set(v___x_1622_, 3, v_l_1288_);
lean_ctor_set(v___x_1622_, 2, v_v_1768_);
lean_ctor_set(v___x_1622_, 1, v_k_1767_);
lean_ctor_set(v___x_1622_, 0, v___x_1769_);
v___x_1771_ = v___x_1622_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v___x_1769_);
lean_ctor_set(v_reuseFailAlloc_1772_, 1, v_k_1767_);
lean_ctor_set(v_reuseFailAlloc_1772_, 2, v_v_1768_);
lean_ctor_set(v_reuseFailAlloc_1772_, 3, v_l_1288_);
lean_ctor_set(v_reuseFailAlloc_1772_, 4, v_r_1472_);
v___x_1771_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
return v___x_1771_;
}
}
}
}
}
}
}
else
{
return v_l_1288_;
}
}
else
{
return v_r_1289_;
}
}
default: 
{
lean_object* v_impl_1779_; lean_object* v___x_1780_; 
v_impl_1779_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_k_1284_, v_r_1289_);
v___x_1780_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1779_) == 0)
{
if (lean_obj_tag(v_l_1288_) == 0)
{
lean_object* v_size_1781_; lean_object* v_size_1782_; lean_object* v_k_1783_; lean_object* v_v_1784_; lean_object* v_l_1785_; lean_object* v_r_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; uint8_t v___x_1789_; 
v_size_1781_ = lean_ctor_get(v_impl_1779_, 0);
lean_inc(v_size_1781_);
v_size_1782_ = lean_ctor_get(v_l_1288_, 0);
v_k_1783_ = lean_ctor_get(v_l_1288_, 1);
v_v_1784_ = lean_ctor_get(v_l_1288_, 2);
v_l_1785_ = lean_ctor_get(v_l_1288_, 3);
v_r_1786_ = lean_ctor_get(v_l_1288_, 4);
lean_inc(v_r_1786_);
v___x_1787_ = lean_unsigned_to_nat(3u);
v___x_1788_ = lean_nat_mul(v___x_1787_, v_size_1781_);
v___x_1789_ = lean_nat_dec_lt(v___x_1788_, v_size_1782_);
lean_dec(v___x_1788_);
if (v___x_1789_ == 0)
{
lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1793_; 
lean_dec(v_r_1786_);
v___x_1790_ = lean_nat_add(v___x_1780_, v_size_1782_);
v___x_1791_ = lean_nat_add(v___x_1790_, v_size_1781_);
lean_dec(v_size_1781_);
lean_dec(v___x_1790_);
if (v_isShared_1292_ == 0)
{
lean_ctor_set(v___x_1291_, 4, v_impl_1779_);
lean_ctor_set(v___x_1291_, 0, v___x_1791_);
v___x_1793_ = v___x_1291_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v___x_1791_);
lean_ctor_set(v_reuseFailAlloc_1794_, 1, v_k_1286_);
lean_ctor_set(v_reuseFailAlloc_1794_, 2, v_v_1287_);
lean_ctor_set(v_reuseFailAlloc_1794_, 3, v_l_1288_);
lean_ctor_set(v_reuseFailAlloc_1794_, 4, v_impl_1779_);
v___x_1793_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
return v___x_1793_;
}
}
else
{
lean_object* v___x_1796_; uint8_t v_isShared_1797_; uint8_t v_isSharedCheck_1860_; 
lean_inc(v_l_1785_);
lean_inc(v_v_1784_);
lean_inc(v_k_1783_);
lean_inc(v_size_1782_);
v_isSharedCheck_1860_ = !lean_is_exclusive(v_l_1288_);
if (v_isSharedCheck_1860_ == 0)
{
lean_object* v_unused_1861_; lean_object* v_unused_1862_; lean_object* v_unused_1863_; lean_object* v_unused_1864_; lean_object* v_unused_1865_; 
v_unused_1861_ = lean_ctor_get(v_l_1288_, 4);
lean_dec(v_unused_1861_);
v_unused_1862_ = lean_ctor_get(v_l_1288_, 3);
lean_dec(v_unused_1862_);
v_unused_1863_ = lean_ctor_get(v_l_1288_, 2);
lean_dec(v_unused_1863_);
v_unused_1864_ = lean_ctor_get(v_l_1288_, 1);
lean_dec(v_unused_1864_);
v_unused_1865_ = lean_ctor_get(v_l_1288_, 0);
lean_dec(v_unused_1865_);
v___x_1796_ = v_l_1288_;
v_isShared_1797_ = v_isSharedCheck_1860_;
goto v_resetjp_1795_;
}
else
{
lean_dec(v_l_1288_);
v___x_1796_ = lean_box(0);
v_isShared_1797_ = v_isSharedCheck_1860_;
goto v_resetjp_1795_;
}
v_resetjp_1795_:
{
lean_object* v_size_1798_; lean_object* v_size_1799_; lean_object* v_k_1800_; lean_object* v_v_1801_; lean_object* v_l_1802_; lean_object* v_r_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; uint8_t v___x_1806_; 
v_size_1798_ = lean_ctor_get(v_l_1785_, 0);
v_size_1799_ = lean_ctor_get(v_r_1786_, 0);
v_k_1800_ = lean_ctor_get(v_r_1786_, 1);
v_v_1801_ = lean_ctor_get(v_r_1786_, 2);
v_l_1802_ = lean_ctor_get(v_r_1786_, 3);
v_r_1803_ = lean_ctor_get(v_r_1786_, 4);
v___x_1804_ = lean_unsigned_to_nat(2u);
v___x_1805_ = lean_nat_mul(v___x_1804_, v_size_1798_);
v___x_1806_ = lean_nat_dec_lt(v_size_1799_, v___x_1805_);
lean_dec(v___x_1805_);
if (v___x_1806_ == 0)
{
lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1835_; 
lean_inc(v_r_1803_);
lean_inc(v_l_1802_);
lean_inc(v_v_1801_);
lean_inc(v_k_1800_);
v_isSharedCheck_1835_ = !lean_is_exclusive(v_r_1786_);
if (v_isSharedCheck_1835_ == 0)
{
lean_object* v_unused_1836_; lean_object* v_unused_1837_; lean_object* v_unused_1838_; lean_object* v_unused_1839_; lean_object* v_unused_1840_; 
v_unused_1836_ = lean_ctor_get(v_r_1786_, 4);
lean_dec(v_unused_1836_);
v_unused_1837_ = lean_ctor_get(v_r_1786_, 3);
lean_dec(v_unused_1837_);
v_unused_1838_ = lean_ctor_get(v_r_1786_, 2);
lean_dec(v_unused_1838_);
v_unused_1839_ = lean_ctor_get(v_r_1786_, 1);
lean_dec(v_unused_1839_);
v_unused_1840_ = lean_ctor_get(v_r_1786_, 0);
lean_dec(v_unused_1840_);
v___x_1808_ = v_r_1786_;
v_isShared_1809_ = v_isSharedCheck_1835_;
goto v_resetjp_1807_;
}
else
{
lean_dec(v_r_1786_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1835_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___y_1813_; lean_object* v___y_1814_; lean_object* v___y_1815_; lean_object* v___x_1823_; lean_object* v___y_1825_; 
v___x_1810_ = lean_nat_add(v___x_1780_, v_size_1782_);
lean_dec(v_size_1782_);
v___x_1811_ = lean_nat_add(v___x_1810_, v_size_1781_);
lean_dec(v___x_1810_);
v___x_1823_ = lean_nat_add(v___x_1780_, v_size_1798_);
if (lean_obj_tag(v_l_1802_) == 0)
{
lean_object* v_size_1833_; 
v_size_1833_ = lean_ctor_get(v_l_1802_, 0);
lean_inc(v_size_1833_);
v___y_1825_ = v_size_1833_;
goto v___jp_1824_;
}
else
{
lean_object* v___x_1834_; 
v___x_1834_ = lean_unsigned_to_nat(0u);
v___y_1825_ = v___x_1834_;
goto v___jp_1824_;
}
v___jp_1812_:
{
lean_object* v___x_1816_; lean_object* v___x_1818_; 
v___x_1816_ = lean_nat_add(v___y_1813_, v___y_1815_);
lean_dec(v___y_1815_);
lean_dec(v___y_1813_);
if (v_isShared_1809_ == 0)
{
lean_ctor_set(v___x_1808_, 4, v_impl_1779_);
lean_ctor_set(v___x_1808_, 3, v_r_1803_);
lean_ctor_set(v___x_1808_, 2, v_v_1287_);
lean_ctor_set(v___x_1808_, 1, v_k_1286_);
lean_ctor_set(v___x_1808_, 0, v___x_1816_);
v___x_1818_ = v___x_1808_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v___x_1816_);
lean_ctor_set(v_reuseFailAlloc_1822_, 1, v_k_1286_);
lean_ctor_set(v_reuseFailAlloc_1822_, 2, v_v_1287_);
lean_ctor_set(v_reuseFailAlloc_1822_, 3, v_r_1803_);
lean_ctor_set(v_reuseFailAlloc_1822_, 4, v_impl_1779_);
v___x_1818_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
lean_object* v___x_1820_; 
if (v_isShared_1797_ == 0)
{
lean_ctor_set(v___x_1796_, 4, v___x_1818_);
lean_ctor_set(v___x_1796_, 3, v___y_1814_);
lean_ctor_set(v___x_1796_, 2, v_v_1801_);
lean_ctor_set(v___x_1796_, 1, v_k_1800_);
lean_ctor_set(v___x_1796_, 0, v___x_1811_);
v___x_1820_ = v___x_1796_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v___x_1811_);
lean_ctor_set(v_reuseFailAlloc_1821_, 1, v_k_1800_);
lean_ctor_set(v_reuseFailAlloc_1821_, 2, v_v_1801_);
lean_ctor_set(v_reuseFailAlloc_1821_, 3, v___y_1814_);
lean_ctor_set(v_reuseFailAlloc_1821_, 4, v___x_1818_);
v___x_1820_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
return v___x_1820_;
}
}
}
v___jp_1824_:
{
lean_object* v___x_1826_; lean_object* v___x_1828_; 
v___x_1826_ = lean_nat_add(v___x_1823_, v___y_1825_);
lean_dec(v___y_1825_);
lean_dec(v___x_1823_);
if (v_isShared_1292_ == 0)
{
lean_ctor_set(v___x_1291_, 4, v_l_1802_);
lean_ctor_set(v___x_1291_, 3, v_l_1785_);
lean_ctor_set(v___x_1291_, 2, v_v_1784_);
lean_ctor_set(v___x_1291_, 1, v_k_1783_);
lean_ctor_set(v___x_1291_, 0, v___x_1826_);
v___x_1828_ = v___x_1291_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v___x_1826_);
lean_ctor_set(v_reuseFailAlloc_1832_, 1, v_k_1783_);
lean_ctor_set(v_reuseFailAlloc_1832_, 2, v_v_1784_);
lean_ctor_set(v_reuseFailAlloc_1832_, 3, v_l_1785_);
lean_ctor_set(v_reuseFailAlloc_1832_, 4, v_l_1802_);
v___x_1828_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
lean_object* v___x_1829_; 
v___x_1829_ = lean_nat_add(v___x_1780_, v_size_1781_);
lean_dec(v_size_1781_);
if (lean_obj_tag(v_r_1803_) == 0)
{
lean_object* v_size_1830_; 
v_size_1830_ = lean_ctor_get(v_r_1803_, 0);
lean_inc(v_size_1830_);
v___y_1813_ = v___x_1829_;
v___y_1814_ = v___x_1828_;
v___y_1815_ = v_size_1830_;
goto v___jp_1812_;
}
else
{
lean_object* v___x_1831_; 
v___x_1831_ = lean_unsigned_to_nat(0u);
v___y_1813_ = v___x_1829_;
v___y_1814_ = v___x_1828_;
v___y_1815_ = v___x_1831_;
goto v___jp_1812_;
}
}
}
}
}
else
{
lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1846_; 
lean_del_object(v___x_1291_);
v___x_1841_ = lean_nat_add(v___x_1780_, v_size_1782_);
lean_dec(v_size_1782_);
v___x_1842_ = lean_nat_add(v___x_1841_, v_size_1781_);
lean_dec(v___x_1841_);
v___x_1843_ = lean_nat_add(v___x_1780_, v_size_1781_);
lean_dec(v_size_1781_);
v___x_1844_ = lean_nat_add(v___x_1843_, v_size_1799_);
lean_dec(v___x_1843_);
lean_inc_ref(v_impl_1779_);
if (v_isShared_1797_ == 0)
{
lean_ctor_set(v___x_1796_, 4, v_impl_1779_);
lean_ctor_set(v___x_1796_, 3, v_r_1786_);
lean_ctor_set(v___x_1796_, 2, v_v_1287_);
lean_ctor_set(v___x_1796_, 1, v_k_1286_);
lean_ctor_set(v___x_1796_, 0, v___x_1844_);
v___x_1846_ = v___x_1796_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v___x_1844_);
lean_ctor_set(v_reuseFailAlloc_1859_, 1, v_k_1286_);
lean_ctor_set(v_reuseFailAlloc_1859_, 2, v_v_1287_);
lean_ctor_set(v_reuseFailAlloc_1859_, 3, v_r_1786_);
lean_ctor_set(v_reuseFailAlloc_1859_, 4, v_impl_1779_);
v___x_1846_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1853_; 
v_isSharedCheck_1853_ = !lean_is_exclusive(v_impl_1779_);
if (v_isSharedCheck_1853_ == 0)
{
lean_object* v_unused_1854_; lean_object* v_unused_1855_; lean_object* v_unused_1856_; lean_object* v_unused_1857_; lean_object* v_unused_1858_; 
v_unused_1854_ = lean_ctor_get(v_impl_1779_, 4);
lean_dec(v_unused_1854_);
v_unused_1855_ = lean_ctor_get(v_impl_1779_, 3);
lean_dec(v_unused_1855_);
v_unused_1856_ = lean_ctor_get(v_impl_1779_, 2);
lean_dec(v_unused_1856_);
v_unused_1857_ = lean_ctor_get(v_impl_1779_, 1);
lean_dec(v_unused_1857_);
v_unused_1858_ = lean_ctor_get(v_impl_1779_, 0);
lean_dec(v_unused_1858_);
v___x_1848_ = v_impl_1779_;
v_isShared_1849_ = v_isSharedCheck_1853_;
goto v_resetjp_1847_;
}
else
{
lean_dec(v_impl_1779_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1853_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v___x_1851_; 
if (v_isShared_1849_ == 0)
{
lean_ctor_set(v___x_1848_, 4, v___x_1846_);
lean_ctor_set(v___x_1848_, 3, v_l_1785_);
lean_ctor_set(v___x_1848_, 2, v_v_1784_);
lean_ctor_set(v___x_1848_, 1, v_k_1783_);
lean_ctor_set(v___x_1848_, 0, v___x_1842_);
v___x_1851_ = v___x_1848_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v___x_1842_);
lean_ctor_set(v_reuseFailAlloc_1852_, 1, v_k_1783_);
lean_ctor_set(v_reuseFailAlloc_1852_, 2, v_v_1784_);
lean_ctor_set(v_reuseFailAlloc_1852_, 3, v_l_1785_);
lean_ctor_set(v_reuseFailAlloc_1852_, 4, v___x_1846_);
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
}
}
}
else
{
lean_object* v_size_1866_; lean_object* v___x_1867_; lean_object* v___x_1869_; 
v_size_1866_ = lean_ctor_get(v_impl_1779_, 0);
lean_inc(v_size_1866_);
v___x_1867_ = lean_nat_add(v___x_1780_, v_size_1866_);
lean_dec(v_size_1866_);
if (v_isShared_1292_ == 0)
{
lean_ctor_set(v___x_1291_, 4, v_impl_1779_);
lean_ctor_set(v___x_1291_, 0, v___x_1867_);
v___x_1869_ = v___x_1291_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v___x_1867_);
lean_ctor_set(v_reuseFailAlloc_1870_, 1, v_k_1286_);
lean_ctor_set(v_reuseFailAlloc_1870_, 2, v_v_1287_);
lean_ctor_set(v_reuseFailAlloc_1870_, 3, v_l_1288_);
lean_ctor_set(v_reuseFailAlloc_1870_, 4, v_impl_1779_);
v___x_1869_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
return v___x_1869_;
}
}
}
else
{
if (lean_obj_tag(v_l_1288_) == 0)
{
lean_object* v_l_1871_; 
v_l_1871_ = lean_ctor_get(v_l_1288_, 3);
if (lean_obj_tag(v_l_1871_) == 0)
{
lean_object* v_r_1872_; 
lean_inc_ref(v_l_1871_);
v_r_1872_ = lean_ctor_get(v_l_1288_, 4);
lean_inc(v_r_1872_);
if (lean_obj_tag(v_r_1872_) == 0)
{
lean_object* v_size_1873_; lean_object* v_k_1874_; lean_object* v_v_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1888_; 
v_size_1873_ = lean_ctor_get(v_l_1288_, 0);
v_k_1874_ = lean_ctor_get(v_l_1288_, 1);
v_v_1875_ = lean_ctor_get(v_l_1288_, 2);
v_isSharedCheck_1888_ = !lean_is_exclusive(v_l_1288_);
if (v_isSharedCheck_1888_ == 0)
{
lean_object* v_unused_1889_; lean_object* v_unused_1890_; 
v_unused_1889_ = lean_ctor_get(v_l_1288_, 4);
lean_dec(v_unused_1889_);
v_unused_1890_ = lean_ctor_get(v_l_1288_, 3);
lean_dec(v_unused_1890_);
v___x_1877_ = v_l_1288_;
v_isShared_1878_ = v_isSharedCheck_1888_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_v_1875_);
lean_inc(v_k_1874_);
lean_inc(v_size_1873_);
lean_dec(v_l_1288_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1888_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v_size_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1883_; 
v_size_1879_ = lean_ctor_get(v_r_1872_, 0);
v___x_1880_ = lean_nat_add(v___x_1780_, v_size_1873_);
lean_dec(v_size_1873_);
v___x_1881_ = lean_nat_add(v___x_1780_, v_size_1879_);
if (v_isShared_1878_ == 0)
{
lean_ctor_set(v___x_1877_, 4, v_impl_1779_);
lean_ctor_set(v___x_1877_, 3, v_r_1872_);
lean_ctor_set(v___x_1877_, 2, v_v_1287_);
lean_ctor_set(v___x_1877_, 1, v_k_1286_);
lean_ctor_set(v___x_1877_, 0, v___x_1881_);
v___x_1883_ = v___x_1877_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v___x_1881_);
lean_ctor_set(v_reuseFailAlloc_1887_, 1, v_k_1286_);
lean_ctor_set(v_reuseFailAlloc_1887_, 2, v_v_1287_);
lean_ctor_set(v_reuseFailAlloc_1887_, 3, v_r_1872_);
lean_ctor_set(v_reuseFailAlloc_1887_, 4, v_impl_1779_);
v___x_1883_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
lean_object* v___x_1885_; 
if (v_isShared_1292_ == 0)
{
lean_ctor_set(v___x_1291_, 4, v___x_1883_);
lean_ctor_set(v___x_1291_, 3, v_l_1871_);
lean_ctor_set(v___x_1291_, 2, v_v_1875_);
lean_ctor_set(v___x_1291_, 1, v_k_1874_);
lean_ctor_set(v___x_1291_, 0, v___x_1880_);
v___x_1885_ = v___x_1291_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v___x_1880_);
lean_ctor_set(v_reuseFailAlloc_1886_, 1, v_k_1874_);
lean_ctor_set(v_reuseFailAlloc_1886_, 2, v_v_1875_);
lean_ctor_set(v_reuseFailAlloc_1886_, 3, v_l_1871_);
lean_ctor_set(v_reuseFailAlloc_1886_, 4, v___x_1883_);
v___x_1885_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
return v___x_1885_;
}
}
}
}
else
{
lean_object* v_k_1891_; lean_object* v_v_1892_; lean_object* v___x_1894_; uint8_t v_isShared_1895_; uint8_t v_isSharedCheck_1903_; 
v_k_1891_ = lean_ctor_get(v_l_1288_, 1);
v_v_1892_ = lean_ctor_get(v_l_1288_, 2);
v_isSharedCheck_1903_ = !lean_is_exclusive(v_l_1288_);
if (v_isSharedCheck_1903_ == 0)
{
lean_object* v_unused_1904_; lean_object* v_unused_1905_; lean_object* v_unused_1906_; 
v_unused_1904_ = lean_ctor_get(v_l_1288_, 4);
lean_dec(v_unused_1904_);
v_unused_1905_ = lean_ctor_get(v_l_1288_, 3);
lean_dec(v_unused_1905_);
v_unused_1906_ = lean_ctor_get(v_l_1288_, 0);
lean_dec(v_unused_1906_);
v___x_1894_ = v_l_1288_;
v_isShared_1895_ = v_isSharedCheck_1903_;
goto v_resetjp_1893_;
}
else
{
lean_inc(v_v_1892_);
lean_inc(v_k_1891_);
lean_dec(v_l_1288_);
v___x_1894_ = lean_box(0);
v_isShared_1895_ = v_isSharedCheck_1903_;
goto v_resetjp_1893_;
}
v_resetjp_1893_:
{
lean_object* v___x_1896_; lean_object* v___x_1898_; 
v___x_1896_ = lean_unsigned_to_nat(3u);
if (v_isShared_1895_ == 0)
{
lean_ctor_set(v___x_1894_, 3, v_r_1872_);
lean_ctor_set(v___x_1894_, 2, v_v_1287_);
lean_ctor_set(v___x_1894_, 1, v_k_1286_);
lean_ctor_set(v___x_1894_, 0, v___x_1780_);
v___x_1898_ = v___x_1894_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v___x_1780_);
lean_ctor_set(v_reuseFailAlloc_1902_, 1, v_k_1286_);
lean_ctor_set(v_reuseFailAlloc_1902_, 2, v_v_1287_);
lean_ctor_set(v_reuseFailAlloc_1902_, 3, v_r_1872_);
lean_ctor_set(v_reuseFailAlloc_1902_, 4, v_r_1872_);
v___x_1898_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
lean_object* v___x_1900_; 
if (v_isShared_1292_ == 0)
{
lean_ctor_set(v___x_1291_, 4, v___x_1898_);
lean_ctor_set(v___x_1291_, 3, v_l_1871_);
lean_ctor_set(v___x_1291_, 2, v_v_1892_);
lean_ctor_set(v___x_1291_, 1, v_k_1891_);
lean_ctor_set(v___x_1291_, 0, v___x_1896_);
v___x_1900_ = v___x_1291_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v___x_1896_);
lean_ctor_set(v_reuseFailAlloc_1901_, 1, v_k_1891_);
lean_ctor_set(v_reuseFailAlloc_1901_, 2, v_v_1892_);
lean_ctor_set(v_reuseFailAlloc_1901_, 3, v_l_1871_);
lean_ctor_set(v_reuseFailAlloc_1901_, 4, v___x_1898_);
v___x_1900_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
return v___x_1900_;
}
}
}
}
}
else
{
lean_object* v_r_1907_; 
v_r_1907_ = lean_ctor_get(v_l_1288_, 4);
lean_inc(v_r_1907_);
if (lean_obj_tag(v_r_1907_) == 0)
{
lean_object* v_k_1908_; lean_object* v_v_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1932_; 
lean_inc(v_l_1871_);
v_k_1908_ = lean_ctor_get(v_l_1288_, 1);
v_v_1909_ = lean_ctor_get(v_l_1288_, 2);
v_isSharedCheck_1932_ = !lean_is_exclusive(v_l_1288_);
if (v_isSharedCheck_1932_ == 0)
{
lean_object* v_unused_1933_; lean_object* v_unused_1934_; lean_object* v_unused_1935_; 
v_unused_1933_ = lean_ctor_get(v_l_1288_, 4);
lean_dec(v_unused_1933_);
v_unused_1934_ = lean_ctor_get(v_l_1288_, 3);
lean_dec(v_unused_1934_);
v_unused_1935_ = lean_ctor_get(v_l_1288_, 0);
lean_dec(v_unused_1935_);
v___x_1911_ = v_l_1288_;
v_isShared_1912_ = v_isSharedCheck_1932_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_v_1909_);
lean_inc(v_k_1908_);
lean_dec(v_l_1288_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1932_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
lean_object* v_k_1913_; lean_object* v_v_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1928_; 
v_k_1913_ = lean_ctor_get(v_r_1907_, 1);
v_v_1914_ = lean_ctor_get(v_r_1907_, 2);
v_isSharedCheck_1928_ = !lean_is_exclusive(v_r_1907_);
if (v_isSharedCheck_1928_ == 0)
{
lean_object* v_unused_1929_; lean_object* v_unused_1930_; lean_object* v_unused_1931_; 
v_unused_1929_ = lean_ctor_get(v_r_1907_, 4);
lean_dec(v_unused_1929_);
v_unused_1930_ = lean_ctor_get(v_r_1907_, 3);
lean_dec(v_unused_1930_);
v_unused_1931_ = lean_ctor_get(v_r_1907_, 0);
lean_dec(v_unused_1931_);
v___x_1916_ = v_r_1907_;
v_isShared_1917_ = v_isSharedCheck_1928_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_v_1914_);
lean_inc(v_k_1913_);
lean_dec(v_r_1907_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1928_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v___x_1918_; lean_object* v___x_1920_; 
v___x_1918_ = lean_unsigned_to_nat(3u);
if (v_isShared_1917_ == 0)
{
lean_ctor_set(v___x_1916_, 4, v_l_1871_);
lean_ctor_set(v___x_1916_, 3, v_l_1871_);
lean_ctor_set(v___x_1916_, 2, v_v_1909_);
lean_ctor_set(v___x_1916_, 1, v_k_1908_);
lean_ctor_set(v___x_1916_, 0, v___x_1780_);
v___x_1920_ = v___x_1916_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v___x_1780_);
lean_ctor_set(v_reuseFailAlloc_1927_, 1, v_k_1908_);
lean_ctor_set(v_reuseFailAlloc_1927_, 2, v_v_1909_);
lean_ctor_set(v_reuseFailAlloc_1927_, 3, v_l_1871_);
lean_ctor_set(v_reuseFailAlloc_1927_, 4, v_l_1871_);
v___x_1920_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
lean_object* v___x_1922_; 
if (v_isShared_1912_ == 0)
{
lean_ctor_set(v___x_1911_, 4, v_l_1871_);
lean_ctor_set(v___x_1911_, 2, v_v_1287_);
lean_ctor_set(v___x_1911_, 1, v_k_1286_);
lean_ctor_set(v___x_1911_, 0, v___x_1780_);
v___x_1922_ = v___x_1911_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v___x_1780_);
lean_ctor_set(v_reuseFailAlloc_1926_, 1, v_k_1286_);
lean_ctor_set(v_reuseFailAlloc_1926_, 2, v_v_1287_);
lean_ctor_set(v_reuseFailAlloc_1926_, 3, v_l_1871_);
lean_ctor_set(v_reuseFailAlloc_1926_, 4, v_l_1871_);
v___x_1922_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
lean_object* v___x_1924_; 
if (v_isShared_1292_ == 0)
{
lean_ctor_set(v___x_1291_, 4, v___x_1922_);
lean_ctor_set(v___x_1291_, 3, v___x_1920_);
lean_ctor_set(v___x_1291_, 2, v_v_1914_);
lean_ctor_set(v___x_1291_, 1, v_k_1913_);
lean_ctor_set(v___x_1291_, 0, v___x_1918_);
v___x_1924_ = v___x_1291_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v___x_1918_);
lean_ctor_set(v_reuseFailAlloc_1925_, 1, v_k_1913_);
lean_ctor_set(v_reuseFailAlloc_1925_, 2, v_v_1914_);
lean_ctor_set(v_reuseFailAlloc_1925_, 3, v___x_1920_);
lean_ctor_set(v_reuseFailAlloc_1925_, 4, v___x_1922_);
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
else
{
lean_object* v___x_1936_; lean_object* v___x_1938_; 
v___x_1936_ = lean_unsigned_to_nat(2u);
if (v_isShared_1292_ == 0)
{
lean_ctor_set(v___x_1291_, 4, v_r_1907_);
lean_ctor_set(v___x_1291_, 0, v___x_1936_);
v___x_1938_ = v___x_1291_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v___x_1936_);
lean_ctor_set(v_reuseFailAlloc_1939_, 1, v_k_1286_);
lean_ctor_set(v_reuseFailAlloc_1939_, 2, v_v_1287_);
lean_ctor_set(v_reuseFailAlloc_1939_, 3, v_l_1288_);
lean_ctor_set(v_reuseFailAlloc_1939_, 4, v_r_1907_);
v___x_1938_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
return v___x_1938_;
}
}
}
}
else
{
lean_object* v___x_1941_; 
if (v_isShared_1292_ == 0)
{
lean_ctor_set(v___x_1291_, 4, v_l_1288_);
lean_ctor_set(v___x_1291_, 0, v___x_1780_);
v___x_1941_ = v___x_1291_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v___x_1780_);
lean_ctor_set(v_reuseFailAlloc_1942_, 1, v_k_1286_);
lean_ctor_set(v_reuseFailAlloc_1942_, 2, v_v_1287_);
lean_ctor_set(v_reuseFailAlloc_1942_, 3, v_l_1288_);
lean_ctor_set(v_reuseFailAlloc_1942_, 4, v_l_1288_);
v___x_1941_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
return v___x_1941_;
}
}
}
}
}
}
}
else
{
return v_t_1285_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg___boxed(lean_object* v_k_1945_, lean_object* v_t_1946_){
_start:
{
lean_object* v_res_1947_; 
v_res_1947_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_k_1945_, v_t_1946_);
lean_dec_ref(v_k_1945_);
return v_res_1947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___lam__0(lean_object* v_val_1948_, lean_object* v_s_1949_){
_start:
{
lean_object* v_toRing_1950_; lean_object* v_invFn_x3f_1951_; lean_object* v_semiringId_x3f_1952_; lean_object* v_commSemiringInst_1953_; lean_object* v_commRingInst_1954_; lean_object* v_noZeroDivInst_x3f_1955_; lean_object* v_fieldInst_x3f_1956_; lean_object* v_powIdentityInst_x3f_1957_; lean_object* v_denoteEntries_1958_; lean_object* v_nextId_1959_; lean_object* v_steps_1960_; lean_object* v_queue_1961_; lean_object* v_basis_1962_; lean_object* v_diseqs_1963_; uint8_t v_recheck_1964_; lean_object* v_invSet_1965_; lean_object* v_powIdentityVarCount_1966_; lean_object* v_numEq0_x3f_1967_; uint8_t v_numEq0Updated_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_1976_; 
v_toRing_1950_ = lean_ctor_get(v_s_1949_, 0);
v_invFn_x3f_1951_ = lean_ctor_get(v_s_1949_, 1);
v_semiringId_x3f_1952_ = lean_ctor_get(v_s_1949_, 2);
v_commSemiringInst_1953_ = lean_ctor_get(v_s_1949_, 3);
v_commRingInst_1954_ = lean_ctor_get(v_s_1949_, 4);
v_noZeroDivInst_x3f_1955_ = lean_ctor_get(v_s_1949_, 5);
v_fieldInst_x3f_1956_ = lean_ctor_get(v_s_1949_, 6);
v_powIdentityInst_x3f_1957_ = lean_ctor_get(v_s_1949_, 7);
v_denoteEntries_1958_ = lean_ctor_get(v_s_1949_, 8);
v_nextId_1959_ = lean_ctor_get(v_s_1949_, 9);
v_steps_1960_ = lean_ctor_get(v_s_1949_, 10);
v_queue_1961_ = lean_ctor_get(v_s_1949_, 11);
v_basis_1962_ = lean_ctor_get(v_s_1949_, 12);
v_diseqs_1963_ = lean_ctor_get(v_s_1949_, 13);
v_recheck_1964_ = lean_ctor_get_uint8(v_s_1949_, sizeof(void*)*17);
v_invSet_1965_ = lean_ctor_get(v_s_1949_, 14);
v_powIdentityVarCount_1966_ = lean_ctor_get(v_s_1949_, 15);
v_numEq0_x3f_1967_ = lean_ctor_get(v_s_1949_, 16);
v_numEq0Updated_1968_ = lean_ctor_get_uint8(v_s_1949_, sizeof(void*)*17 + 1);
v_isSharedCheck_1976_ = !lean_is_exclusive(v_s_1949_);
if (v_isSharedCheck_1976_ == 0)
{
v___x_1970_ = v_s_1949_;
v_isShared_1971_ = v_isSharedCheck_1976_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_numEq0_x3f_1967_);
lean_inc(v_powIdentityVarCount_1966_);
lean_inc(v_invSet_1965_);
lean_inc(v_diseqs_1963_);
lean_inc(v_basis_1962_);
lean_inc(v_queue_1961_);
lean_inc(v_steps_1960_);
lean_inc(v_nextId_1959_);
lean_inc(v_denoteEntries_1958_);
lean_inc(v_powIdentityInst_x3f_1957_);
lean_inc(v_fieldInst_x3f_1956_);
lean_inc(v_noZeroDivInst_x3f_1955_);
lean_inc(v_commRingInst_1954_);
lean_inc(v_commSemiringInst_1953_);
lean_inc(v_semiringId_x3f_1952_);
lean_inc(v_invFn_x3f_1951_);
lean_inc(v_toRing_1950_);
lean_dec(v_s_1949_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_1976_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
lean_object* v___x_1972_; lean_object* v___x_1974_; 
v___x_1972_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_val_1948_, v_queue_1961_);
if (v_isShared_1971_ == 0)
{
lean_ctor_set(v___x_1970_, 11, v___x_1972_);
v___x_1974_ = v___x_1970_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v_toRing_1950_);
lean_ctor_set(v_reuseFailAlloc_1975_, 1, v_invFn_x3f_1951_);
lean_ctor_set(v_reuseFailAlloc_1975_, 2, v_semiringId_x3f_1952_);
lean_ctor_set(v_reuseFailAlloc_1975_, 3, v_commSemiringInst_1953_);
lean_ctor_set(v_reuseFailAlloc_1975_, 4, v_commRingInst_1954_);
lean_ctor_set(v_reuseFailAlloc_1975_, 5, v_noZeroDivInst_x3f_1955_);
lean_ctor_set(v_reuseFailAlloc_1975_, 6, v_fieldInst_x3f_1956_);
lean_ctor_set(v_reuseFailAlloc_1975_, 7, v_powIdentityInst_x3f_1957_);
lean_ctor_set(v_reuseFailAlloc_1975_, 8, v_denoteEntries_1958_);
lean_ctor_set(v_reuseFailAlloc_1975_, 9, v_nextId_1959_);
lean_ctor_set(v_reuseFailAlloc_1975_, 10, v_steps_1960_);
lean_ctor_set(v_reuseFailAlloc_1975_, 11, v___x_1972_);
lean_ctor_set(v_reuseFailAlloc_1975_, 12, v_basis_1962_);
lean_ctor_set(v_reuseFailAlloc_1975_, 13, v_diseqs_1963_);
lean_ctor_set(v_reuseFailAlloc_1975_, 14, v_invSet_1965_);
lean_ctor_set(v_reuseFailAlloc_1975_, 15, v_powIdentityVarCount_1966_);
lean_ctor_set(v_reuseFailAlloc_1975_, 16, v_numEq0_x3f_1967_);
lean_ctor_set_uint8(v_reuseFailAlloc_1975_, sizeof(void*)*17, v_recheck_1964_);
lean_ctor_set_uint8(v_reuseFailAlloc_1975_, sizeof(void*)*17 + 1, v_numEq0Updated_1968_);
v___x_1974_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1973_;
}
v_reusejp_1973_:
{
return v___x_1974_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___lam__0___boxed(lean_object* v_val_1977_, lean_object* v_s_1978_){
_start:
{
lean_object* v_res_1979_; 
v_res_1979_ = l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___lam__0(v_val_1977_, v_s_1978_);
lean_dec_ref(v_val_1977_);
return v_res_1979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f(lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_){
_start:
{
lean_object* v___x_1992_; 
v___x_1992_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v_a_1980_, v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_, v_a_1985_, v_a_1986_, v_a_1987_, v_a_1988_, v_a_1989_, v_a_1990_);
if (lean_obj_tag(v___x_1992_) == 0)
{
lean_object* v_a_1993_; lean_object* v___x_1995_; uint8_t v_isShared_1996_; uint8_t v_isSharedCheck_2032_; 
v_a_1993_ = lean_ctor_get(v___x_1992_, 0);
v_isSharedCheck_2032_ = !lean_is_exclusive(v___x_1992_);
if (v_isSharedCheck_2032_ == 0)
{
v___x_1995_ = v___x_1992_;
v_isShared_1996_ = v_isSharedCheck_2032_;
goto v_resetjp_1994_;
}
else
{
lean_inc(v_a_1993_);
lean_dec(v___x_1992_);
v___x_1995_ = lean_box(0);
v_isShared_1996_ = v_isSharedCheck_2032_;
goto v_resetjp_1994_;
}
v_resetjp_1994_:
{
lean_object* v_queue_1997_; lean_object* v___x_1998_; 
v_queue_1997_ = lean_ctor_get(v_a_1993_, 11);
lean_inc(v_queue_1997_);
lean_dec(v_a_1993_);
v___x_1998_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_queue_1997_);
lean_dec(v_queue_1997_);
if (lean_obj_tag(v___x_1998_) == 1)
{
lean_object* v_val_1999_; lean_object* v___f_2000_; lean_object* v___x_2001_; 
lean_del_object(v___x_1995_);
v_val_1999_ = lean_ctor_get(v___x_1998_, 0);
lean_inc(v_val_1999_);
v___f_2000_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2000_, 0, v_val_1999_);
v___x_2001_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_2000_, v_a_1980_, v_a_1981_);
if (lean_obj_tag(v___x_2001_) == 0)
{
lean_object* v___x_2002_; lean_object* v___x_2003_; 
lean_dec_ref(v___x_2001_);
v___x_2002_ = lean_unsigned_to_nat(1u);
v___x_2003_ = l_Lean_Meta_Grind_Arith_CommRing_incSteps___redArg(v___x_2002_, v_a_1981_);
if (lean_obj_tag(v___x_2003_) == 0)
{
lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2010_; 
v_isSharedCheck_2010_ = !lean_is_exclusive(v___x_2003_);
if (v_isSharedCheck_2010_ == 0)
{
lean_object* v_unused_2011_; 
v_unused_2011_ = lean_ctor_get(v___x_2003_, 0);
lean_dec(v_unused_2011_);
v___x_2005_ = v___x_2003_;
v_isShared_2006_ = v_isSharedCheck_2010_;
goto v_resetjp_2004_;
}
else
{
lean_dec(v___x_2003_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2010_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
lean_object* v___x_2008_; 
if (v_isShared_2006_ == 0)
{
lean_ctor_set(v___x_2005_, 0, v___x_1998_);
v___x_2008_ = v___x_2005_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v___x_1998_);
v___x_2008_ = v_reuseFailAlloc_2009_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
return v___x_2008_;
}
}
}
else
{
lean_object* v_a_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2019_; 
lean_dec_ref(v___x_1998_);
v_a_2012_ = lean_ctor_get(v___x_2003_, 0);
v_isSharedCheck_2019_ = !lean_is_exclusive(v___x_2003_);
if (v_isSharedCheck_2019_ == 0)
{
v___x_2014_ = v___x_2003_;
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_a_2012_);
lean_dec(v___x_2003_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2017_; 
if (v_isShared_2015_ == 0)
{
v___x_2017_ = v___x_2014_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v_a_2012_);
v___x_2017_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
return v___x_2017_;
}
}
}
}
else
{
lean_object* v_a_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2027_; 
lean_dec_ref(v___x_1998_);
v_a_2020_ = lean_ctor_get(v___x_2001_, 0);
v_isSharedCheck_2027_ = !lean_is_exclusive(v___x_2001_);
if (v_isSharedCheck_2027_ == 0)
{
v___x_2022_ = v___x_2001_;
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_a_2020_);
lean_dec(v___x_2001_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v___x_2025_; 
if (v_isShared_2023_ == 0)
{
v___x_2025_ = v___x_2022_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v_a_2020_);
v___x_2025_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
return v___x_2025_;
}
}
}
}
else
{
lean_object* v___x_2028_; lean_object* v___x_2030_; 
lean_dec(v___x_1998_);
v___x_2028_ = lean_box(0);
if (v_isShared_1996_ == 0)
{
lean_ctor_set(v___x_1995_, 0, v___x_2028_);
v___x_2030_ = v___x_1995_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v___x_2028_);
v___x_2030_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
return v___x_2030_;
}
}
}
}
else
{
lean_object* v_a_2033_; lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2040_; 
v_a_2033_ = lean_ctor_get(v___x_1992_, 0);
v_isSharedCheck_2040_ = !lean_is_exclusive(v___x_1992_);
if (v_isSharedCheck_2040_ == 0)
{
v___x_2035_ = v___x_1992_;
v_isShared_2036_ = v_isSharedCheck_2040_;
goto v_resetjp_2034_;
}
else
{
lean_inc(v_a_2033_);
lean_dec(v___x_1992_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2040_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v___x_2038_; 
if (v_isShared_2036_ == 0)
{
v___x_2038_ = v___x_2035_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v_a_2033_);
v___x_2038_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
return v___x_2038_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f___boxed(lean_object* v_a_2041_, lean_object* v_a_2042_, lean_object* v_a_2043_, lean_object* v_a_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_){
_start:
{
lean_object* v_res_2053_; 
v_res_2053_ = l_Lean_Meta_Grind_Arith_CommRing_getNext_x3f(v_a_2041_, v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_, v_a_2046_, v_a_2047_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_);
lean_dec(v_a_2051_);
lean_dec_ref(v_a_2050_);
lean_dec(v_a_2049_);
lean_dec_ref(v_a_2048_);
lean_dec(v_a_2047_);
lean_dec_ref(v_a_2046_);
lean_dec(v_a_2045_);
lean_dec_ref(v_a_2044_);
lean_dec(v_a_2043_);
lean_dec(v_a_2042_);
lean_dec_ref(v_a_2041_);
return v_res_2053_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0(lean_object* v_00_u03b2_2054_, lean_object* v_k_2055_, lean_object* v_t_2056_, lean_object* v_h_2057_){
_start:
{
lean_object* v___x_2058_; 
v___x_2058_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___redArg(v_k_2055_, v_t_2056_);
return v___x_2058_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0___boxed(lean_object* v_00_u03b2_2059_, lean_object* v_k_2060_, lean_object* v_t_2061_, lean_object* v_h_2062_){
_start:
{
lean_object* v_res_2063_; 
v_res_2063_ = l_Std_DTreeMap_Internal_Impl_erase___at___00Lean_Meta_Grind_Arith_CommRing_getNext_x3f_spec__0(v_00_u03b2_2059_, v_k_2060_, v_t_2061_, v_h_2062_);
lean_dec_ref(v_k_2060_);
return v_res_2063_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_2064_, lean_object* v_x_2065_, lean_object* v_x_2066_, lean_object* v_x_2067_){
_start:
{
lean_object* v_ks_2068_; lean_object* v_vs_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2093_; 
v_ks_2068_ = lean_ctor_get(v_x_2064_, 0);
v_vs_2069_ = lean_ctor_get(v_x_2064_, 1);
v_isSharedCheck_2093_ = !lean_is_exclusive(v_x_2064_);
if (v_isSharedCheck_2093_ == 0)
{
v___x_2071_ = v_x_2064_;
v_isShared_2072_ = v_isSharedCheck_2093_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_vs_2069_);
lean_inc(v_ks_2068_);
lean_dec(v_x_2064_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2093_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
lean_object* v___x_2073_; uint8_t v___x_2074_; 
v___x_2073_ = lean_array_get_size(v_ks_2068_);
v___x_2074_ = lean_nat_dec_lt(v_x_2065_, v___x_2073_);
if (v___x_2074_ == 0)
{
lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2078_; 
lean_dec(v_x_2065_);
v___x_2075_ = lean_array_push(v_ks_2068_, v_x_2066_);
v___x_2076_ = lean_array_push(v_vs_2069_, v_x_2067_);
if (v_isShared_2072_ == 0)
{
lean_ctor_set(v___x_2071_, 1, v___x_2076_);
lean_ctor_set(v___x_2071_, 0, v___x_2075_);
v___x_2078_ = v___x_2071_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v___x_2075_);
lean_ctor_set(v_reuseFailAlloc_2079_, 1, v___x_2076_);
v___x_2078_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
return v___x_2078_;
}
}
else
{
lean_object* v_k_x27_2080_; uint8_t v___x_2081_; 
v_k_x27_2080_ = lean_array_fget_borrowed(v_ks_2068_, v_x_2065_);
v___x_2081_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_2066_, v_k_x27_2080_);
if (v___x_2081_ == 0)
{
lean_object* v___x_2083_; 
if (v_isShared_2072_ == 0)
{
v___x_2083_ = v___x_2071_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v_ks_2068_);
lean_ctor_set(v_reuseFailAlloc_2087_, 1, v_vs_2069_);
v___x_2083_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
lean_object* v___x_2084_; lean_object* v___x_2085_; 
v___x_2084_ = lean_unsigned_to_nat(1u);
v___x_2085_ = lean_nat_add(v_x_2065_, v___x_2084_);
lean_dec(v_x_2065_);
v_x_2064_ = v___x_2083_;
v_x_2065_ = v___x_2085_;
goto _start;
}
}
else
{
lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2091_; 
v___x_2088_ = lean_array_fset(v_ks_2068_, v_x_2065_, v_x_2066_);
v___x_2089_ = lean_array_fset(v_vs_2069_, v_x_2065_, v_x_2067_);
lean_dec(v_x_2065_);
if (v_isShared_2072_ == 0)
{
lean_ctor_set(v___x_2071_, 1, v___x_2089_);
lean_ctor_set(v___x_2071_, 0, v___x_2088_);
v___x_2091_ = v___x_2071_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v___x_2088_);
lean_ctor_set(v_reuseFailAlloc_2092_, 1, v___x_2089_);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1___redArg(lean_object* v_n_2094_, lean_object* v_k_2095_, lean_object* v_v_2096_){
_start:
{
lean_object* v___x_2097_; lean_object* v___x_2098_; 
v___x_2097_ = lean_unsigned_to_nat(0u);
v___x_2098_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1_spec__2___redArg(v_n_2094_, v___x_2097_, v_k_2095_, v_v_2096_);
return v___x_2098_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2099_; 
v___x_2099_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_2099_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(lean_object* v_x_2100_, size_t v_x_2101_, size_t v_x_2102_, lean_object* v_x_2103_, lean_object* v_x_2104_){
_start:
{
if (lean_obj_tag(v_x_2100_) == 0)
{
lean_object* v_es_2105_; size_t v___x_2106_; size_t v___x_2107_; size_t v___x_2108_; size_t v___x_2109_; lean_object* v_j_2110_; lean_object* v___x_2111_; uint8_t v___x_2112_; 
v_es_2105_ = lean_ctor_get(v_x_2100_, 0);
v___x_2106_ = ((size_t)5ULL);
v___x_2107_ = ((size_t)1ULL);
v___x_2108_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0_spec__0___redArg___closed__1);
v___x_2109_ = lean_usize_land(v_x_2101_, v___x_2108_);
v_j_2110_ = lean_usize_to_nat(v___x_2109_);
v___x_2111_ = lean_array_get_size(v_es_2105_);
v___x_2112_ = lean_nat_dec_lt(v_j_2110_, v___x_2111_);
if (v___x_2112_ == 0)
{
lean_dec(v_j_2110_);
lean_dec(v_x_2104_);
lean_dec_ref(v_x_2103_);
return v_x_2100_;
}
else
{
lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2149_; 
lean_inc_ref(v_es_2105_);
v_isSharedCheck_2149_ = !lean_is_exclusive(v_x_2100_);
if (v_isSharedCheck_2149_ == 0)
{
lean_object* v_unused_2150_; 
v_unused_2150_ = lean_ctor_get(v_x_2100_, 0);
lean_dec(v_unused_2150_);
v___x_2114_ = v_x_2100_;
v_isShared_2115_ = v_isSharedCheck_2149_;
goto v_resetjp_2113_;
}
else
{
lean_dec(v_x_2100_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2149_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v_v_2116_; lean_object* v___x_2117_; lean_object* v_xs_x27_2118_; lean_object* v___y_2120_; 
v_v_2116_ = lean_array_fget(v_es_2105_, v_j_2110_);
v___x_2117_ = lean_box(0);
v_xs_x27_2118_ = lean_array_fset(v_es_2105_, v_j_2110_, v___x_2117_);
switch(lean_obj_tag(v_v_2116_))
{
case 0:
{
lean_object* v_key_2125_; lean_object* v_val_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2136_; 
v_key_2125_ = lean_ctor_get(v_v_2116_, 0);
v_val_2126_ = lean_ctor_get(v_v_2116_, 1);
v_isSharedCheck_2136_ = !lean_is_exclusive(v_v_2116_);
if (v_isSharedCheck_2136_ == 0)
{
v___x_2128_ = v_v_2116_;
v_isShared_2129_ = v_isSharedCheck_2136_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_val_2126_);
lean_inc(v_key_2125_);
lean_dec(v_v_2116_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2136_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
uint8_t v___x_2130_; 
v___x_2130_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_2103_, v_key_2125_);
if (v___x_2130_ == 0)
{
lean_object* v___x_2131_; lean_object* v___x_2132_; 
lean_del_object(v___x_2128_);
v___x_2131_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_2125_, v_val_2126_, v_x_2103_, v_x_2104_);
v___x_2132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2132_, 0, v___x_2131_);
v___y_2120_ = v___x_2132_;
goto v___jp_2119_;
}
else
{
lean_object* v___x_2134_; 
lean_dec(v_val_2126_);
lean_dec(v_key_2125_);
if (v_isShared_2129_ == 0)
{
lean_ctor_set(v___x_2128_, 1, v_x_2104_);
lean_ctor_set(v___x_2128_, 0, v_x_2103_);
v___x_2134_ = v___x_2128_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v_x_2103_);
lean_ctor_set(v_reuseFailAlloc_2135_, 1, v_x_2104_);
v___x_2134_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
v___y_2120_ = v___x_2134_;
goto v___jp_2119_;
}
}
}
}
case 1:
{
lean_object* v_node_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2147_; 
v_node_2137_ = lean_ctor_get(v_v_2116_, 0);
v_isSharedCheck_2147_ = !lean_is_exclusive(v_v_2116_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2139_ = v_v_2116_;
v_isShared_2140_ = v_isSharedCheck_2147_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_node_2137_);
lean_dec(v_v_2116_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2147_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
size_t v___x_2141_; size_t v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2145_; 
v___x_2141_ = lean_usize_shift_right(v_x_2101_, v___x_2106_);
v___x_2142_ = lean_usize_add(v_x_2102_, v___x_2107_);
v___x_2143_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_node_2137_, v___x_2141_, v___x_2142_, v_x_2103_, v_x_2104_);
if (v_isShared_2140_ == 0)
{
lean_ctor_set(v___x_2139_, 0, v___x_2143_);
v___x_2145_ = v___x_2139_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v___x_2143_);
v___x_2145_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
v___y_2120_ = v___x_2145_;
goto v___jp_2119_;
}
}
}
default: 
{
lean_object* v___x_2148_; 
v___x_2148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2148_, 0, v_x_2103_);
lean_ctor_set(v___x_2148_, 1, v_x_2104_);
v___y_2120_ = v___x_2148_;
goto v___jp_2119_;
}
}
v___jp_2119_:
{
lean_object* v___x_2121_; lean_object* v___x_2123_; 
v___x_2121_ = lean_array_fset(v_xs_x27_2118_, v_j_2110_, v___y_2120_);
lean_dec(v_j_2110_);
if (v_isShared_2115_ == 0)
{
lean_ctor_set(v___x_2114_, 0, v___x_2121_);
v___x_2123_ = v___x_2114_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v___x_2121_);
v___x_2123_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2122_;
}
v_reusejp_2122_:
{
return v___x_2123_;
}
}
}
}
}
else
{
lean_object* v_ks_2151_; lean_object* v_vs_2152_; lean_object* v___x_2154_; uint8_t v_isShared_2155_; uint8_t v_isSharedCheck_2172_; 
v_ks_2151_ = lean_ctor_get(v_x_2100_, 0);
v_vs_2152_ = lean_ctor_get(v_x_2100_, 1);
v_isSharedCheck_2172_ = !lean_is_exclusive(v_x_2100_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2154_ = v_x_2100_;
v_isShared_2155_ = v_isSharedCheck_2172_;
goto v_resetjp_2153_;
}
else
{
lean_inc(v_vs_2152_);
lean_inc(v_ks_2151_);
lean_dec(v_x_2100_);
v___x_2154_ = lean_box(0);
v_isShared_2155_ = v_isSharedCheck_2172_;
goto v_resetjp_2153_;
}
v_resetjp_2153_:
{
lean_object* v___x_2157_; 
if (v_isShared_2155_ == 0)
{
v___x_2157_ = v___x_2154_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v_ks_2151_);
lean_ctor_set(v_reuseFailAlloc_2171_, 1, v_vs_2152_);
v___x_2157_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
lean_object* v_newNode_2158_; uint8_t v___y_2160_; size_t v___x_2166_; uint8_t v___x_2167_; 
v_newNode_2158_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1___redArg(v___x_2157_, v_x_2103_, v_x_2104_);
v___x_2166_ = ((size_t)7ULL);
v___x_2167_ = lean_usize_dec_le(v___x_2166_, v_x_2102_);
if (v___x_2167_ == 0)
{
lean_object* v___x_2168_; lean_object* v___x_2169_; uint8_t v___x_2170_; 
v___x_2168_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2158_);
v___x_2169_ = lean_unsigned_to_nat(4u);
v___x_2170_ = lean_nat_dec_lt(v___x_2168_, v___x_2169_);
lean_dec(v___x_2168_);
v___y_2160_ = v___x_2170_;
goto v___jp_2159_;
}
else
{
v___y_2160_ = v___x_2167_;
goto v___jp_2159_;
}
v___jp_2159_:
{
if (v___y_2160_ == 0)
{
lean_object* v_ks_2161_; lean_object* v_vs_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; 
v_ks_2161_ = lean_ctor_get(v_newNode_2158_, 0);
lean_inc_ref(v_ks_2161_);
v_vs_2162_ = lean_ctor_get(v_newNode_2158_, 1);
lean_inc_ref(v_vs_2162_);
lean_dec_ref(v_newNode_2158_);
v___x_2163_ = lean_unsigned_to_nat(0u);
v___x_2164_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___closed__0);
v___x_2165_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg(v_x_2102_, v_ks_2161_, v_vs_2162_, v___x_2163_, v___x_2164_);
lean_dec_ref(v_vs_2162_);
lean_dec_ref(v_ks_2161_);
return v___x_2165_;
}
else
{
return v_newNode_2158_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg(size_t v_depth_2173_, lean_object* v_keys_2174_, lean_object* v_vals_2175_, lean_object* v_i_2176_, lean_object* v_entries_2177_){
_start:
{
lean_object* v___x_2178_; uint8_t v___x_2179_; 
v___x_2178_ = lean_array_get_size(v_keys_2174_);
v___x_2179_ = lean_nat_dec_lt(v_i_2176_, v___x_2178_);
if (v___x_2179_ == 0)
{
lean_dec(v_i_2176_);
return v_entries_2177_;
}
else
{
lean_object* v_k_2180_; lean_object* v_v_2181_; uint64_t v___x_2182_; size_t v_h_2183_; size_t v___x_2184_; lean_object* v___x_2185_; size_t v___x_2186_; size_t v___x_2187_; size_t v___x_2188_; size_t v_h_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; 
v_k_2180_ = lean_array_fget_borrowed(v_keys_2174_, v_i_2176_);
v_v_2181_ = lean_array_fget_borrowed(v_vals_2175_, v_i_2176_);
v___x_2182_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_2180_);
v_h_2183_ = lean_uint64_to_usize(v___x_2182_);
v___x_2184_ = ((size_t)5ULL);
v___x_2185_ = lean_unsigned_to_nat(1u);
v___x_2186_ = ((size_t)1ULL);
v___x_2187_ = lean_usize_sub(v_depth_2173_, v___x_2186_);
v___x_2188_ = lean_usize_mul(v___x_2184_, v___x_2187_);
v_h_2189_ = lean_usize_shift_right(v_h_2183_, v___x_2188_);
v___x_2190_ = lean_nat_add(v_i_2176_, v___x_2185_);
lean_dec(v_i_2176_);
lean_inc(v_v_2181_);
lean_inc(v_k_2180_);
v___x_2191_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_entries_2177_, v_h_2189_, v_depth_2173_, v_k_2180_, v_v_2181_);
v_i_2176_ = v___x_2190_;
v_entries_2177_ = v___x_2191_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_2193_, lean_object* v_keys_2194_, lean_object* v_vals_2195_, lean_object* v_i_2196_, lean_object* v_entries_2197_){
_start:
{
size_t v_depth_boxed_2198_; lean_object* v_res_2199_; 
v_depth_boxed_2198_ = lean_unbox_usize(v_depth_2193_);
lean_dec(v_depth_2193_);
v_res_2199_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg(v_depth_boxed_2198_, v_keys_2194_, v_vals_2195_, v_i_2196_, v_entries_2197_);
lean_dec_ref(v_vals_2195_);
lean_dec_ref(v_keys_2194_);
return v_res_2199_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg___boxed(lean_object* v_x_2200_, lean_object* v_x_2201_, lean_object* v_x_2202_, lean_object* v_x_2203_, lean_object* v_x_2204_){
_start:
{
size_t v_x_7240__boxed_2205_; size_t v_x_7241__boxed_2206_; lean_object* v_res_2207_; 
v_x_7240__boxed_2205_ = lean_unbox_usize(v_x_2201_);
lean_dec(v_x_2201_);
v_x_7241__boxed_2206_ = lean_unbox_usize(v_x_2202_);
lean_dec(v_x_2202_);
v_res_2207_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_x_2200_, v_x_7240__boxed_2205_, v_x_7241__boxed_2206_, v_x_2203_, v_x_2204_);
return v_res_2207_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0___redArg(lean_object* v_x_2208_, lean_object* v_x_2209_, lean_object* v_x_2210_){
_start:
{
uint64_t v___x_2211_; size_t v___x_2212_; size_t v___x_2213_; lean_object* v___x_2214_; 
v___x_2211_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_2209_);
v___x_2212_ = lean_uint64_to_usize(v___x_2211_);
v___x_2213_ = ((size_t)1ULL);
v___x_2214_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_x_2208_, v___x_2212_, v___x_2213_, v_x_2209_, v_x_2210_);
return v___x_2214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___lam__0(lean_object* v_e_2215_, lean_object* v_ringId_2216_, lean_object* v_s_2217_){
_start:
{
lean_object* v_rings_2218_; lean_object* v_typeIdOf_2219_; lean_object* v_exprToRingId_2220_; lean_object* v_semirings_2221_; lean_object* v_stypeIdOf_2222_; lean_object* v_exprToSemiringId_2223_; lean_object* v_ncRings_2224_; lean_object* v_exprToNCRingId_2225_; lean_object* v_nctypeIdOf_2226_; lean_object* v_ncSemirings_2227_; lean_object* v_exprToNCSemiringId_2228_; lean_object* v_ncstypeIdOf_2229_; lean_object* v_steps_2230_; uint8_t v_reportedMaxDegreeIssue_2231_; lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2239_; 
v_rings_2218_ = lean_ctor_get(v_s_2217_, 0);
v_typeIdOf_2219_ = lean_ctor_get(v_s_2217_, 1);
v_exprToRingId_2220_ = lean_ctor_get(v_s_2217_, 2);
v_semirings_2221_ = lean_ctor_get(v_s_2217_, 3);
v_stypeIdOf_2222_ = lean_ctor_get(v_s_2217_, 4);
v_exprToSemiringId_2223_ = lean_ctor_get(v_s_2217_, 5);
v_ncRings_2224_ = lean_ctor_get(v_s_2217_, 6);
v_exprToNCRingId_2225_ = lean_ctor_get(v_s_2217_, 7);
v_nctypeIdOf_2226_ = lean_ctor_get(v_s_2217_, 8);
v_ncSemirings_2227_ = lean_ctor_get(v_s_2217_, 9);
v_exprToNCSemiringId_2228_ = lean_ctor_get(v_s_2217_, 10);
v_ncstypeIdOf_2229_ = lean_ctor_get(v_s_2217_, 11);
v_steps_2230_ = lean_ctor_get(v_s_2217_, 12);
v_reportedMaxDegreeIssue_2231_ = lean_ctor_get_uint8(v_s_2217_, sizeof(void*)*13);
v_isSharedCheck_2239_ = !lean_is_exclusive(v_s_2217_);
if (v_isSharedCheck_2239_ == 0)
{
v___x_2233_ = v_s_2217_;
v_isShared_2234_ = v_isSharedCheck_2239_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_steps_2230_);
lean_inc(v_ncstypeIdOf_2229_);
lean_inc(v_exprToNCSemiringId_2228_);
lean_inc(v_ncSemirings_2227_);
lean_inc(v_nctypeIdOf_2226_);
lean_inc(v_exprToNCRingId_2225_);
lean_inc(v_ncRings_2224_);
lean_inc(v_exprToSemiringId_2223_);
lean_inc(v_stypeIdOf_2222_);
lean_inc(v_semirings_2221_);
lean_inc(v_exprToRingId_2220_);
lean_inc(v_typeIdOf_2219_);
lean_inc(v_rings_2218_);
lean_dec(v_s_2217_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2239_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
lean_object* v___x_2235_; lean_object* v___x_2237_; 
v___x_2235_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0___redArg(v_exprToRingId_2220_, v_e_2215_, v_ringId_2216_);
if (v_isShared_2234_ == 0)
{
lean_ctor_set(v___x_2233_, 2, v___x_2235_);
v___x_2237_ = v___x_2233_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v_rings_2218_);
lean_ctor_set(v_reuseFailAlloc_2238_, 1, v_typeIdOf_2219_);
lean_ctor_set(v_reuseFailAlloc_2238_, 2, v___x_2235_);
lean_ctor_set(v_reuseFailAlloc_2238_, 3, v_semirings_2221_);
lean_ctor_set(v_reuseFailAlloc_2238_, 4, v_stypeIdOf_2222_);
lean_ctor_set(v_reuseFailAlloc_2238_, 5, v_exprToSemiringId_2223_);
lean_ctor_set(v_reuseFailAlloc_2238_, 6, v_ncRings_2224_);
lean_ctor_set(v_reuseFailAlloc_2238_, 7, v_exprToNCRingId_2225_);
lean_ctor_set(v_reuseFailAlloc_2238_, 8, v_nctypeIdOf_2226_);
lean_ctor_set(v_reuseFailAlloc_2238_, 9, v_ncSemirings_2227_);
lean_ctor_set(v_reuseFailAlloc_2238_, 10, v_exprToNCSemiringId_2228_);
lean_ctor_set(v_reuseFailAlloc_2238_, 11, v_ncstypeIdOf_2229_);
lean_ctor_set(v_reuseFailAlloc_2238_, 12, v_steps_2230_);
lean_ctor_set_uint8(v_reuseFailAlloc_2238_, sizeof(void*)*13, v_reportedMaxDegreeIssue_2231_);
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
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__1(void){
_start:
{
lean_object* v___x_2241_; lean_object* v___x_2242_; 
v___x_2241_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__0));
v___x_2242_ = l_Lean_stringToMessageData(v___x_2241_);
return v___x_2242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(lean_object* v_e_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_){
_start:
{
lean_object* v___x_2256_; 
v___x_2256_ = l_Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f___redArg(v_e_2243_, v_a_2245_, v_a_2250_);
if (lean_obj_tag(v___x_2256_) == 0)
{
lean_object* v_a_2257_; 
v_a_2257_ = lean_ctor_get(v___x_2256_, 0);
lean_inc(v_a_2257_);
lean_dec_ref(v___x_2256_);
if (lean_obj_tag(v_a_2257_) == 1)
{
lean_object* v_ringId_2258_; lean_object* v_val_2259_; uint8_t v___x_2260_; 
v_ringId_2258_ = lean_ctor_get(v_a_2244_, 0);
v_val_2259_ = lean_ctor_get(v_a_2257_, 0);
lean_inc(v_val_2259_);
lean_dec_ref(v_a_2257_);
v___x_2260_ = lean_nat_dec_eq(v_val_2259_, v_ringId_2258_);
lean_dec(v_val_2259_);
if (v___x_2260_ == 0)
{
lean_object* v___x_2261_; 
v___x_2261_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_2246_);
if (lean_obj_tag(v___x_2261_) == 0)
{
lean_object* v_a_2262_; uint8_t v___x_2263_; 
v_a_2262_ = lean_ctor_get(v___x_2261_, 0);
lean_inc(v_a_2262_);
lean_dec_ref(v___x_2261_);
v___x_2263_ = lean_unbox(v_a_2262_);
lean_dec(v_a_2262_);
if (v___x_2263_ == 0)
{
lean_dec_ref(v_e_2243_);
goto v___jp_2253_;
}
else
{
lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; 
v___x_2264_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___closed__1);
v___x_2265_ = l_Lean_indentExpr(v_e_2243_);
v___x_2266_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2266_, 0, v___x_2264_);
lean_ctor_set(v___x_2266_, 1, v___x_2265_);
v___x_2267_ = l_Lean_Meta_Sym_reportIssue(v___x_2266_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_, v_a_2250_, v_a_2251_);
if (lean_obj_tag(v___x_2267_) == 0)
{
lean_dec_ref(v___x_2267_);
goto v___jp_2253_;
}
else
{
return v___x_2267_;
}
}
}
else
{
lean_object* v_a_2268_; lean_object* v___x_2270_; uint8_t v_isShared_2271_; uint8_t v_isSharedCheck_2275_; 
lean_dec_ref(v_e_2243_);
v_a_2268_ = lean_ctor_get(v___x_2261_, 0);
v_isSharedCheck_2275_ = !lean_is_exclusive(v___x_2261_);
if (v_isSharedCheck_2275_ == 0)
{
v___x_2270_ = v___x_2261_;
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
else
{
lean_inc(v_a_2268_);
lean_dec(v___x_2261_);
v___x_2270_ = lean_box(0);
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
v_resetjp_2269_:
{
lean_object* v___x_2273_; 
if (v_isShared_2271_ == 0)
{
v___x_2273_ = v___x_2270_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v_a_2268_);
v___x_2273_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
return v___x_2273_;
}
}
}
}
else
{
lean_dec_ref(v_e_2243_);
goto v___jp_2253_;
}
}
else
{
lean_object* v_ringId_2276_; lean_object* v___f_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; 
lean_dec(v_a_2257_);
v_ringId_2276_ = lean_ctor_get(v_a_2244_, 0);
lean_inc(v_ringId_2276_);
v___f_2277_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2277_, 0, v_e_2243_);
lean_closure_set(v___f_2277_, 1, v_ringId_2276_);
v___x_2278_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_2279_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2278_, v___f_2277_, v_a_2245_);
return v___x_2279_;
}
}
else
{
lean_object* v_a_2280_; lean_object* v___x_2282_; uint8_t v_isShared_2283_; uint8_t v_isSharedCheck_2287_; 
lean_dec_ref(v_e_2243_);
v_a_2280_ = lean_ctor_get(v___x_2256_, 0);
v_isSharedCheck_2287_ = !lean_is_exclusive(v___x_2256_);
if (v_isSharedCheck_2287_ == 0)
{
v___x_2282_ = v___x_2256_;
v_isShared_2283_ = v_isSharedCheck_2287_;
goto v_resetjp_2281_;
}
else
{
lean_inc(v_a_2280_);
lean_dec(v___x_2256_);
v___x_2282_ = lean_box(0);
v_isShared_2283_ = v_isSharedCheck_2287_;
goto v_resetjp_2281_;
}
v_resetjp_2281_:
{
lean_object* v___x_2285_; 
if (v_isShared_2283_ == 0)
{
v___x_2285_ = v___x_2282_;
goto v_reusejp_2284_;
}
else
{
lean_object* v_reuseFailAlloc_2286_; 
v_reuseFailAlloc_2286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2286_, 0, v_a_2280_);
v___x_2285_ = v_reuseFailAlloc_2286_;
goto v_reusejp_2284_;
}
v_reusejp_2284_:
{
return v___x_2285_;
}
}
}
v___jp_2253_:
{
lean_object* v___x_2254_; lean_object* v___x_2255_; 
v___x_2254_ = lean_box(0);
v___x_2255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2255_, 0, v___x_2254_);
return v___x_2255_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg___boxed(lean_object* v_e_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_){
_start:
{
lean_object* v_res_2298_; 
v_res_2298_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(v_e_2288_, v_a_2289_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_);
lean_dec(v_a_2296_);
lean_dec_ref(v_a_2295_);
lean_dec(v_a_2294_);
lean_dec_ref(v_a_2293_);
lean_dec(v_a_2292_);
lean_dec_ref(v_a_2291_);
lean_dec(v_a_2290_);
lean_dec_ref(v_a_2289_);
return v_res_2298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId(lean_object* v_e_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_){
_start:
{
lean_object* v___x_2312_; 
v___x_2312_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(v_e_2299_, v_a_2300_, v_a_2301_, v_a_2305_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_, v_a_2310_);
return v___x_2312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___boxed(lean_object* v_e_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_, lean_object* v_a_2318_, lean_object* v_a_2319_, lean_object* v_a_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_){
_start:
{
lean_object* v_res_2326_; 
v_res_2326_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId(v_e_2313_, v_a_2314_, v_a_2315_, v_a_2316_, v_a_2317_, v_a_2318_, v_a_2319_, v_a_2320_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_);
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
lean_dec_ref(v_a_2314_);
return v_res_2326_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0(lean_object* v_00_u03b2_2327_, lean_object* v_x_2328_, lean_object* v_x_2329_, lean_object* v_x_2330_){
_start:
{
lean_object* v___x_2331_; 
v___x_2331_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0___redArg(v_x_2328_, v_x_2329_, v_x_2330_);
return v___x_2331_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0(lean_object* v_00_u03b2_2332_, lean_object* v_x_2333_, size_t v_x_2334_, size_t v_x_2335_, lean_object* v_x_2336_, lean_object* v_x_2337_){
_start:
{
lean_object* v___x_2338_; 
v___x_2338_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___redArg(v_x_2333_, v_x_2334_, v_x_2335_, v_x_2336_, v_x_2337_);
return v___x_2338_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2339_, lean_object* v_x_2340_, lean_object* v_x_2341_, lean_object* v_x_2342_, lean_object* v_x_2343_, lean_object* v_x_2344_){
_start:
{
size_t v_x_7519__boxed_2345_; size_t v_x_7520__boxed_2346_; lean_object* v_res_2347_; 
v_x_7519__boxed_2345_ = lean_unbox_usize(v_x_2341_);
lean_dec(v_x_2341_);
v_x_7520__boxed_2346_ = lean_unbox_usize(v_x_2342_);
lean_dec(v_x_2342_);
v_res_2347_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0(v_00_u03b2_2339_, v_x_2340_, v_x_7519__boxed_2345_, v_x_7520__boxed_2346_, v_x_2343_, v_x_2344_);
return v_res_2347_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2348_, lean_object* v_n_2349_, lean_object* v_k_2350_, lean_object* v_v_2351_){
_start:
{
lean_object* v___x_2352_; 
v___x_2352_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1___redArg(v_n_2349_, v_k_2350_, v_v_2351_);
return v___x_2352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_2353_, size_t v_depth_2354_, lean_object* v_keys_2355_, lean_object* v_vals_2356_, lean_object* v_heq_2357_, lean_object* v_i_2358_, lean_object* v_entries_2359_){
_start:
{
lean_object* v___x_2360_; 
v___x_2360_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___redArg(v_depth_2354_, v_keys_2355_, v_vals_2356_, v_i_2358_, v_entries_2359_);
return v___x_2360_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_2361_, lean_object* v_depth_2362_, lean_object* v_keys_2363_, lean_object* v_vals_2364_, lean_object* v_heq_2365_, lean_object* v_i_2366_, lean_object* v_entries_2367_){
_start:
{
size_t v_depth_boxed_2368_; lean_object* v_res_2369_; 
v_depth_boxed_2368_ = lean_unbox_usize(v_depth_2362_);
lean_dec(v_depth_2362_);
v_res_2369_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__2(v_00_u03b2_2361_, v_depth_boxed_2368_, v_keys_2363_, v_vals_2364_, v_heq_2365_, v_i_2366_, v_entries_2367_);
lean_dec_ref(v_vals_2364_);
lean_dec_ref(v_keys_2363_);
return v_res_2369_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2370_, lean_object* v_x_2371_, lean_object* v_x_2372_, lean_object* v_x_2373_, lean_object* v_x_2374_){
_start:
{
lean_object* v___x_2375_; 
v___x_2375_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0_spec__0_spec__1_spec__2___redArg(v_x_2371_, v_x_2372_, v_x_2373_, v_x_2374_);
return v___x_2375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__0(lean_object* v_e_2376_, lean_object* v___f_2377_, lean_object* v___f_2378_, lean_object* v_size_2379_, lean_object* v_s_2380_){
_start:
{
lean_object* v_id_2381_; lean_object* v_type_2382_; lean_object* v_u_2383_; lean_object* v_ringInst_2384_; lean_object* v_semiringInst_2385_; lean_object* v_charInst_x3f_2386_; lean_object* v_addFn_x3f_2387_; lean_object* v_mulFn_x3f_2388_; lean_object* v_subFn_x3f_2389_; lean_object* v_negFn_x3f_2390_; lean_object* v_powFn_x3f_2391_; lean_object* v_intCastFn_x3f_2392_; lean_object* v_natCastFn_x3f_2393_; lean_object* v_one_x3f_2394_; lean_object* v_vars_2395_; lean_object* v_varMap_2396_; lean_object* v_denote_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2406_; 
v_id_2381_ = lean_ctor_get(v_s_2380_, 0);
v_type_2382_ = lean_ctor_get(v_s_2380_, 1);
v_u_2383_ = lean_ctor_get(v_s_2380_, 2);
v_ringInst_2384_ = lean_ctor_get(v_s_2380_, 3);
v_semiringInst_2385_ = lean_ctor_get(v_s_2380_, 4);
v_charInst_x3f_2386_ = lean_ctor_get(v_s_2380_, 5);
v_addFn_x3f_2387_ = lean_ctor_get(v_s_2380_, 6);
v_mulFn_x3f_2388_ = lean_ctor_get(v_s_2380_, 7);
v_subFn_x3f_2389_ = lean_ctor_get(v_s_2380_, 8);
v_negFn_x3f_2390_ = lean_ctor_get(v_s_2380_, 9);
v_powFn_x3f_2391_ = lean_ctor_get(v_s_2380_, 10);
v_intCastFn_x3f_2392_ = lean_ctor_get(v_s_2380_, 11);
v_natCastFn_x3f_2393_ = lean_ctor_get(v_s_2380_, 12);
v_one_x3f_2394_ = lean_ctor_get(v_s_2380_, 13);
v_vars_2395_ = lean_ctor_get(v_s_2380_, 14);
v_varMap_2396_ = lean_ctor_get(v_s_2380_, 15);
v_denote_2397_ = lean_ctor_get(v_s_2380_, 16);
v_isSharedCheck_2406_ = !lean_is_exclusive(v_s_2380_);
if (v_isSharedCheck_2406_ == 0)
{
v___x_2399_ = v_s_2380_;
v_isShared_2400_ = v_isSharedCheck_2406_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_denote_2397_);
lean_inc(v_varMap_2396_);
lean_inc(v_vars_2395_);
lean_inc(v_one_x3f_2394_);
lean_inc(v_natCastFn_x3f_2393_);
lean_inc(v_intCastFn_x3f_2392_);
lean_inc(v_powFn_x3f_2391_);
lean_inc(v_negFn_x3f_2390_);
lean_inc(v_subFn_x3f_2389_);
lean_inc(v_mulFn_x3f_2388_);
lean_inc(v_addFn_x3f_2387_);
lean_inc(v_charInst_x3f_2386_);
lean_inc(v_semiringInst_2385_);
lean_inc(v_ringInst_2384_);
lean_inc(v_u_2383_);
lean_inc(v_type_2382_);
lean_inc(v_id_2381_);
lean_dec(v_s_2380_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2406_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2404_; 
lean_inc_ref(v_e_2376_);
v___x_2401_ = l_Lean_PersistentArray_push___redArg(v_vars_2395_, v_e_2376_);
v___x_2402_ = l_Lean_PersistentHashMap_insert___redArg(v___f_2377_, v___f_2378_, v_varMap_2396_, v_e_2376_, v_size_2379_);
if (v_isShared_2400_ == 0)
{
lean_ctor_set(v___x_2399_, 15, v___x_2402_);
lean_ctor_set(v___x_2399_, 14, v___x_2401_);
v___x_2404_ = v___x_2399_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v_id_2381_);
lean_ctor_set(v_reuseFailAlloc_2405_, 1, v_type_2382_);
lean_ctor_set(v_reuseFailAlloc_2405_, 2, v_u_2383_);
lean_ctor_set(v_reuseFailAlloc_2405_, 3, v_ringInst_2384_);
lean_ctor_set(v_reuseFailAlloc_2405_, 4, v_semiringInst_2385_);
lean_ctor_set(v_reuseFailAlloc_2405_, 5, v_charInst_x3f_2386_);
lean_ctor_set(v_reuseFailAlloc_2405_, 6, v_addFn_x3f_2387_);
lean_ctor_set(v_reuseFailAlloc_2405_, 7, v_mulFn_x3f_2388_);
lean_ctor_set(v_reuseFailAlloc_2405_, 8, v_subFn_x3f_2389_);
lean_ctor_set(v_reuseFailAlloc_2405_, 9, v_negFn_x3f_2390_);
lean_ctor_set(v_reuseFailAlloc_2405_, 10, v_powFn_x3f_2391_);
lean_ctor_set(v_reuseFailAlloc_2405_, 11, v_intCastFn_x3f_2392_);
lean_ctor_set(v_reuseFailAlloc_2405_, 12, v_natCastFn_x3f_2393_);
lean_ctor_set(v_reuseFailAlloc_2405_, 13, v_one_x3f_2394_);
lean_ctor_set(v_reuseFailAlloc_2405_, 14, v___x_2401_);
lean_ctor_set(v_reuseFailAlloc_2405_, 15, v___x_2402_);
lean_ctor_set(v_reuseFailAlloc_2405_, 16, v_denote_2397_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__1(lean_object* v_toPure_2407_, lean_object* v_size_2408_, lean_object* v_____r_2409_){
_start:
{
lean_object* v___x_2410_; 
v___x_2410_ = lean_apply_2(v_toPure_2407_, lean_box(0), v_size_2408_);
return v___x_2410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__2(lean_object* v_e_2411_, lean_object* v_inst_2412_, lean_object* v_toBind_2413_, lean_object* v___f_2414_, lean_object* v_____r_2415_){
_start:
{
lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; 
v___x_2416_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_2417_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_SolverExtension_markTerm___boxed), 14, 3);
lean_closure_set(v___x_2417_, 0, lean_box(0));
lean_closure_set(v___x_2417_, 1, v___x_2416_);
lean_closure_set(v___x_2417_, 2, v_e_2411_);
v___x_2418_ = lean_apply_2(v_inst_2412_, lean_box(0), v___x_2417_);
v___x_2419_ = lean_apply_4(v_toBind_2413_, lean_box(0), lean_box(0), v___x_2418_, v___f_2414_);
return v___x_2419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__3(lean_object* v_inst_2420_, lean_object* v_e_2421_, lean_object* v_toBind_2422_, lean_object* v___f_2423_, lean_object* v_____r_2424_){
_start:
{
lean_object* v___x_2425_; lean_object* v___x_2426_; 
v___x_2425_ = lean_apply_1(v_inst_2420_, v_e_2421_);
v___x_2426_ = lean_apply_4(v_toBind_2422_, lean_box(0), lean_box(0), v___x_2425_, v___f_2423_);
return v___x_2426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__4(lean_object* v___f_2427_, lean_object* v___f_2428_, lean_object* v_e_2429_, lean_object* v_toPure_2430_, lean_object* v_inst_2431_, lean_object* v_toBind_2432_, lean_object* v_inst_2433_, lean_object* v_modifyRing_2434_, lean_object* v_s_2435_){
_start:
{
lean_object* v_vars_2436_; lean_object* v_varMap_2437_; lean_object* v___x_2438_; 
v_vars_2436_ = lean_ctor_get(v_s_2435_, 14);
lean_inc_ref(v_vars_2436_);
v_varMap_2437_ = lean_ctor_get(v_s_2435_, 15);
lean_inc_ref(v_varMap_2437_);
lean_dec_ref(v_s_2435_);
lean_inc_ref(v_e_2429_);
lean_inc_ref(v___f_2428_);
lean_inc_ref(v___f_2427_);
v___x_2438_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___f_2427_, v___f_2428_, v_varMap_2437_, v_e_2429_);
lean_dec_ref(v_varMap_2437_);
if (lean_obj_tag(v___x_2438_) == 1)
{
lean_object* v_val_2439_; lean_object* v___x_2440_; 
lean_dec_ref(v_vars_2436_);
lean_dec(v_modifyRing_2434_);
lean_dec(v_inst_2433_);
lean_dec(v_toBind_2432_);
lean_dec(v_inst_2431_);
lean_dec_ref(v_e_2429_);
lean_dec_ref(v___f_2428_);
lean_dec_ref(v___f_2427_);
v_val_2439_ = lean_ctor_get(v___x_2438_, 0);
lean_inc(v_val_2439_);
lean_dec_ref(v___x_2438_);
v___x_2440_ = lean_apply_2(v_toPure_2430_, lean_box(0), v_val_2439_);
return v___x_2440_;
}
else
{
lean_object* v_size_2441_; lean_object* v___f_2442_; lean_object* v___f_2443_; lean_object* v___f_2444_; lean_object* v___f_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; 
lean_dec(v___x_2438_);
v_size_2441_ = lean_ctor_get(v_vars_2436_, 2);
lean_inc_n(v_size_2441_, 2);
lean_dec_ref(v_vars_2436_);
lean_inc_ref_n(v_e_2429_, 2);
v___f_2442_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2442_, 0, v_e_2429_);
lean_closure_set(v___f_2442_, 1, v___f_2427_);
lean_closure_set(v___f_2442_, 2, v___f_2428_);
lean_closure_set(v___f_2442_, 3, v_size_2441_);
v___f_2443_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2443_, 0, v_toPure_2430_);
lean_closure_set(v___f_2443_, 1, v_size_2441_);
lean_inc_n(v_toBind_2432_, 2);
v___f_2444_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__2), 5, 4);
lean_closure_set(v___f_2444_, 0, v_e_2429_);
lean_closure_set(v___f_2444_, 1, v_inst_2431_);
lean_closure_set(v___f_2444_, 2, v_toBind_2432_);
lean_closure_set(v___f_2444_, 3, v___f_2443_);
v___f_2445_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__3), 5, 4);
lean_closure_set(v___f_2445_, 0, v_inst_2433_);
lean_closure_set(v___f_2445_, 1, v_e_2429_);
lean_closure_set(v___f_2445_, 2, v_toBind_2432_);
lean_closure_set(v___f_2445_, 3, v___f_2444_);
v___x_2446_ = lean_apply_1(v_modifyRing_2434_, v___f_2442_);
v___x_2447_ = lean_apply_4(v_toBind_2432_, lean_box(0), lean_box(0), v___x_2446_, v___f_2445_);
return v___x_2447_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg(lean_object* v_inst_2450_, lean_object* v_inst_2451_, lean_object* v_inst_2452_, lean_object* v_inst_2453_, lean_object* v_e_2454_){
_start:
{
lean_object* v_toApplicative_2455_; lean_object* v_toBind_2456_; lean_object* v_getRing_2457_; lean_object* v_modifyRing_2458_; lean_object* v_toPure_2459_; lean_object* v___f_2460_; lean_object* v___f_2461_; lean_object* v___f_2462_; lean_object* v___x_2463_; 
v_toApplicative_2455_ = lean_ctor_get(v_inst_2451_, 0);
lean_inc_ref(v_toApplicative_2455_);
v_toBind_2456_ = lean_ctor_get(v_inst_2451_, 1);
lean_inc_n(v_toBind_2456_, 2);
lean_dec_ref(v_inst_2451_);
v_getRing_2457_ = lean_ctor_get(v_inst_2452_, 0);
lean_inc(v_getRing_2457_);
v_modifyRing_2458_ = lean_ctor_get(v_inst_2452_, 1);
lean_inc(v_modifyRing_2458_);
lean_dec_ref(v_inst_2452_);
v_toPure_2459_ = lean_ctor_get(v_toApplicative_2455_, 1);
lean_inc(v_toPure_2459_);
lean_dec_ref(v_toApplicative_2455_);
v___f_2460_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___closed__0));
v___f_2461_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___closed__1));
v___f_2462_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg___lam__4), 9, 8);
lean_closure_set(v___f_2462_, 0, v___f_2460_);
lean_closure_set(v___f_2462_, 1, v___f_2461_);
lean_closure_set(v___f_2462_, 2, v_e_2454_);
lean_closure_set(v___f_2462_, 3, v_toPure_2459_);
lean_closure_set(v___f_2462_, 4, v_inst_2450_);
lean_closure_set(v___f_2462_, 5, v_toBind_2456_);
lean_closure_set(v___f_2462_, 6, v_inst_2453_);
lean_closure_set(v___f_2462_, 7, v_modifyRing_2458_);
v___x_2463_ = lean_apply_4(v_toBind_2456_, lean_box(0), lean_box(0), v_getRing_2457_, v___f_2462_);
return v___x_2463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore(lean_object* v_m_2464_, lean_object* v_inst_2465_, lean_object* v_inst_2466_, lean_object* v_inst_2467_, lean_object* v_inst_2468_, lean_object* v_e_2469_){
_start:
{
lean_object* v___x_2470_; 
v___x_2470_ = l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___redArg(v_inst_2465_, v_inst_2466_, v_inst_2467_, v_inst_2468_, v_e_2469_);
return v___x_2470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___lam__0(lean_object* v_e_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_){
_start:
{
lean_object* v___x_2484_; 
v___x_2484_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(v_e_2471_, v___y_2472_, v___y_2473_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_);
return v___x_2484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___lam__0___boxed(lean_object* v_e_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_){
_start:
{
lean_object* v_res_2498_; 
v_res_2498_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdRingM___lam__0(v_e_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_);
lean_dec(v___y_2496_);
lean_dec_ref(v___y_2495_);
lean_dec(v___y_2494_);
lean_dec_ref(v___y_2493_);
lean_dec(v___y_2492_);
lean_dec_ref(v___y_2491_);
lean_dec(v___y_2490_);
lean_dec_ref(v___y_2489_);
lean_dec(v___y_2488_);
lean_dec(v___y_2487_);
lean_dec_ref(v___y_2486_);
return v_res_2498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkVar_spec__0___lam__0(lean_object* v_e_2501_, lean_object* v_size_2502_, lean_object* v_s_2503_){
_start:
{
lean_object* v_toRing_2504_; lean_object* v_invFn_x3f_2505_; lean_object* v_semiringId_x3f_2506_; lean_object* v_commSemiringInst_2507_; lean_object* v_commRingInst_2508_; lean_object* v_noZeroDivInst_x3f_2509_; lean_object* v_fieldInst_x3f_2510_; lean_object* v_powIdentityInst_x3f_2511_; lean_object* v_denoteEntries_2512_; lean_object* v_nextId_2513_; lean_object* v_steps_2514_; lean_object* v_queue_2515_; lean_object* v_basis_2516_; lean_object* v_diseqs_2517_; uint8_t v_recheck_2518_; lean_object* v_invSet_2519_; lean_object* v_powIdentityVarCount_2520_; lean_object* v_numEq0_x3f_2521_; uint8_t v_numEq0Updated_2522_; lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2555_; 
v_toRing_2504_ = lean_ctor_get(v_s_2503_, 0);
v_invFn_x3f_2505_ = lean_ctor_get(v_s_2503_, 1);
v_semiringId_x3f_2506_ = lean_ctor_get(v_s_2503_, 2);
v_commSemiringInst_2507_ = lean_ctor_get(v_s_2503_, 3);
v_commRingInst_2508_ = lean_ctor_get(v_s_2503_, 4);
v_noZeroDivInst_x3f_2509_ = lean_ctor_get(v_s_2503_, 5);
v_fieldInst_x3f_2510_ = lean_ctor_get(v_s_2503_, 6);
v_powIdentityInst_x3f_2511_ = lean_ctor_get(v_s_2503_, 7);
v_denoteEntries_2512_ = lean_ctor_get(v_s_2503_, 8);
v_nextId_2513_ = lean_ctor_get(v_s_2503_, 9);
v_steps_2514_ = lean_ctor_get(v_s_2503_, 10);
v_queue_2515_ = lean_ctor_get(v_s_2503_, 11);
v_basis_2516_ = lean_ctor_get(v_s_2503_, 12);
v_diseqs_2517_ = lean_ctor_get(v_s_2503_, 13);
v_recheck_2518_ = lean_ctor_get_uint8(v_s_2503_, sizeof(void*)*17);
v_invSet_2519_ = lean_ctor_get(v_s_2503_, 14);
v_powIdentityVarCount_2520_ = lean_ctor_get(v_s_2503_, 15);
v_numEq0_x3f_2521_ = lean_ctor_get(v_s_2503_, 16);
v_numEq0Updated_2522_ = lean_ctor_get_uint8(v_s_2503_, sizeof(void*)*17 + 1);
v_isSharedCheck_2555_ = !lean_is_exclusive(v_s_2503_);
if (v_isSharedCheck_2555_ == 0)
{
v___x_2524_ = v_s_2503_;
v_isShared_2525_ = v_isSharedCheck_2555_;
goto v_resetjp_2523_;
}
else
{
lean_inc(v_numEq0_x3f_2521_);
lean_inc(v_powIdentityVarCount_2520_);
lean_inc(v_invSet_2519_);
lean_inc(v_diseqs_2517_);
lean_inc(v_basis_2516_);
lean_inc(v_queue_2515_);
lean_inc(v_steps_2514_);
lean_inc(v_nextId_2513_);
lean_inc(v_denoteEntries_2512_);
lean_inc(v_powIdentityInst_x3f_2511_);
lean_inc(v_fieldInst_x3f_2510_);
lean_inc(v_noZeroDivInst_x3f_2509_);
lean_inc(v_commRingInst_2508_);
lean_inc(v_commSemiringInst_2507_);
lean_inc(v_semiringId_x3f_2506_);
lean_inc(v_invFn_x3f_2505_);
lean_inc(v_toRing_2504_);
lean_dec(v_s_2503_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_2555_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
lean_object* v_id_2526_; lean_object* v_type_2527_; lean_object* v_u_2528_; lean_object* v_ringInst_2529_; lean_object* v_semiringInst_2530_; lean_object* v_charInst_x3f_2531_; lean_object* v_addFn_x3f_2532_; lean_object* v_mulFn_x3f_2533_; lean_object* v_subFn_x3f_2534_; lean_object* v_negFn_x3f_2535_; lean_object* v_powFn_x3f_2536_; lean_object* v_intCastFn_x3f_2537_; lean_object* v_natCastFn_x3f_2538_; lean_object* v_one_x3f_2539_; lean_object* v_vars_2540_; lean_object* v_varMap_2541_; lean_object* v_denote_2542_; lean_object* v___x_2544_; uint8_t v_isShared_2545_; uint8_t v_isSharedCheck_2554_; 
v_id_2526_ = lean_ctor_get(v_toRing_2504_, 0);
v_type_2527_ = lean_ctor_get(v_toRing_2504_, 1);
v_u_2528_ = lean_ctor_get(v_toRing_2504_, 2);
v_ringInst_2529_ = lean_ctor_get(v_toRing_2504_, 3);
v_semiringInst_2530_ = lean_ctor_get(v_toRing_2504_, 4);
v_charInst_x3f_2531_ = lean_ctor_get(v_toRing_2504_, 5);
v_addFn_x3f_2532_ = lean_ctor_get(v_toRing_2504_, 6);
v_mulFn_x3f_2533_ = lean_ctor_get(v_toRing_2504_, 7);
v_subFn_x3f_2534_ = lean_ctor_get(v_toRing_2504_, 8);
v_negFn_x3f_2535_ = lean_ctor_get(v_toRing_2504_, 9);
v_powFn_x3f_2536_ = lean_ctor_get(v_toRing_2504_, 10);
v_intCastFn_x3f_2537_ = lean_ctor_get(v_toRing_2504_, 11);
v_natCastFn_x3f_2538_ = lean_ctor_get(v_toRing_2504_, 12);
v_one_x3f_2539_ = lean_ctor_get(v_toRing_2504_, 13);
v_vars_2540_ = lean_ctor_get(v_toRing_2504_, 14);
v_varMap_2541_ = lean_ctor_get(v_toRing_2504_, 15);
v_denote_2542_ = lean_ctor_get(v_toRing_2504_, 16);
v_isSharedCheck_2554_ = !lean_is_exclusive(v_toRing_2504_);
if (v_isSharedCheck_2554_ == 0)
{
v___x_2544_ = v_toRing_2504_;
v_isShared_2545_ = v_isSharedCheck_2554_;
goto v_resetjp_2543_;
}
else
{
lean_inc(v_denote_2542_);
lean_inc(v_varMap_2541_);
lean_inc(v_vars_2540_);
lean_inc(v_one_x3f_2539_);
lean_inc(v_natCastFn_x3f_2538_);
lean_inc(v_intCastFn_x3f_2537_);
lean_inc(v_powFn_x3f_2536_);
lean_inc(v_negFn_x3f_2535_);
lean_inc(v_subFn_x3f_2534_);
lean_inc(v_mulFn_x3f_2533_);
lean_inc(v_addFn_x3f_2532_);
lean_inc(v_charInst_x3f_2531_);
lean_inc(v_semiringInst_2530_);
lean_inc(v_ringInst_2529_);
lean_inc(v_u_2528_);
lean_inc(v_type_2527_);
lean_inc(v_id_2526_);
lean_dec(v_toRing_2504_);
v___x_2544_ = lean_box(0);
v_isShared_2545_ = v_isSharedCheck_2554_;
goto v_resetjp_2543_;
}
v_resetjp_2543_:
{
lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2549_; 
lean_inc_ref(v_e_2501_);
v___x_2546_ = l_Lean_PersistentArray_push___redArg(v_vars_2540_, v_e_2501_);
v___x_2547_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermRingId_spec__0___redArg(v_varMap_2541_, v_e_2501_, v_size_2502_);
if (v_isShared_2545_ == 0)
{
lean_ctor_set(v___x_2544_, 15, v___x_2547_);
lean_ctor_set(v___x_2544_, 14, v___x_2546_);
v___x_2549_ = v___x_2544_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v_id_2526_);
lean_ctor_set(v_reuseFailAlloc_2553_, 1, v_type_2527_);
lean_ctor_set(v_reuseFailAlloc_2553_, 2, v_u_2528_);
lean_ctor_set(v_reuseFailAlloc_2553_, 3, v_ringInst_2529_);
lean_ctor_set(v_reuseFailAlloc_2553_, 4, v_semiringInst_2530_);
lean_ctor_set(v_reuseFailAlloc_2553_, 5, v_charInst_x3f_2531_);
lean_ctor_set(v_reuseFailAlloc_2553_, 6, v_addFn_x3f_2532_);
lean_ctor_set(v_reuseFailAlloc_2553_, 7, v_mulFn_x3f_2533_);
lean_ctor_set(v_reuseFailAlloc_2553_, 8, v_subFn_x3f_2534_);
lean_ctor_set(v_reuseFailAlloc_2553_, 9, v_negFn_x3f_2535_);
lean_ctor_set(v_reuseFailAlloc_2553_, 10, v_powFn_x3f_2536_);
lean_ctor_set(v_reuseFailAlloc_2553_, 11, v_intCastFn_x3f_2537_);
lean_ctor_set(v_reuseFailAlloc_2553_, 12, v_natCastFn_x3f_2538_);
lean_ctor_set(v_reuseFailAlloc_2553_, 13, v_one_x3f_2539_);
lean_ctor_set(v_reuseFailAlloc_2553_, 14, v___x_2546_);
lean_ctor_set(v_reuseFailAlloc_2553_, 15, v___x_2547_);
lean_ctor_set(v_reuseFailAlloc_2553_, 16, v_denote_2542_);
v___x_2549_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
lean_object* v___x_2551_; 
if (v_isShared_2525_ == 0)
{
lean_ctor_set(v___x_2524_, 0, v___x_2549_);
v___x_2551_ = v___x_2524_;
goto v_reusejp_2550_;
}
else
{
lean_object* v_reuseFailAlloc_2552_; 
v_reuseFailAlloc_2552_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_2552_, 0, v___x_2549_);
lean_ctor_set(v_reuseFailAlloc_2552_, 1, v_invFn_x3f_2505_);
lean_ctor_set(v_reuseFailAlloc_2552_, 2, v_semiringId_x3f_2506_);
lean_ctor_set(v_reuseFailAlloc_2552_, 3, v_commSemiringInst_2507_);
lean_ctor_set(v_reuseFailAlloc_2552_, 4, v_commRingInst_2508_);
lean_ctor_set(v_reuseFailAlloc_2552_, 5, v_noZeroDivInst_x3f_2509_);
lean_ctor_set(v_reuseFailAlloc_2552_, 6, v_fieldInst_x3f_2510_);
lean_ctor_set(v_reuseFailAlloc_2552_, 7, v_powIdentityInst_x3f_2511_);
lean_ctor_set(v_reuseFailAlloc_2552_, 8, v_denoteEntries_2512_);
lean_ctor_set(v_reuseFailAlloc_2552_, 9, v_nextId_2513_);
lean_ctor_set(v_reuseFailAlloc_2552_, 10, v_steps_2514_);
lean_ctor_set(v_reuseFailAlloc_2552_, 11, v_queue_2515_);
lean_ctor_set(v_reuseFailAlloc_2552_, 12, v_basis_2516_);
lean_ctor_set(v_reuseFailAlloc_2552_, 13, v_diseqs_2517_);
lean_ctor_set(v_reuseFailAlloc_2552_, 14, v_invSet_2519_);
lean_ctor_set(v_reuseFailAlloc_2552_, 15, v_powIdentityVarCount_2520_);
lean_ctor_set(v_reuseFailAlloc_2552_, 16, v_numEq0_x3f_2521_);
lean_ctor_set_uint8(v_reuseFailAlloc_2552_, sizeof(void*)*17, v_recheck_2518_);
lean_ctor_set_uint8(v_reuseFailAlloc_2552_, sizeof(void*)*17 + 1, v_numEq0Updated_2522_);
v___x_2551_ = v_reuseFailAlloc_2552_;
goto v_reusejp_2550_;
}
v_reusejp_2550_:
{
return v___x_2551_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkVar_spec__0(lean_object* v_e_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_){
_start:
{
lean_object* v___x_2569_; 
v___x_2569_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_);
if (lean_obj_tag(v___x_2569_) == 0)
{
lean_object* v_a_2570_; lean_object* v___x_2572_; uint8_t v_isShared_2573_; uint8_t v_isSharedCheck_2620_; 
v_a_2570_ = lean_ctor_get(v___x_2569_, 0);
v_isSharedCheck_2620_ = !lean_is_exclusive(v___x_2569_);
if (v_isSharedCheck_2620_ == 0)
{
v___x_2572_ = v___x_2569_;
v_isShared_2573_ = v_isSharedCheck_2620_;
goto v_resetjp_2571_;
}
else
{
lean_inc(v_a_2570_);
lean_dec(v___x_2569_);
v___x_2572_ = lean_box(0);
v_isShared_2573_ = v_isSharedCheck_2620_;
goto v_resetjp_2571_;
}
v_resetjp_2571_:
{
lean_object* v_toRing_2574_; lean_object* v_vars_2575_; lean_object* v_varMap_2576_; lean_object* v___x_2577_; 
v_toRing_2574_ = lean_ctor_get(v_a_2570_, 0);
lean_inc_ref(v_toRing_2574_);
lean_dec(v_a_2570_);
v_vars_2575_ = lean_ctor_get(v_toRing_2574_, 14);
lean_inc_ref(v_vars_2575_);
v_varMap_2576_ = lean_ctor_get(v_toRing_2574_, 15);
lean_inc_ref(v_varMap_2576_);
lean_dec_ref(v_toRing_2574_);
v___x_2577_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermRingId_x3f_spec__0___redArg(v_varMap_2576_, v_e_2556_);
lean_dec_ref(v_varMap_2576_);
if (lean_obj_tag(v___x_2577_) == 1)
{
lean_object* v_val_2578_; lean_object* v___x_2580_; 
lean_dec_ref(v_vars_2575_);
lean_dec_ref(v_e_2556_);
v_val_2578_ = lean_ctor_get(v___x_2577_, 0);
lean_inc(v_val_2578_);
lean_dec_ref(v___x_2577_);
if (v_isShared_2573_ == 0)
{
lean_ctor_set(v___x_2572_, 0, v_val_2578_);
v___x_2580_ = v___x_2572_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v_val_2578_);
v___x_2580_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
return v___x_2580_;
}
}
else
{
lean_object* v_size_2582_; lean_object* v___f_2583_; lean_object* v___x_2584_; 
lean_dec(v___x_2577_);
lean_del_object(v___x_2572_);
v_size_2582_ = lean_ctor_get(v_vars_2575_, 2);
lean_inc_n(v_size_2582_, 2);
lean_dec_ref(v_vars_2575_);
lean_inc_ref(v_e_2556_);
v___f_2583_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkVar_spec__0___lam__0), 3, 2);
lean_closure_set(v___f_2583_, 0, v_e_2556_);
lean_closure_set(v___f_2583_, 1, v_size_2582_);
v___x_2584_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_modifyCommRing___redArg(v___f_2583_, v___y_2557_, v___y_2558_);
if (lean_obj_tag(v___x_2584_) == 0)
{
lean_object* v___x_2585_; 
lean_dec_ref(v___x_2584_);
lean_inc_ref(v_e_2556_);
v___x_2585_ = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId___redArg(v_e_2556_, v___y_2557_, v___y_2558_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_);
if (lean_obj_tag(v___x_2585_) == 0)
{
lean_object* v___x_2586_; lean_object* v___x_2587_; 
lean_dec_ref(v___x_2585_);
v___x_2586_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_2587_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(v___x_2586_, v_e_2556_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_);
if (lean_obj_tag(v___x_2587_) == 0)
{
lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2594_; 
v_isSharedCheck_2594_ = !lean_is_exclusive(v___x_2587_);
if (v_isSharedCheck_2594_ == 0)
{
lean_object* v_unused_2595_; 
v_unused_2595_ = lean_ctor_get(v___x_2587_, 0);
lean_dec(v_unused_2595_);
v___x_2589_ = v___x_2587_;
v_isShared_2590_ = v_isSharedCheck_2594_;
goto v_resetjp_2588_;
}
else
{
lean_dec(v___x_2587_);
v___x_2589_ = lean_box(0);
v_isShared_2590_ = v_isSharedCheck_2594_;
goto v_resetjp_2588_;
}
v_resetjp_2588_:
{
lean_object* v___x_2592_; 
if (v_isShared_2590_ == 0)
{
lean_ctor_set(v___x_2589_, 0, v_size_2582_);
v___x_2592_ = v___x_2589_;
goto v_reusejp_2591_;
}
else
{
lean_object* v_reuseFailAlloc_2593_; 
v_reuseFailAlloc_2593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2593_, 0, v_size_2582_);
v___x_2592_ = v_reuseFailAlloc_2593_;
goto v_reusejp_2591_;
}
v_reusejp_2591_:
{
return v___x_2592_;
}
}
}
else
{
lean_object* v_a_2596_; lean_object* v___x_2598_; uint8_t v_isShared_2599_; uint8_t v_isSharedCheck_2603_; 
lean_dec(v_size_2582_);
v_a_2596_ = lean_ctor_get(v___x_2587_, 0);
v_isSharedCheck_2603_ = !lean_is_exclusive(v___x_2587_);
if (v_isSharedCheck_2603_ == 0)
{
v___x_2598_ = v___x_2587_;
v_isShared_2599_ = v_isSharedCheck_2603_;
goto v_resetjp_2597_;
}
else
{
lean_inc(v_a_2596_);
lean_dec(v___x_2587_);
v___x_2598_ = lean_box(0);
v_isShared_2599_ = v_isSharedCheck_2603_;
goto v_resetjp_2597_;
}
v_resetjp_2597_:
{
lean_object* v___x_2601_; 
if (v_isShared_2599_ == 0)
{
v___x_2601_ = v___x_2598_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2602_; 
v_reuseFailAlloc_2602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2602_, 0, v_a_2596_);
v___x_2601_ = v_reuseFailAlloc_2602_;
goto v_reusejp_2600_;
}
v_reusejp_2600_:
{
return v___x_2601_;
}
}
}
}
else
{
lean_object* v_a_2604_; lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2611_; 
lean_dec(v_size_2582_);
lean_dec_ref(v_e_2556_);
v_a_2604_ = lean_ctor_get(v___x_2585_, 0);
v_isSharedCheck_2611_ = !lean_is_exclusive(v___x_2585_);
if (v_isSharedCheck_2611_ == 0)
{
v___x_2606_ = v___x_2585_;
v_isShared_2607_ = v_isSharedCheck_2611_;
goto v_resetjp_2605_;
}
else
{
lean_inc(v_a_2604_);
lean_dec(v___x_2585_);
v___x_2606_ = lean_box(0);
v_isShared_2607_ = v_isSharedCheck_2611_;
goto v_resetjp_2605_;
}
v_resetjp_2605_:
{
lean_object* v___x_2609_; 
if (v_isShared_2607_ == 0)
{
v___x_2609_ = v___x_2606_;
goto v_reusejp_2608_;
}
else
{
lean_object* v_reuseFailAlloc_2610_; 
v_reuseFailAlloc_2610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2610_, 0, v_a_2604_);
v___x_2609_ = v_reuseFailAlloc_2610_;
goto v_reusejp_2608_;
}
v_reusejp_2608_:
{
return v___x_2609_;
}
}
}
}
else
{
lean_object* v_a_2612_; lean_object* v___x_2614_; uint8_t v_isShared_2615_; uint8_t v_isSharedCheck_2619_; 
lean_dec(v_size_2582_);
lean_dec_ref(v_e_2556_);
v_a_2612_ = lean_ctor_get(v___x_2584_, 0);
v_isSharedCheck_2619_ = !lean_is_exclusive(v___x_2584_);
if (v_isSharedCheck_2619_ == 0)
{
v___x_2614_ = v___x_2584_;
v_isShared_2615_ = v_isSharedCheck_2619_;
goto v_resetjp_2613_;
}
else
{
lean_inc(v_a_2612_);
lean_dec(v___x_2584_);
v___x_2614_ = lean_box(0);
v_isShared_2615_ = v_isSharedCheck_2619_;
goto v_resetjp_2613_;
}
v_resetjp_2613_:
{
lean_object* v___x_2617_; 
if (v_isShared_2615_ == 0)
{
v___x_2617_ = v___x_2614_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v_a_2612_);
v___x_2617_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
return v___x_2617_;
}
}
}
}
}
}
else
{
lean_object* v_a_2621_; lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2628_; 
lean_dec_ref(v_e_2556_);
v_a_2621_ = lean_ctor_get(v___x_2569_, 0);
v_isSharedCheck_2628_ = !lean_is_exclusive(v___x_2569_);
if (v_isSharedCheck_2628_ == 0)
{
v___x_2623_ = v___x_2569_;
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
else
{
lean_inc(v_a_2621_);
lean_dec(v___x_2569_);
v___x_2623_ = lean_box(0);
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
v_resetjp_2622_:
{
lean_object* v___x_2626_; 
if (v_isShared_2624_ == 0)
{
v___x_2626_ = v___x_2623_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v_a_2621_);
v___x_2626_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
return v___x_2626_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkVar_spec__0___boxed(lean_object* v_e_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_){
_start:
{
lean_object* v_res_2642_; 
v_res_2642_ = l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkVar_spec__0(v_e_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_);
lean_dec(v___y_2640_);
lean_dec_ref(v___y_2639_);
lean_dec(v___y_2638_);
lean_dec_ref(v___y_2637_);
lean_dec(v___y_2636_);
lean_dec_ref(v___y_2635_);
lean_dec(v___y_2634_);
lean_dec_ref(v___y_2633_);
lean_dec(v___y_2632_);
lean_dec(v___y_2631_);
lean_dec_ref(v___y_2630_);
return v_res_2642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVar(lean_object* v_e_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_){
_start:
{
lean_object* v___x_2656_; 
v___x_2656_ = l_Lean_Meta_Grind_Arith_CommRing_mkVarCore___at___00Lean_Meta_Grind_Arith_CommRing_mkVar_spec__0(v_e_2643_, v_a_2644_, v_a_2645_, v_a_2646_, v_a_2647_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_, v_a_2653_, v_a_2654_);
return v___x_2656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVar___boxed(lean_object* v_e_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_){
_start:
{
lean_object* v_res_2670_; 
v_res_2670_ = l_Lean_Meta_Grind_Arith_CommRing_mkVar(v_e_2657_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_, v_a_2662_, v_a_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_);
lean_dec(v_a_2668_);
lean_dec_ref(v_a_2667_);
lean_dec(v_a_2666_);
lean_dec_ref(v_a_2665_);
lean_dec(v_a_2664_);
lean_dec_ref(v_a_2663_);
lean_dec(v_a_2662_);
lean_dec_ref(v_a_2661_);
lean_dec(v_a_2660_);
lean_dec(v_a_2659_);
lean_dec_ref(v_a_2658_);
return v_res_2670_;
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
