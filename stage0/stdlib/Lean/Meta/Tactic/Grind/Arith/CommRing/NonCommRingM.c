// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.CommRing.NonCommRingM
// Imports: public import Lean.Meta.Tactic.Grind.Arith.CommRing.RingM
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
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_synthInstanceMeta_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_grind_canon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon___redArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_CommRing_ringExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Grind_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___lam__0___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___closed__0_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___lam__1___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___closed__0_value),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___closed__1_value)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "`grind` internal error, invalid ringId"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadRingNonCommRingM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingNonCommRingM___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadRingNonCommRingM___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instMonadRingNonCommRingM___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingNonCommRingM___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingNonCommRingM;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__2___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "expression in two different rings"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommRingM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommRingM___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommRingM___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommRingM = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommRingM___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_run___redArg(lean_object* v_ringId_1_, lean_object* v_x_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = lean_apply_12(v_x_2_, v_ringId_1_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_, v_a_10_, v_a_11_, v_a_12_, lean_box(0));
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_run___redArg___boxed(lean_object* v_ringId_15_, lean_object* v_x_16_, lean_object* v_a_17_, lean_object* v_a_18_, lean_object* v_a_19_, lean_object* v_a_20_, lean_object* v_a_21_, lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_, lean_object* v_a_25_, lean_object* v_a_26_, lean_object* v_a_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_run___redArg(v_ringId_15_, v_x_16_, v_a_17_, v_a_18_, v_a_19_, v_a_20_, v_a_21_, v_a_22_, v_a_23_, v_a_24_, v_a_25_, v_a_26_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_run(lean_object* v_00_u03b1_29_, lean_object* v_ringId_30_, lean_object* v_x_31_, lean_object* v_a_32_, lean_object* v_a_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = lean_apply_12(v_x_31_, v_ringId_30_, v_a_32_, v_a_33_, v_a_34_, v_a_35_, v_a_36_, v_a_37_, v_a_38_, v_a_39_, v_a_40_, v_a_41_, lean_box(0));
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_run___boxed(lean_object* v_00_u03b1_44_, lean_object* v_ringId_45_, lean_object* v_x_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_run(v_00_u03b1_44_, v_ringId_45_, v_x_46_, v_a_47_, v_a_48_, v_a_49_, v_a_50_, v_a_51_, v_a_52_, v_a_53_, v_a_54_, v_a_55_, v_a_56_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___lam__0(lean_object* v_e_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_){
_start:
{
lean_object* v___x_72_; 
lean_inc(v___y_66_);
v___x_72_ = lean_grind_canon(v_e_59_, v___y_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_, v___y_67_, v___y_68_, v___y_69_, v___y_70_);
if (lean_obj_tag(v___x_72_) == 0)
{
lean_object* v_a_73_; lean_object* v___x_74_; 
v_a_73_ = lean_ctor_get(v___x_72_, 0);
lean_inc(v_a_73_);
lean_dec_ref(v___x_72_);
v___x_74_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_73_, v___y_66_);
lean_dec(v___y_66_);
return v___x_74_;
}
else
{
lean_dec(v___y_66_);
return v___x_72_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___lam__0___boxed(lean_object* v_e_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___lam__0(v_e_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_, v___y_85_, v___y_86_);
lean_dec(v___y_76_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___lam__1(lean_object* v_e_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = l_Lean_Meta_Grind_synthInstanceMeta_x3f(v_e_89_, v___y_97_, v___y_98_, v___y_99_, v___y_100_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___lam__1___boxed(lean_object* v_e_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___lam__1(v_e_103_, v___y_104_, v___y_105_, v___y_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_);
lean_dec(v___y_110_);
lean_dec_ref(v___y_109_);
lean_dec(v___y_108_);
lean_dec_ref(v___y_107_);
lean_dec(v___y_106_);
lean_dec(v___y_105_);
lean_dec(v___y_104_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0_spec__0(lean_object* v_msgData_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_){
_start:
{
lean_object* v___x_129_; lean_object* v_env_130_; lean_object* v___x_131_; lean_object* v_mctx_132_; lean_object* v_lctx_133_; lean_object* v_options_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_129_ = lean_st_ref_get(v___y_127_);
v_env_130_ = lean_ctor_get(v___x_129_, 0);
lean_inc_ref(v_env_130_);
lean_dec(v___x_129_);
v___x_131_ = lean_st_ref_get(v___y_125_);
v_mctx_132_ = lean_ctor_get(v___x_131_, 0);
lean_inc_ref(v_mctx_132_);
lean_dec(v___x_131_);
v_lctx_133_ = lean_ctor_get(v___y_124_, 2);
v_options_134_ = lean_ctor_get(v___y_126_, 2);
lean_inc_ref(v_options_134_);
lean_inc_ref(v_lctx_133_);
v___x_135_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_135_, 0, v_env_130_);
lean_ctor_set(v___x_135_, 1, v_mctx_132_);
lean_ctor_set(v___x_135_, 2, v_lctx_133_);
lean_ctor_set(v___x_135_, 3, v_options_134_);
v___x_136_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_136_, 0, v___x_135_);
lean_ctor_set(v___x_136_, 1, v_msgData_123_);
v___x_137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_137_, 0, v___x_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0_spec__0___boxed(lean_object* v_msgData_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0_spec__0(v_msgData_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_);
lean_dec(v___y_142_);
lean_dec_ref(v___y_141_);
lean_dec(v___y_140_);
lean_dec_ref(v___y_139_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0___redArg(lean_object* v_msg_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_){
_start:
{
lean_object* v_ref_151_; lean_object* v___x_152_; lean_object* v_a_153_; lean_object* v___x_155_; uint8_t v_isShared_156_; uint8_t v_isSharedCheck_161_; 
v_ref_151_ = lean_ctor_get(v___y_148_, 5);
v___x_152_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0_spec__0(v_msg_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_);
v_a_153_ = lean_ctor_get(v___x_152_, 0);
v_isSharedCheck_161_ = !lean_is_exclusive(v___x_152_);
if (v_isSharedCheck_161_ == 0)
{
v___x_155_ = v___x_152_;
v_isShared_156_ = v_isSharedCheck_161_;
goto v_resetjp_154_;
}
else
{
lean_inc(v_a_153_);
lean_dec(v___x_152_);
v___x_155_ = lean_box(0);
v_isShared_156_ = v_isSharedCheck_161_;
goto v_resetjp_154_;
}
v_resetjp_154_:
{
lean_object* v___x_157_; lean_object* v___x_159_; 
lean_inc(v_ref_151_);
v___x_157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_157_, 0, v_ref_151_);
lean_ctor_set(v___x_157_, 1, v_a_153_);
if (v_isShared_156_ == 0)
{
lean_ctor_set_tag(v___x_155_, 1);
lean_ctor_set(v___x_155_, 0, v___x_157_);
v___x_159_ = v___x_155_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v___x_157_);
v___x_159_ = v_reuseFailAlloc_160_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
return v___x_159_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0___redArg___boxed(lean_object* v_msg_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0___redArg(v_msg_162_, v___y_163_, v___y_164_, v___y_165_, v___y_166_);
lean_dec(v___y_166_);
lean_dec_ref(v___y_165_);
lean_dec(v___y_164_);
lean_dec_ref(v___y_163_);
return v_res_168_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing___closed__1(void){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_170_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing___closed__0));
v___x_171_ = l_Lean_stringToMessageData(v___x_170_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing(lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_173_, v_a_181_);
if (lean_obj_tag(v___x_184_) == 0)
{
lean_object* v_a_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_198_; 
v_a_185_ = lean_ctor_get(v___x_184_, 0);
v_isSharedCheck_198_ = !lean_is_exclusive(v___x_184_);
if (v_isSharedCheck_198_ == 0)
{
v___x_187_ = v___x_184_;
v_isShared_188_ = v_isSharedCheck_198_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_a_185_);
lean_dec(v___x_184_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_198_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v_ncRings_189_; lean_object* v___x_190_; uint8_t v___x_191_; 
v_ncRings_189_ = lean_ctor_get(v_a_185_, 6);
lean_inc_ref(v_ncRings_189_);
lean_dec(v_a_185_);
v___x_190_ = lean_array_get_size(v_ncRings_189_);
v___x_191_ = lean_nat_dec_lt(v_a_172_, v___x_190_);
if (v___x_191_ == 0)
{
lean_object* v___x_192_; lean_object* v___x_193_; 
lean_dec_ref(v_ncRings_189_);
lean_del_object(v___x_187_);
v___x_192_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing___closed__1);
v___x_193_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0___redArg(v___x_192_, v_a_179_, v_a_180_, v_a_181_, v_a_182_);
return v___x_193_;
}
else
{
lean_object* v___x_194_; lean_object* v___x_196_; 
v___x_194_ = lean_array_fget(v_ncRings_189_, v_a_172_);
lean_dec_ref(v_ncRings_189_);
if (v_isShared_188_ == 0)
{
lean_ctor_set(v___x_187_, 0, v___x_194_);
v___x_196_ = v___x_187_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v___x_194_);
v___x_196_ = v_reuseFailAlloc_197_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
return v___x_196_;
}
}
}
}
else
{
lean_object* v_a_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_206_; 
v_a_199_ = lean_ctor_get(v___x_184_, 0);
v_isSharedCheck_206_ = !lean_is_exclusive(v___x_184_);
if (v_isSharedCheck_206_ == 0)
{
v___x_201_ = v___x_184_;
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_a_199_);
lean_dec(v___x_184_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v___x_204_; 
if (v_isShared_202_ == 0)
{
v___x_204_ = v___x_201_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v_a_199_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
return v___x_204_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing___boxed(lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing(v_a_207_, v_a_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_);
lean_dec(v_a_217_);
lean_dec_ref(v_a_216_);
lean_dec(v_a_215_);
lean_dec_ref(v_a_214_);
lean_dec(v_a_213_);
lean_dec_ref(v_a_212_);
lean_dec(v_a_211_);
lean_dec_ref(v_a_210_);
lean_dec(v_a_209_);
lean_dec(v_a_208_);
lean_dec(v_a_207_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0(lean_object* v_00_u03b1_220_, lean_object* v_msg_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0___redArg(v_msg_221_, v___y_229_, v___y_230_, v___y_231_, v___y_232_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0___boxed(lean_object* v_00_u03b1_235_, lean_object* v_msg_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0(v_00_u03b1_235_, v_msg_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_, v___y_246_, v___y_247_);
lean_dec(v___y_247_);
lean_dec_ref(v___y_246_);
lean_dec(v___y_245_);
lean_dec_ref(v___y_244_);
lean_dec(v___y_243_);
lean_dec_ref(v___y_242_);
lean_dec(v___y_241_);
lean_dec_ref(v___y_240_);
lean_dec(v___y_239_);
lean_dec(v___y_238_);
lean_dec(v___y_237_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg___lam__0(lean_object* v_a_250_, lean_object* v_f_251_, lean_object* v_s_252_){
_start:
{
lean_object* v_rings_253_; lean_object* v_typeIdOf_254_; lean_object* v_exprToRingId_255_; lean_object* v_semirings_256_; lean_object* v_stypeIdOf_257_; lean_object* v_exprToSemiringId_258_; lean_object* v_ncRings_259_; lean_object* v_exprToNCRingId_260_; lean_object* v_nctypeIdOf_261_; lean_object* v_ncSemirings_262_; lean_object* v_exprToNCSemiringId_263_; lean_object* v_ncstypeIdOf_264_; lean_object* v_steps_265_; lean_object* v___x_266_; uint8_t v___x_267_; 
v_rings_253_ = lean_ctor_get(v_s_252_, 0);
v_typeIdOf_254_ = lean_ctor_get(v_s_252_, 1);
v_exprToRingId_255_ = lean_ctor_get(v_s_252_, 2);
v_semirings_256_ = lean_ctor_get(v_s_252_, 3);
v_stypeIdOf_257_ = lean_ctor_get(v_s_252_, 4);
v_exprToSemiringId_258_ = lean_ctor_get(v_s_252_, 5);
v_ncRings_259_ = lean_ctor_get(v_s_252_, 6);
v_exprToNCRingId_260_ = lean_ctor_get(v_s_252_, 7);
v_nctypeIdOf_261_ = lean_ctor_get(v_s_252_, 8);
v_ncSemirings_262_ = lean_ctor_get(v_s_252_, 9);
v_exprToNCSemiringId_263_ = lean_ctor_get(v_s_252_, 10);
v_ncstypeIdOf_264_ = lean_ctor_get(v_s_252_, 11);
v_steps_265_ = lean_ctor_get(v_s_252_, 12);
v___x_266_ = lean_array_get_size(v_ncRings_259_);
v___x_267_ = lean_nat_dec_lt(v_a_250_, v___x_266_);
if (v___x_267_ == 0)
{
lean_dec_ref(v_f_251_);
return v_s_252_;
}
else
{
lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_279_; 
lean_inc(v_steps_265_);
lean_inc_ref(v_ncstypeIdOf_264_);
lean_inc_ref(v_exprToNCSemiringId_263_);
lean_inc_ref(v_ncSemirings_262_);
lean_inc_ref(v_nctypeIdOf_261_);
lean_inc_ref(v_exprToNCRingId_260_);
lean_inc_ref(v_ncRings_259_);
lean_inc_ref(v_exprToSemiringId_258_);
lean_inc_ref(v_stypeIdOf_257_);
lean_inc_ref(v_semirings_256_);
lean_inc_ref(v_exprToRingId_255_);
lean_inc_ref(v_typeIdOf_254_);
lean_inc_ref(v_rings_253_);
v_isSharedCheck_279_ = !lean_is_exclusive(v_s_252_);
if (v_isSharedCheck_279_ == 0)
{
lean_object* v_unused_280_; lean_object* v_unused_281_; lean_object* v_unused_282_; lean_object* v_unused_283_; lean_object* v_unused_284_; lean_object* v_unused_285_; lean_object* v_unused_286_; lean_object* v_unused_287_; lean_object* v_unused_288_; lean_object* v_unused_289_; lean_object* v_unused_290_; lean_object* v_unused_291_; lean_object* v_unused_292_; 
v_unused_280_ = lean_ctor_get(v_s_252_, 12);
lean_dec(v_unused_280_);
v_unused_281_ = lean_ctor_get(v_s_252_, 11);
lean_dec(v_unused_281_);
v_unused_282_ = lean_ctor_get(v_s_252_, 10);
lean_dec(v_unused_282_);
v_unused_283_ = lean_ctor_get(v_s_252_, 9);
lean_dec(v_unused_283_);
v_unused_284_ = lean_ctor_get(v_s_252_, 8);
lean_dec(v_unused_284_);
v_unused_285_ = lean_ctor_get(v_s_252_, 7);
lean_dec(v_unused_285_);
v_unused_286_ = lean_ctor_get(v_s_252_, 6);
lean_dec(v_unused_286_);
v_unused_287_ = lean_ctor_get(v_s_252_, 5);
lean_dec(v_unused_287_);
v_unused_288_ = lean_ctor_get(v_s_252_, 4);
lean_dec(v_unused_288_);
v_unused_289_ = lean_ctor_get(v_s_252_, 3);
lean_dec(v_unused_289_);
v_unused_290_ = lean_ctor_get(v_s_252_, 2);
lean_dec(v_unused_290_);
v_unused_291_ = lean_ctor_get(v_s_252_, 1);
lean_dec(v_unused_291_);
v_unused_292_ = lean_ctor_get(v_s_252_, 0);
lean_dec(v_unused_292_);
v___x_269_ = v_s_252_;
v_isShared_270_ = v_isSharedCheck_279_;
goto v_resetjp_268_;
}
else
{
lean_dec(v_s_252_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_279_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v_v_271_; lean_object* v___x_272_; lean_object* v_xs_x27_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_277_; 
v_v_271_ = lean_array_fget(v_ncRings_259_, v_a_250_);
v___x_272_ = lean_box(0);
v_xs_x27_273_ = lean_array_fset(v_ncRings_259_, v_a_250_, v___x_272_);
v___x_274_ = lean_apply_1(v_f_251_, v_v_271_);
v___x_275_ = lean_array_fset(v_xs_x27_273_, v_a_250_, v___x_274_);
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 6, v___x_275_);
v___x_277_ = v___x_269_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v_rings_253_);
lean_ctor_set(v_reuseFailAlloc_278_, 1, v_typeIdOf_254_);
lean_ctor_set(v_reuseFailAlloc_278_, 2, v_exprToRingId_255_);
lean_ctor_set(v_reuseFailAlloc_278_, 3, v_semirings_256_);
lean_ctor_set(v_reuseFailAlloc_278_, 4, v_stypeIdOf_257_);
lean_ctor_set(v_reuseFailAlloc_278_, 5, v_exprToSemiringId_258_);
lean_ctor_set(v_reuseFailAlloc_278_, 6, v___x_275_);
lean_ctor_set(v_reuseFailAlloc_278_, 7, v_exprToNCRingId_260_);
lean_ctor_set(v_reuseFailAlloc_278_, 8, v_nctypeIdOf_261_);
lean_ctor_set(v_reuseFailAlloc_278_, 9, v_ncSemirings_262_);
lean_ctor_set(v_reuseFailAlloc_278_, 10, v_exprToNCSemiringId_263_);
lean_ctor_set(v_reuseFailAlloc_278_, 11, v_ncstypeIdOf_264_);
lean_ctor_set(v_reuseFailAlloc_278_, 12, v_steps_265_);
v___x_277_ = v_reuseFailAlloc_278_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
return v___x_277_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg___lam__0___boxed(lean_object* v_a_293_, lean_object* v_f_294_, lean_object* v_s_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg___lam__0(v_a_293_, v_f_294_, v_s_295_);
lean_dec(v_a_293_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg(lean_object* v_f_297_, lean_object* v_a_298_, lean_object* v_a_299_){
_start:
{
lean_object* v___f_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
v___f_301_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_301_, 0, v_a_298_);
lean_closure_set(v___f_301_, 1, v_f_297_);
v___x_302_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_303_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_302_, v___f_301_, v_a_299_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg___boxed(lean_object* v_f_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg(v_f_304_, v_a_305_, v_a_306_);
lean_dec(v_a_306_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing(lean_object* v_f_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_){
_start:
{
lean_object* v___x_322_; 
v___x_322_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg(v_f_309_, v_a_310_, v_a_311_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___boxed(lean_object* v_f_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing(v_f_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_);
lean_dec(v_a_334_);
lean_dec_ref(v_a_333_);
lean_dec(v_a_332_);
lean_dec_ref(v_a_331_);
lean_dec(v_a_330_);
lean_dec_ref(v_a_329_);
lean_dec(v_a_328_);
lean_dec_ref(v_a_327_);
lean_dec(v_a_326_);
lean_dec(v_a_325_);
return v_res_336_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadRingNonCommRingM___closed__1(void){
_start:
{
lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_338_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadRingNonCommRingM___closed__0));
v___x_339_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing___boxed), 12, 0);
v___x_340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_340_, 0, v___x_339_);
lean_ctor_set(v___x_340_, 1, v___x_338_);
return v___x_340_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadRingNonCommRingM(void){
_start:
{
lean_object* v___x_341_; 
v___x_341_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadRingNonCommRingM___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instMonadRingNonCommRingM___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadRingNonCommRingM___closed__1);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_342_, lean_object* v_vals_343_, lean_object* v_i_344_, lean_object* v_k_345_){
_start:
{
lean_object* v___x_346_; uint8_t v___x_347_; 
v___x_346_ = lean_array_get_size(v_keys_342_);
v___x_347_ = lean_nat_dec_lt(v_i_344_, v___x_346_);
if (v___x_347_ == 0)
{
lean_object* v___x_348_; 
lean_dec(v_i_344_);
v___x_348_ = lean_box(0);
return v___x_348_;
}
else
{
lean_object* v_k_x27_349_; uint8_t v___x_350_; 
v_k_x27_349_ = lean_array_fget_borrowed(v_keys_342_, v_i_344_);
v___x_350_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_345_, v_k_x27_349_);
if (v___x_350_ == 0)
{
lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_351_ = lean_unsigned_to_nat(1u);
v___x_352_ = lean_nat_add(v_i_344_, v___x_351_);
lean_dec(v_i_344_);
v_i_344_ = v___x_352_;
goto _start;
}
else
{
lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_354_ = lean_array_fget_borrowed(v_vals_343_, v_i_344_);
lean_dec(v_i_344_);
lean_inc(v___x_354_);
v___x_355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_355_, 0, v___x_354_);
return v___x_355_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_356_, lean_object* v_vals_357_, lean_object* v_i_358_, lean_object* v_k_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_356_, v_vals_357_, v_i_358_, v_k_359_);
lean_dec_ref(v_k_359_);
lean_dec_ref(v_vals_357_);
lean_dec_ref(v_keys_356_);
return v_res_360_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_361_; size_t v___x_362_; size_t v___x_363_; 
v___x_361_ = ((size_t)5ULL);
v___x_362_ = ((size_t)1ULL);
v___x_363_ = lean_usize_shift_left(v___x_362_, v___x_361_);
return v___x_363_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_364_; size_t v___x_365_; size_t v___x_366_; 
v___x_364_ = ((size_t)1ULL);
v___x_365_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___redArg___closed__0);
v___x_366_ = lean_usize_sub(v___x_365_, v___x_364_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___redArg(lean_object* v_x_367_, size_t v_x_368_, lean_object* v_x_369_){
_start:
{
if (lean_obj_tag(v_x_367_) == 0)
{
lean_object* v_es_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_391_; 
v_es_370_ = lean_ctor_get(v_x_367_, 0);
v_isSharedCheck_391_ = !lean_is_exclusive(v_x_367_);
if (v_isSharedCheck_391_ == 0)
{
v___x_372_ = v_x_367_;
v_isShared_373_ = v_isSharedCheck_391_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_es_370_);
lean_dec(v_x_367_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_391_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_374_; size_t v___x_375_; size_t v___x_376_; size_t v___x_377_; lean_object* v_j_378_; lean_object* v___x_379_; 
v___x_374_ = lean_box(2);
v___x_375_ = ((size_t)5ULL);
v___x_376_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___redArg___closed__1);
v___x_377_ = lean_usize_land(v_x_368_, v___x_376_);
v_j_378_ = lean_usize_to_nat(v___x_377_);
v___x_379_ = lean_array_get(v___x_374_, v_es_370_, v_j_378_);
lean_dec(v_j_378_);
lean_dec_ref(v_es_370_);
switch(lean_obj_tag(v___x_379_))
{
case 0:
{
lean_object* v_key_380_; lean_object* v_val_381_; uint8_t v___x_382_; 
v_key_380_ = lean_ctor_get(v___x_379_, 0);
lean_inc(v_key_380_);
v_val_381_ = lean_ctor_get(v___x_379_, 1);
lean_inc(v_val_381_);
lean_dec_ref(v___x_379_);
v___x_382_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_369_, v_key_380_);
lean_dec(v_key_380_);
if (v___x_382_ == 0)
{
lean_object* v___x_383_; 
lean_dec(v_val_381_);
lean_del_object(v___x_372_);
v___x_383_ = lean_box(0);
return v___x_383_;
}
else
{
lean_object* v___x_385_; 
if (v_isShared_373_ == 0)
{
lean_ctor_set_tag(v___x_372_, 1);
lean_ctor_set(v___x_372_, 0, v_val_381_);
v___x_385_ = v___x_372_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v_val_381_);
v___x_385_ = v_reuseFailAlloc_386_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
return v___x_385_;
}
}
}
case 1:
{
lean_object* v_node_387_; size_t v___x_388_; 
lean_del_object(v___x_372_);
v_node_387_ = lean_ctor_get(v___x_379_, 0);
lean_inc(v_node_387_);
lean_dec_ref(v___x_379_);
v___x_388_ = lean_usize_shift_right(v_x_368_, v___x_375_);
v_x_367_ = v_node_387_;
v_x_368_ = v___x_388_;
goto _start;
}
default: 
{
lean_object* v___x_390_; 
lean_del_object(v___x_372_);
v___x_390_ = lean_box(0);
return v___x_390_;
}
}
}
}
else
{
lean_object* v_ks_392_; lean_object* v_vs_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v_ks_392_ = lean_ctor_get(v_x_367_, 0);
lean_inc_ref(v_ks_392_);
v_vs_393_ = lean_ctor_get(v_x_367_, 1);
lean_inc_ref(v_vs_393_);
lean_dec_ref(v_x_367_);
v___x_394_ = lean_unsigned_to_nat(0u);
v___x_395_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_392_, v_vs_393_, v___x_394_, v_x_369_);
lean_dec_ref(v_vs_393_);
lean_dec_ref(v_ks_392_);
return v___x_395_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_396_, lean_object* v_x_397_, lean_object* v_x_398_){
_start:
{
size_t v_x_960__boxed_399_; lean_object* v_res_400_; 
v_x_960__boxed_399_ = lean_unbox_usize(v_x_397_);
lean_dec(v_x_397_);
v_res_400_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___redArg(v_x_396_, v_x_960__boxed_399_, v_x_398_);
lean_dec_ref(v_x_398_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0___redArg(lean_object* v_x_401_, lean_object* v_x_402_){
_start:
{
uint64_t v___x_403_; size_t v___x_404_; lean_object* v___x_405_; 
v___x_403_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_402_);
v___x_404_ = lean_uint64_to_usize(v___x_403_);
v___x_405_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___redArg(v_x_401_, v___x_404_, v_x_402_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0___redArg___boxed(lean_object* v_x_406_, lean_object* v_x_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0___redArg(v_x_406_, v_x_407_);
lean_dec_ref(v_x_407_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f___redArg(lean_object* v_e_409_, lean_object* v_a_410_, lean_object* v_a_411_){
_start:
{
lean_object* v___x_413_; 
v___x_413_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_410_, v_a_411_);
if (lean_obj_tag(v___x_413_) == 0)
{
lean_object* v_a_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_423_; 
v_a_414_ = lean_ctor_get(v___x_413_, 0);
v_isSharedCheck_423_ = !lean_is_exclusive(v___x_413_);
if (v_isSharedCheck_423_ == 0)
{
v___x_416_ = v___x_413_;
v_isShared_417_ = v_isSharedCheck_423_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_a_414_);
lean_dec(v___x_413_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_423_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v_exprToNCRingId_418_; lean_object* v___x_419_; lean_object* v___x_421_; 
v_exprToNCRingId_418_ = lean_ctor_get(v_a_414_, 7);
lean_inc_ref(v_exprToNCRingId_418_);
lean_dec(v_a_414_);
v___x_419_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0___redArg(v_exprToNCRingId_418_, v_e_409_);
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 0, v___x_419_);
v___x_421_ = v___x_416_;
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
else
{
lean_object* v_a_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_431_; 
v_a_424_ = lean_ctor_get(v___x_413_, 0);
v_isSharedCheck_431_ = !lean_is_exclusive(v___x_413_);
if (v_isSharedCheck_431_ == 0)
{
v___x_426_ = v___x_413_;
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_a_424_);
lean_dec(v___x_413_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_429_; 
if (v_isShared_427_ == 0)
{
v___x_429_ = v___x_426_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_a_424_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f___redArg___boxed(lean_object* v_e_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f___redArg(v_e_432_, v_a_433_, v_a_434_);
lean_dec_ref(v_a_434_);
lean_dec(v_a_433_);
lean_dec_ref(v_e_432_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f(lean_object* v_e_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_){
_start:
{
lean_object* v___x_449_; 
v___x_449_ = l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f___redArg(v_e_437_, v_a_438_, v_a_446_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f___boxed(lean_object* v_e_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f(v_e_450_, v_a_451_, v_a_452_, v_a_453_, v_a_454_, v_a_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_, v_a_460_);
lean_dec(v_a_460_);
lean_dec_ref(v_a_459_);
lean_dec(v_a_458_);
lean_dec_ref(v_a_457_);
lean_dec(v_a_456_);
lean_dec_ref(v_a_455_);
lean_dec(v_a_454_);
lean_dec_ref(v_a_453_);
lean_dec(v_a_452_);
lean_dec(v_a_451_);
lean_dec_ref(v_e_450_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0(lean_object* v_00_u03b2_463_, lean_object* v_x_464_, lean_object* v_x_465_){
_start:
{
lean_object* v___x_466_; 
v___x_466_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0___redArg(v_x_464_, v_x_465_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0___boxed(lean_object* v_00_u03b2_467_, lean_object* v_x_468_, lean_object* v_x_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0(v_00_u03b2_467_, v_x_468_, v_x_469_);
lean_dec_ref(v_x_469_);
return v_res_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_471_, lean_object* v_x_472_, size_t v_x_473_, lean_object* v_x_474_){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___redArg(v_x_472_, v_x_473_, v_x_474_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_476_, lean_object* v_x_477_, lean_object* v_x_478_, lean_object* v_x_479_){
_start:
{
size_t v_x_1125__boxed_480_; lean_object* v_res_481_; 
v_x_1125__boxed_480_ = lean_unbox_usize(v_x_478_);
lean_dec(v_x_478_);
v_res_481_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0(v_00_u03b2_476_, v_x_477_, v_x_1125__boxed_480_, v_x_479_);
lean_dec_ref(v_x_479_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_482_, lean_object* v_keys_483_, lean_object* v_vals_484_, lean_object* v_heq_485_, lean_object* v_i_486_, lean_object* v_k_487_){
_start:
{
lean_object* v___x_488_; 
v___x_488_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_483_, v_vals_484_, v_i_486_, v_k_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_489_, lean_object* v_keys_490_, lean_object* v_vals_491_, lean_object* v_heq_492_, lean_object* v_i_493_, lean_object* v_k_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_489_, v_keys_490_, v_vals_491_, v_heq_492_, v_i_493_, v_k_494_);
lean_dec_ref(v_k_494_);
lean_dec_ref(v_vals_491_);
lean_dec_ref(v_keys_490_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_496_, lean_object* v_x_497_, lean_object* v_x_498_, lean_object* v_x_499_){
_start:
{
lean_object* v_ks_500_; lean_object* v_vs_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_525_; 
v_ks_500_ = lean_ctor_get(v_x_496_, 0);
v_vs_501_ = lean_ctor_get(v_x_496_, 1);
v_isSharedCheck_525_ = !lean_is_exclusive(v_x_496_);
if (v_isSharedCheck_525_ == 0)
{
v___x_503_ = v_x_496_;
v_isShared_504_ = v_isSharedCheck_525_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_vs_501_);
lean_inc(v_ks_500_);
lean_dec(v_x_496_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_525_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_505_; uint8_t v___x_506_; 
v___x_505_ = lean_array_get_size(v_ks_500_);
v___x_506_ = lean_nat_dec_lt(v_x_497_, v___x_505_);
if (v___x_506_ == 0)
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_510_; 
lean_dec(v_x_497_);
v___x_507_ = lean_array_push(v_ks_500_, v_x_498_);
v___x_508_ = lean_array_push(v_vs_501_, v_x_499_);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 1, v___x_508_);
lean_ctor_set(v___x_503_, 0, v___x_507_);
v___x_510_ = v___x_503_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v___x_507_);
lean_ctor_set(v_reuseFailAlloc_511_, 1, v___x_508_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
else
{
lean_object* v_k_x27_512_; uint8_t v___x_513_; 
v_k_x27_512_ = lean_array_fget_borrowed(v_ks_500_, v_x_497_);
v___x_513_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_498_, v_k_x27_512_);
if (v___x_513_ == 0)
{
lean_object* v___x_515_; 
if (v_isShared_504_ == 0)
{
v___x_515_ = v___x_503_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v_ks_500_);
lean_ctor_set(v_reuseFailAlloc_519_, 1, v_vs_501_);
v___x_515_ = v_reuseFailAlloc_519_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_516_ = lean_unsigned_to_nat(1u);
v___x_517_ = lean_nat_add(v_x_497_, v___x_516_);
lean_dec(v_x_497_);
v_x_496_ = v___x_515_;
v_x_497_ = v___x_517_;
goto _start;
}
}
else
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_523_; 
v___x_520_ = lean_array_fset(v_ks_500_, v_x_497_, v_x_498_);
v___x_521_ = lean_array_fset(v_vs_501_, v_x_497_, v_x_499_);
lean_dec(v_x_497_);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 1, v___x_521_);
lean_ctor_set(v___x_503_, 0, v___x_520_);
v___x_523_ = v___x_503_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v___x_520_);
lean_ctor_set(v_reuseFailAlloc_524_, 1, v___x_521_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__1___redArg(lean_object* v_n_526_, lean_object* v_k_527_, lean_object* v_v_528_){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_529_ = lean_unsigned_to_nat(0u);
v___x_530_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__1_spec__2___redArg(v_n_526_, v___x_529_, v_k_527_, v_v_528_);
return v___x_530_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg(lean_object* v_x_532_, size_t v_x_533_, size_t v_x_534_, lean_object* v_x_535_, lean_object* v_x_536_){
_start:
{
if (lean_obj_tag(v_x_532_) == 0)
{
lean_object* v_es_537_; size_t v___x_538_; size_t v___x_539_; size_t v___x_540_; size_t v___x_541_; lean_object* v_j_542_; lean_object* v___x_543_; uint8_t v___x_544_; 
v_es_537_ = lean_ctor_get(v_x_532_, 0);
v___x_538_ = ((size_t)5ULL);
v___x_539_ = ((size_t)1ULL);
v___x_540_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___redArg___closed__1);
v___x_541_ = lean_usize_land(v_x_533_, v___x_540_);
v_j_542_ = lean_usize_to_nat(v___x_541_);
v___x_543_ = lean_array_get_size(v_es_537_);
v___x_544_ = lean_nat_dec_lt(v_j_542_, v___x_543_);
if (v___x_544_ == 0)
{
lean_dec(v_j_542_);
lean_dec(v_x_536_);
lean_dec_ref(v_x_535_);
return v_x_532_;
}
else
{
lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_581_; 
lean_inc_ref(v_es_537_);
v_isSharedCheck_581_ = !lean_is_exclusive(v_x_532_);
if (v_isSharedCheck_581_ == 0)
{
lean_object* v_unused_582_; 
v_unused_582_ = lean_ctor_get(v_x_532_, 0);
lean_dec(v_unused_582_);
v___x_546_ = v_x_532_;
v_isShared_547_ = v_isSharedCheck_581_;
goto v_resetjp_545_;
}
else
{
lean_dec(v_x_532_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_581_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v_v_548_; lean_object* v___x_549_; lean_object* v_xs_x27_550_; lean_object* v___y_552_; 
v_v_548_ = lean_array_fget(v_es_537_, v_j_542_);
v___x_549_ = lean_box(0);
v_xs_x27_550_ = lean_array_fset(v_es_537_, v_j_542_, v___x_549_);
switch(lean_obj_tag(v_v_548_))
{
case 0:
{
lean_object* v_key_557_; lean_object* v_val_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_568_; 
v_key_557_ = lean_ctor_get(v_v_548_, 0);
v_val_558_ = lean_ctor_get(v_v_548_, 1);
v_isSharedCheck_568_ = !lean_is_exclusive(v_v_548_);
if (v_isSharedCheck_568_ == 0)
{
v___x_560_ = v_v_548_;
v_isShared_561_ = v_isSharedCheck_568_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_val_558_);
lean_inc(v_key_557_);
lean_dec(v_v_548_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_568_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
uint8_t v___x_562_; 
v___x_562_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_535_, v_key_557_);
if (v___x_562_ == 0)
{
lean_object* v___x_563_; lean_object* v___x_564_; 
lean_del_object(v___x_560_);
v___x_563_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_557_, v_val_558_, v_x_535_, v_x_536_);
v___x_564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_564_, 0, v___x_563_);
v___y_552_ = v___x_564_;
goto v___jp_551_;
}
else
{
lean_object* v___x_566_; 
lean_dec(v_val_558_);
lean_dec(v_key_557_);
if (v_isShared_561_ == 0)
{
lean_ctor_set(v___x_560_, 1, v_x_536_);
lean_ctor_set(v___x_560_, 0, v_x_535_);
v___x_566_ = v___x_560_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v_x_535_);
lean_ctor_set(v_reuseFailAlloc_567_, 1, v_x_536_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
v___y_552_ = v___x_566_;
goto v___jp_551_;
}
}
}
}
case 1:
{
lean_object* v_node_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_579_; 
v_node_569_ = lean_ctor_get(v_v_548_, 0);
v_isSharedCheck_579_ = !lean_is_exclusive(v_v_548_);
if (v_isSharedCheck_579_ == 0)
{
v___x_571_ = v_v_548_;
v_isShared_572_ = v_isSharedCheck_579_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_node_569_);
lean_dec(v_v_548_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_579_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
size_t v___x_573_; size_t v___x_574_; lean_object* v___x_575_; lean_object* v___x_577_; 
v___x_573_ = lean_usize_shift_right(v_x_533_, v___x_538_);
v___x_574_ = lean_usize_add(v_x_534_, v___x_539_);
v___x_575_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg(v_node_569_, v___x_573_, v___x_574_, v_x_535_, v_x_536_);
if (v_isShared_572_ == 0)
{
lean_ctor_set(v___x_571_, 0, v___x_575_);
v___x_577_ = v___x_571_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v___x_575_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
v___y_552_ = v___x_577_;
goto v___jp_551_;
}
}
}
default: 
{
lean_object* v___x_580_; 
v___x_580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_580_, 0, v_x_535_);
lean_ctor_set(v___x_580_, 1, v_x_536_);
v___y_552_ = v___x_580_;
goto v___jp_551_;
}
}
v___jp_551_:
{
lean_object* v___x_553_; lean_object* v___x_555_; 
v___x_553_ = lean_array_fset(v_xs_x27_550_, v_j_542_, v___y_552_);
lean_dec(v_j_542_);
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 0, v___x_553_);
v___x_555_ = v___x_546_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v___x_553_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
return v___x_555_;
}
}
}
}
}
else
{
lean_object* v_ks_583_; lean_object* v_vs_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_604_; 
v_ks_583_ = lean_ctor_get(v_x_532_, 0);
v_vs_584_ = lean_ctor_get(v_x_532_, 1);
v_isSharedCheck_604_ = !lean_is_exclusive(v_x_532_);
if (v_isSharedCheck_604_ == 0)
{
v___x_586_ = v_x_532_;
v_isShared_587_ = v_isSharedCheck_604_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_vs_584_);
lean_inc(v_ks_583_);
lean_dec(v_x_532_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_604_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_589_; 
if (v_isShared_587_ == 0)
{
v___x_589_ = v___x_586_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v_ks_583_);
lean_ctor_set(v_reuseFailAlloc_603_, 1, v_vs_584_);
v___x_589_ = v_reuseFailAlloc_603_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
lean_object* v_newNode_590_; uint8_t v___y_592_; size_t v___x_598_; uint8_t v___x_599_; 
v_newNode_590_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__1___redArg(v___x_589_, v_x_535_, v_x_536_);
v___x_598_ = ((size_t)7ULL);
v___x_599_ = lean_usize_dec_le(v___x_598_, v_x_534_);
if (v___x_599_ == 0)
{
lean_object* v___x_600_; lean_object* v___x_601_; uint8_t v___x_602_; 
v___x_600_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_590_);
v___x_601_ = lean_unsigned_to_nat(4u);
v___x_602_ = lean_nat_dec_lt(v___x_600_, v___x_601_);
lean_dec(v___x_600_);
v___y_592_ = v___x_602_;
goto v___jp_591_;
}
else
{
v___y_592_ = v___x_599_;
goto v___jp_591_;
}
v___jp_591_:
{
if (v___y_592_ == 0)
{
lean_object* v_ks_593_; lean_object* v_vs_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
v_ks_593_ = lean_ctor_get(v_newNode_590_, 0);
lean_inc_ref(v_ks_593_);
v_vs_594_ = lean_ctor_get(v_newNode_590_, 1);
lean_inc_ref(v_vs_594_);
lean_dec_ref(v_newNode_590_);
v___x_595_ = lean_unsigned_to_nat(0u);
v___x_596_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg___closed__0);
v___x_597_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__2___redArg(v_x_534_, v_ks_593_, v_vs_594_, v___x_595_, v___x_596_);
lean_dec_ref(v_vs_594_);
lean_dec_ref(v_ks_593_);
return v___x_597_;
}
else
{
return v_newNode_590_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__2___redArg(size_t v_depth_605_, lean_object* v_keys_606_, lean_object* v_vals_607_, lean_object* v_i_608_, lean_object* v_entries_609_){
_start:
{
lean_object* v___x_610_; uint8_t v___x_611_; 
v___x_610_ = lean_array_get_size(v_keys_606_);
v___x_611_ = lean_nat_dec_lt(v_i_608_, v___x_610_);
if (v___x_611_ == 0)
{
lean_dec(v_i_608_);
return v_entries_609_;
}
else
{
lean_object* v_k_612_; lean_object* v_v_613_; uint64_t v___x_614_; size_t v_h_615_; size_t v___x_616_; lean_object* v___x_617_; size_t v___x_618_; size_t v___x_619_; size_t v___x_620_; size_t v_h_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v_k_612_ = lean_array_fget_borrowed(v_keys_606_, v_i_608_);
v_v_613_ = lean_array_fget_borrowed(v_vals_607_, v_i_608_);
v___x_614_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_612_);
v_h_615_ = lean_uint64_to_usize(v___x_614_);
v___x_616_ = ((size_t)5ULL);
v___x_617_ = lean_unsigned_to_nat(1u);
v___x_618_ = ((size_t)1ULL);
v___x_619_ = lean_usize_sub(v_depth_605_, v___x_618_);
v___x_620_ = lean_usize_mul(v___x_616_, v___x_619_);
v_h_621_ = lean_usize_shift_right(v_h_615_, v___x_620_);
v___x_622_ = lean_nat_add(v_i_608_, v___x_617_);
lean_dec(v_i_608_);
lean_inc(v_v_613_);
lean_inc(v_k_612_);
v___x_623_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg(v_entries_609_, v_h_621_, v_depth_605_, v_k_612_, v_v_613_);
v_i_608_ = v___x_622_;
v_entries_609_ = v___x_623_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_625_, lean_object* v_keys_626_, lean_object* v_vals_627_, lean_object* v_i_628_, lean_object* v_entries_629_){
_start:
{
size_t v_depth_boxed_630_; lean_object* v_res_631_; 
v_depth_boxed_630_ = lean_unbox_usize(v_depth_625_);
lean_dec(v_depth_625_);
v_res_631_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__2___redArg(v_depth_boxed_630_, v_keys_626_, v_vals_627_, v_i_628_, v_entries_629_);
lean_dec_ref(v_vals_627_);
lean_dec_ref(v_keys_626_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg___boxed(lean_object* v_x_632_, lean_object* v_x_633_, lean_object* v_x_634_, lean_object* v_x_635_, lean_object* v_x_636_){
_start:
{
size_t v_x_9919__boxed_637_; size_t v_x_9920__boxed_638_; lean_object* v_res_639_; 
v_x_9919__boxed_637_ = lean_unbox_usize(v_x_633_);
lean_dec(v_x_633_);
v_x_9920__boxed_638_ = lean_unbox_usize(v_x_634_);
lean_dec(v_x_634_);
v_res_639_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg(v_x_632_, v_x_9919__boxed_637_, v_x_9920__boxed_638_, v_x_635_, v_x_636_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0___redArg(lean_object* v_x_640_, lean_object* v_x_641_, lean_object* v_x_642_){
_start:
{
uint64_t v___x_643_; size_t v___x_644_; size_t v___x_645_; lean_object* v___x_646_; 
v___x_643_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_641_);
v___x_644_ = lean_uint64_to_usize(v___x_643_);
v___x_645_ = ((size_t)1ULL);
v___x_646_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg(v_x_640_, v___x_644_, v___x_645_, v_x_641_, v_x_642_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___lam__0(lean_object* v_e_647_, lean_object* v_a_648_, lean_object* v_s_649_){
_start:
{
lean_object* v_rings_650_; lean_object* v_typeIdOf_651_; lean_object* v_exprToRingId_652_; lean_object* v_semirings_653_; lean_object* v_stypeIdOf_654_; lean_object* v_exprToSemiringId_655_; lean_object* v_ncRings_656_; lean_object* v_exprToNCRingId_657_; lean_object* v_nctypeIdOf_658_; lean_object* v_ncSemirings_659_; lean_object* v_exprToNCSemiringId_660_; lean_object* v_ncstypeIdOf_661_; lean_object* v_steps_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_670_; 
v_rings_650_ = lean_ctor_get(v_s_649_, 0);
v_typeIdOf_651_ = lean_ctor_get(v_s_649_, 1);
v_exprToRingId_652_ = lean_ctor_get(v_s_649_, 2);
v_semirings_653_ = lean_ctor_get(v_s_649_, 3);
v_stypeIdOf_654_ = lean_ctor_get(v_s_649_, 4);
v_exprToSemiringId_655_ = lean_ctor_get(v_s_649_, 5);
v_ncRings_656_ = lean_ctor_get(v_s_649_, 6);
v_exprToNCRingId_657_ = lean_ctor_get(v_s_649_, 7);
v_nctypeIdOf_658_ = lean_ctor_get(v_s_649_, 8);
v_ncSemirings_659_ = lean_ctor_get(v_s_649_, 9);
v_exprToNCSemiringId_660_ = lean_ctor_get(v_s_649_, 10);
v_ncstypeIdOf_661_ = lean_ctor_get(v_s_649_, 11);
v_steps_662_ = lean_ctor_get(v_s_649_, 12);
v_isSharedCheck_670_ = !lean_is_exclusive(v_s_649_);
if (v_isSharedCheck_670_ == 0)
{
v___x_664_ = v_s_649_;
v_isShared_665_ = v_isSharedCheck_670_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_steps_662_);
lean_inc(v_ncstypeIdOf_661_);
lean_inc(v_exprToNCSemiringId_660_);
lean_inc(v_ncSemirings_659_);
lean_inc(v_nctypeIdOf_658_);
lean_inc(v_exprToNCRingId_657_);
lean_inc(v_ncRings_656_);
lean_inc(v_exprToSemiringId_655_);
lean_inc(v_stypeIdOf_654_);
lean_inc(v_semirings_653_);
lean_inc(v_exprToRingId_652_);
lean_inc(v_typeIdOf_651_);
lean_inc(v_rings_650_);
lean_dec(v_s_649_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_670_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_666_; lean_object* v___x_668_; 
v___x_666_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0___redArg(v_exprToNCRingId_657_, v_e_647_, v_a_648_);
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 7, v___x_666_);
v___x_668_ = v___x_664_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_rings_650_);
lean_ctor_set(v_reuseFailAlloc_669_, 1, v_typeIdOf_651_);
lean_ctor_set(v_reuseFailAlloc_669_, 2, v_exprToRingId_652_);
lean_ctor_set(v_reuseFailAlloc_669_, 3, v_semirings_653_);
lean_ctor_set(v_reuseFailAlloc_669_, 4, v_stypeIdOf_654_);
lean_ctor_set(v_reuseFailAlloc_669_, 5, v_exprToSemiringId_655_);
lean_ctor_set(v_reuseFailAlloc_669_, 6, v_ncRings_656_);
lean_ctor_set(v_reuseFailAlloc_669_, 7, v___x_666_);
lean_ctor_set(v_reuseFailAlloc_669_, 8, v_nctypeIdOf_658_);
lean_ctor_set(v_reuseFailAlloc_669_, 9, v_ncSemirings_659_);
lean_ctor_set(v_reuseFailAlloc_669_, 10, v_exprToNCSemiringId_660_);
lean_ctor_set(v_reuseFailAlloc_669_, 11, v_ncstypeIdOf_661_);
lean_ctor_set(v_reuseFailAlloc_669_, 12, v_steps_662_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___closed__1(void){
_start:
{
lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_672_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___closed__0));
v___x_673_ = l_Lean_stringToMessageData(v___x_672_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId(lean_object* v_e_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_){
_start:
{
lean_object* v___x_690_; 
v___x_690_ = l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f___redArg(v_e_674_, v_a_676_, v_a_684_);
if (lean_obj_tag(v___x_690_) == 0)
{
lean_object* v_a_691_; 
v_a_691_ = lean_ctor_get(v___x_690_, 0);
lean_inc(v_a_691_);
lean_dec_ref(v___x_690_);
if (lean_obj_tag(v_a_691_) == 1)
{
lean_object* v_val_692_; uint8_t v___x_693_; 
v_val_692_ = lean_ctor_get(v_a_691_, 0);
lean_inc(v_val_692_);
lean_dec_ref(v_a_691_);
v___x_693_ = lean_nat_dec_eq(v_val_692_, v_a_675_);
lean_dec(v_a_675_);
lean_dec(v_val_692_);
if (v___x_693_ == 0)
{
lean_object* v___x_694_; 
v___x_694_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_678_);
if (lean_obj_tag(v___x_694_) == 0)
{
lean_object* v_a_695_; uint8_t v_verbose_696_; 
v_a_695_ = lean_ctor_get(v___x_694_, 0);
lean_inc(v_a_695_);
lean_dec_ref(v___x_694_);
v_verbose_696_ = lean_ctor_get_uint8(v_a_695_, sizeof(void*)*11 + 15);
lean_dec(v_a_695_);
if (v_verbose_696_ == 0)
{
lean_dec_ref(v_e_674_);
goto v___jp_687_;
}
else
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_697_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___closed__1);
v___x_698_ = l_Lean_indentExpr(v_e_674_);
v___x_699_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_699_, 0, v___x_697_);
lean_ctor_set(v___x_699_, 1, v___x_698_);
v___x_700_ = l_Lean_Meta_Grind_reportIssue(v___x_699_, v_a_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_, v_a_682_, v_a_683_, v_a_684_, v_a_685_);
if (lean_obj_tag(v___x_700_) == 0)
{
lean_dec_ref(v___x_700_);
goto v___jp_687_;
}
else
{
return v___x_700_;
}
}
}
else
{
lean_object* v_a_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_708_; 
lean_dec_ref(v_e_674_);
v_a_701_ = lean_ctor_get(v___x_694_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_708_ == 0)
{
v___x_703_ = v___x_694_;
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_a_701_);
lean_dec(v___x_694_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_706_; 
if (v_isShared_704_ == 0)
{
v___x_706_ = v___x_703_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_a_701_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
}
else
{
lean_dec_ref(v_e_674_);
goto v___jp_687_;
}
}
else
{
lean_object* v___f_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
lean_dec(v_a_691_);
v___f_709_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___lam__0), 3, 2);
lean_closure_set(v___f_709_, 0, v_e_674_);
lean_closure_set(v___f_709_, 1, v_a_675_);
v___x_710_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_711_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_710_, v___f_709_, v_a_676_);
return v___x_711_;
}
}
else
{
lean_object* v_a_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_719_; 
lean_dec(v_a_675_);
lean_dec_ref(v_e_674_);
v_a_712_ = lean_ctor_get(v___x_690_, 0);
v_isSharedCheck_719_ = !lean_is_exclusive(v___x_690_);
if (v_isSharedCheck_719_ == 0)
{
v___x_714_ = v___x_690_;
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_a_712_);
lean_dec(v___x_690_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_717_; 
if (v_isShared_715_ == 0)
{
v___x_717_ = v___x_714_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_a_712_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
v___jp_687_:
{
lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_688_ = lean_box(0);
v___x_689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_689_, 0, v___x_688_);
return v___x_689_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___boxed(lean_object* v_e_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_){
_start:
{
lean_object* v_res_733_; 
v_res_733_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId(v_e_720_, v_a_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_);
lean_dec(v_a_731_);
lean_dec_ref(v_a_730_);
lean_dec(v_a_729_);
lean_dec_ref(v_a_728_);
lean_dec(v_a_727_);
lean_dec_ref(v_a_726_);
lean_dec(v_a_725_);
lean_dec_ref(v_a_724_);
lean_dec(v_a_723_);
lean_dec(v_a_722_);
return v_res_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0(lean_object* v_00_u03b2_734_, lean_object* v_x_735_, lean_object* v_x_736_, lean_object* v_x_737_){
_start:
{
lean_object* v___x_738_; 
v___x_738_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0___redArg(v_x_735_, v_x_736_, v_x_737_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0(lean_object* v_00_u03b2_739_, lean_object* v_x_740_, size_t v_x_741_, size_t v_x_742_, lean_object* v_x_743_, lean_object* v_x_744_){
_start:
{
lean_object* v___x_745_; 
v___x_745_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg(v_x_740_, v_x_741_, v_x_742_, v_x_743_, v_x_744_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___boxed(lean_object* v_00_u03b2_746_, lean_object* v_x_747_, lean_object* v_x_748_, lean_object* v_x_749_, lean_object* v_x_750_, lean_object* v_x_751_){
_start:
{
size_t v_x_10226__boxed_752_; size_t v_x_10227__boxed_753_; lean_object* v_res_754_; 
v_x_10226__boxed_752_ = lean_unbox_usize(v_x_748_);
lean_dec(v_x_748_);
v_x_10227__boxed_753_ = lean_unbox_usize(v_x_749_);
lean_dec(v_x_749_);
v_res_754_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0(v_00_u03b2_746_, v_x_747_, v_x_10226__boxed_752_, v_x_10227__boxed_753_, v_x_750_, v_x_751_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_755_, lean_object* v_n_756_, lean_object* v_k_757_, lean_object* v_v_758_){
_start:
{
lean_object* v___x_759_; 
v___x_759_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__1___redArg(v_n_756_, v_k_757_, v_v_758_);
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_760_, size_t v_depth_761_, lean_object* v_keys_762_, lean_object* v_vals_763_, lean_object* v_heq_764_, lean_object* v_i_765_, lean_object* v_entries_766_){
_start:
{
lean_object* v___x_767_; 
v___x_767_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__2___redArg(v_depth_761_, v_keys_762_, v_vals_763_, v_i_765_, v_entries_766_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_768_, lean_object* v_depth_769_, lean_object* v_keys_770_, lean_object* v_vals_771_, lean_object* v_heq_772_, lean_object* v_i_773_, lean_object* v_entries_774_){
_start:
{
size_t v_depth_boxed_775_; lean_object* v_res_776_; 
v_depth_boxed_775_ = lean_unbox_usize(v_depth_769_);
lean_dec(v_depth_769_);
v_res_776_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__2(v_00_u03b2_768_, v_depth_boxed_775_, v_keys_770_, v_vals_771_, v_heq_772_, v_i_773_, v_entries_774_);
lean_dec_ref(v_vals_771_);
lean_dec_ref(v_keys_770_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_777_, lean_object* v_x_778_, lean_object* v_x_779_, lean_object* v_x_780_, lean_object* v_x_781_){
_start:
{
lean_object* v___x_782_; 
v___x_782_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__1_spec__2___redArg(v_x_778_, v_x_779_, v_x_780_, v_x_781_);
return v___x_782_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommRingM(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_Arith_CommRing_instMonadRingNonCommRingM = _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadRingNonCommRingM();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_instMonadRingNonCommRingM);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommRingM(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommRingM(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommRingM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommRingM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommRingM(builtin);
}
#ifdef __cplusplus
}
#endif
