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
lean_object* l_Lean_Meta_Sym_synthInstance_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Sym_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_CommRing_ringExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_canon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "expression in two different rings"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommRingM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommRingM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommRingM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommRingM___lam__0___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommRingM___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommRingM___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommRingM = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommRingM___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_run___redArg(lean_object* v_ringId_1_, lean_object* v_x_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_){
_start:
{
lean_object* v___x_14_; 
lean_inc(v_a_12_);
lean_inc_ref(v_a_11_);
lean_inc(v_a_10_);
lean_inc_ref(v_a_9_);
lean_inc(v_a_8_);
lean_inc_ref(v_a_7_);
lean_inc(v_a_6_);
lean_inc_ref(v_a_5_);
lean_inc(v_a_4_);
lean_inc(v_a_3_);
v___x_14_ = lean_apply_12(v_x_2_, v_ringId_1_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_, v_a_10_, v_a_11_, v_a_12_, lean_box(0));
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_run___redArg___boxed(lean_object* v_ringId_15_, lean_object* v_x_16_, lean_object* v_a_17_, lean_object* v_a_18_, lean_object* v_a_19_, lean_object* v_a_20_, lean_object* v_a_21_, lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_, lean_object* v_a_25_, lean_object* v_a_26_, lean_object* v_a_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_run___redArg(v_ringId_15_, v_x_16_, v_a_17_, v_a_18_, v_a_19_, v_a_20_, v_a_21_, v_a_22_, v_a_23_, v_a_24_, v_a_25_, v_a_26_);
lean_dec(v_a_26_);
lean_dec_ref(v_a_25_);
lean_dec(v_a_24_);
lean_dec_ref(v_a_23_);
lean_dec(v_a_22_);
lean_dec_ref(v_a_21_);
lean_dec(v_a_20_);
lean_dec_ref(v_a_19_);
lean_dec(v_a_18_);
lean_dec(v_a_17_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_run(lean_object* v_00_u03b1_29_, lean_object* v_ringId_30_, lean_object* v_x_31_, lean_object* v_a_32_, lean_object* v_a_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_){
_start:
{
lean_object* v___x_43_; 
lean_inc(v_a_41_);
lean_inc_ref(v_a_40_);
lean_inc(v_a_39_);
lean_inc_ref(v_a_38_);
lean_inc(v_a_37_);
lean_inc_ref(v_a_36_);
lean_inc(v_a_35_);
lean_inc_ref(v_a_34_);
lean_inc(v_a_33_);
lean_inc(v_a_32_);
v___x_43_ = lean_apply_12(v_x_31_, v_ringId_30_, v_a_32_, v_a_33_, v_a_34_, v_a_35_, v_a_36_, v_a_37_, v_a_38_, v_a_39_, v_a_40_, v_a_41_, lean_box(0));
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_run___boxed(lean_object* v_00_u03b1_44_, lean_object* v_ringId_45_, lean_object* v_x_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_run(v_00_u03b1_44_, v_ringId_45_, v_x_46_, v_a_47_, v_a_48_, v_a_49_, v_a_50_, v_a_51_, v_a_52_, v_a_53_, v_a_54_, v_a_55_, v_a_56_);
lean_dec(v_a_56_);
lean_dec_ref(v_a_55_);
lean_dec(v_a_54_);
lean_dec_ref(v_a_53_);
lean_dec(v_a_52_);
lean_dec_ref(v_a_51_);
lean_dec(v_a_50_);
lean_dec_ref(v_a_49_);
lean_dec(v_a_48_);
lean_dec(v_a_47_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___lam__0(lean_object* v_e_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = l_Lean_Meta_Sym_canon(v_e_59_, v___y_65_, v___y_66_, v___y_67_, v___y_68_, v___y_69_, v___y_70_);
if (lean_obj_tag(v___x_72_) == 0)
{
lean_object* v_a_73_; lean_object* v___x_74_; 
v_a_73_ = lean_ctor_get(v___x_72_, 0);
lean_inc(v_a_73_);
lean_dec_ref_known(v___x_72_, 1);
v___x_74_ = l_Lean_Meta_Sym_shareCommon(v_a_73_, v___y_65_, v___y_66_, v___y_67_, v___y_68_, v___y_69_, v___y_70_);
return v___x_74_;
}
else
{
return v___x_72_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___lam__0___boxed(lean_object* v_e_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___lam__0(v_e_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_, v___y_85_, v___y_86_);
lean_dec(v___y_86_);
lean_dec_ref(v___y_85_);
lean_dec(v___y_84_);
lean_dec_ref(v___y_83_);
lean_dec(v___y_82_);
lean_dec_ref(v___y_81_);
lean_dec(v___y_80_);
lean_dec_ref(v___y_79_);
lean_dec(v___y_78_);
lean_dec(v___y_77_);
lean_dec(v___y_76_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___lam__1(lean_object* v_e_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = l_Lean_Meta_Sym_synthInstance_x3f___redArg(v_e_89_, v___y_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___lam__1___boxed(lean_object* v_e_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___lam__1(v_e_103_, v___y_104_, v___y_105_, v___y_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_);
lean_dec(v___y_114_);
lean_dec_ref(v___y_113_);
lean_dec(v___y_112_);
lean_dec_ref(v___y_111_);
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
lean_object* v_rings_253_; lean_object* v_typeIdOf_254_; lean_object* v_exprToRingId_255_; lean_object* v_semirings_256_; lean_object* v_stypeIdOf_257_; lean_object* v_exprToSemiringId_258_; lean_object* v_ncRings_259_; lean_object* v_exprToNCRingId_260_; lean_object* v_nctypeIdOf_261_; lean_object* v_ncSemirings_262_; lean_object* v_exprToNCSemiringId_263_; lean_object* v_ncstypeIdOf_264_; lean_object* v_steps_265_; uint8_t v_reportedMaxDegreeIssue_266_; lean_object* v___x_267_; uint8_t v___x_268_; 
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
v_reportedMaxDegreeIssue_266_ = lean_ctor_get_uint8(v_s_252_, sizeof(void*)*13);
v___x_267_ = lean_array_get_size(v_ncRings_259_);
v___x_268_ = lean_nat_dec_lt(v_a_250_, v___x_267_);
if (v___x_268_ == 0)
{
lean_dec_ref(v_f_251_);
return v_s_252_;
}
else
{
lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_280_; 
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
v_isSharedCheck_280_ = !lean_is_exclusive(v_s_252_);
if (v_isSharedCheck_280_ == 0)
{
lean_object* v_unused_281_; lean_object* v_unused_282_; lean_object* v_unused_283_; lean_object* v_unused_284_; lean_object* v_unused_285_; lean_object* v_unused_286_; lean_object* v_unused_287_; lean_object* v_unused_288_; lean_object* v_unused_289_; lean_object* v_unused_290_; lean_object* v_unused_291_; lean_object* v_unused_292_; lean_object* v_unused_293_; 
v_unused_281_ = lean_ctor_get(v_s_252_, 12);
lean_dec(v_unused_281_);
v_unused_282_ = lean_ctor_get(v_s_252_, 11);
lean_dec(v_unused_282_);
v_unused_283_ = lean_ctor_get(v_s_252_, 10);
lean_dec(v_unused_283_);
v_unused_284_ = lean_ctor_get(v_s_252_, 9);
lean_dec(v_unused_284_);
v_unused_285_ = lean_ctor_get(v_s_252_, 8);
lean_dec(v_unused_285_);
v_unused_286_ = lean_ctor_get(v_s_252_, 7);
lean_dec(v_unused_286_);
v_unused_287_ = lean_ctor_get(v_s_252_, 6);
lean_dec(v_unused_287_);
v_unused_288_ = lean_ctor_get(v_s_252_, 5);
lean_dec(v_unused_288_);
v_unused_289_ = lean_ctor_get(v_s_252_, 4);
lean_dec(v_unused_289_);
v_unused_290_ = lean_ctor_get(v_s_252_, 3);
lean_dec(v_unused_290_);
v_unused_291_ = lean_ctor_get(v_s_252_, 2);
lean_dec(v_unused_291_);
v_unused_292_ = lean_ctor_get(v_s_252_, 1);
lean_dec(v_unused_292_);
v_unused_293_ = lean_ctor_get(v_s_252_, 0);
lean_dec(v_unused_293_);
v___x_270_ = v_s_252_;
v_isShared_271_ = v_isSharedCheck_280_;
goto v_resetjp_269_;
}
else
{
lean_dec(v_s_252_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_280_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
lean_object* v_v_272_; lean_object* v___x_273_; lean_object* v_xs_x27_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_278_; 
v_v_272_ = lean_array_fget(v_ncRings_259_, v_a_250_);
v___x_273_ = lean_box(0);
v_xs_x27_274_ = lean_array_fset(v_ncRings_259_, v_a_250_, v___x_273_);
v___x_275_ = lean_apply_1(v_f_251_, v_v_272_);
v___x_276_ = lean_array_fset(v_xs_x27_274_, v_a_250_, v___x_275_);
if (v_isShared_271_ == 0)
{
lean_ctor_set(v___x_270_, 6, v___x_276_);
v___x_278_ = v___x_270_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_rings_253_);
lean_ctor_set(v_reuseFailAlloc_279_, 1, v_typeIdOf_254_);
lean_ctor_set(v_reuseFailAlloc_279_, 2, v_exprToRingId_255_);
lean_ctor_set(v_reuseFailAlloc_279_, 3, v_semirings_256_);
lean_ctor_set(v_reuseFailAlloc_279_, 4, v_stypeIdOf_257_);
lean_ctor_set(v_reuseFailAlloc_279_, 5, v_exprToSemiringId_258_);
lean_ctor_set(v_reuseFailAlloc_279_, 6, v___x_276_);
lean_ctor_set(v_reuseFailAlloc_279_, 7, v_exprToNCRingId_260_);
lean_ctor_set(v_reuseFailAlloc_279_, 8, v_nctypeIdOf_261_);
lean_ctor_set(v_reuseFailAlloc_279_, 9, v_ncSemirings_262_);
lean_ctor_set(v_reuseFailAlloc_279_, 10, v_exprToNCSemiringId_263_);
lean_ctor_set(v_reuseFailAlloc_279_, 11, v_ncstypeIdOf_264_);
lean_ctor_set(v_reuseFailAlloc_279_, 12, v_steps_265_);
lean_ctor_set_uint8(v_reuseFailAlloc_279_, sizeof(void*)*13, v_reportedMaxDegreeIssue_266_);
v___x_278_ = v_reuseFailAlloc_279_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
return v___x_278_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg___lam__0___boxed(lean_object* v_a_294_, lean_object* v_f_295_, lean_object* v_s_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg___lam__0(v_a_294_, v_f_295_, v_s_296_);
lean_dec(v_a_294_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg(lean_object* v_f_298_, lean_object* v_a_299_, lean_object* v_a_300_){
_start:
{
lean_object* v___f_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
lean_inc(v_a_299_);
v___f_302_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_302_, 0, v_a_299_);
lean_closure_set(v___f_302_, 1, v_f_298_);
v___x_303_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_304_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_303_, v___f_302_, v_a_300_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg___boxed(lean_object* v_f_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg(v_f_305_, v_a_306_, v_a_307_);
lean_dec(v_a_307_);
lean_dec(v_a_306_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing(lean_object* v_f_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_){
_start:
{
lean_object* v___x_323_; 
v___x_323_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg(v_f_310_, v_a_311_, v_a_312_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___boxed(lean_object* v_f_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing(v_f_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_);
lean_dec(v_a_335_);
lean_dec_ref(v_a_334_);
lean_dec(v_a_333_);
lean_dec_ref(v_a_332_);
lean_dec(v_a_331_);
lean_dec_ref(v_a_330_);
lean_dec(v_a_329_);
lean_dec_ref(v_a_328_);
lean_dec(v_a_327_);
lean_dec(v_a_326_);
lean_dec(v_a_325_);
return v_res_337_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadRingNonCommRingM___closed__1(void){
_start:
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_339_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadRingNonCommRingM___closed__0));
v___x_340_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing___boxed), 12, 0);
v___x_341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_341_, 0, v___x_340_);
lean_ctor_set(v___x_341_, 1, v___x_339_);
return v___x_341_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadRingNonCommRingM(void){
_start:
{
lean_object* v___x_342_; 
v___x_342_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instMonadRingNonCommRingM___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_instMonadRingNonCommRingM___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadRingNonCommRingM___closed__1);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_343_, lean_object* v_vals_344_, lean_object* v_i_345_, lean_object* v_k_346_){
_start:
{
lean_object* v___x_347_; uint8_t v___x_348_; 
v___x_347_ = lean_array_get_size(v_keys_343_);
v___x_348_ = lean_nat_dec_lt(v_i_345_, v___x_347_);
if (v___x_348_ == 0)
{
lean_object* v___x_349_; 
lean_dec(v_i_345_);
v___x_349_ = lean_box(0);
return v___x_349_;
}
else
{
lean_object* v_k_x27_350_; size_t v___x_351_; size_t v___x_352_; uint8_t v___x_353_; 
v_k_x27_350_ = lean_array_fget_borrowed(v_keys_343_, v_i_345_);
v___x_351_ = lean_ptr_addr(v_k_346_);
v___x_352_ = lean_ptr_addr(v_k_x27_350_);
v___x_353_ = lean_usize_dec_eq(v___x_351_, v___x_352_);
if (v___x_353_ == 0)
{
lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_354_ = lean_unsigned_to_nat(1u);
v___x_355_ = lean_nat_add(v_i_345_, v___x_354_);
lean_dec(v_i_345_);
v_i_345_ = v___x_355_;
goto _start;
}
else
{
lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_357_ = lean_array_fget_borrowed(v_vals_344_, v_i_345_);
lean_dec(v_i_345_);
lean_inc(v___x_357_);
v___x_358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
return v___x_358_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_359_, lean_object* v_vals_360_, lean_object* v_i_361_, lean_object* v_k_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_359_, v_vals_360_, v_i_361_, v_k_362_);
lean_dec_ref(v_k_362_);
lean_dec_ref(v_vals_360_);
lean_dec_ref(v_keys_359_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___redArg(lean_object* v_x_364_, size_t v_x_365_, lean_object* v_x_366_){
_start:
{
if (lean_obj_tag(v_x_364_) == 0)
{
lean_object* v_es_367_; lean_object* v___x_368_; size_t v___x_369_; size_t v___x_370_; lean_object* v_j_371_; lean_object* v___x_372_; 
v_es_367_ = lean_ctor_get(v_x_364_, 0);
v___x_368_ = lean_box(2);
v___x_369_ = ((size_t)31ULL);
v___x_370_ = lean_usize_land(v_x_365_, v___x_369_);
v_j_371_ = lean_usize_to_nat(v___x_370_);
v___x_372_ = lean_array_get_borrowed(v___x_368_, v_es_367_, v_j_371_);
lean_dec(v_j_371_);
switch(lean_obj_tag(v___x_372_))
{
case 0:
{
lean_object* v_key_373_; lean_object* v_val_374_; size_t v___x_375_; size_t v___x_376_; uint8_t v___x_377_; 
v_key_373_ = lean_ctor_get(v___x_372_, 0);
v_val_374_ = lean_ctor_get(v___x_372_, 1);
v___x_375_ = lean_ptr_addr(v_x_366_);
v___x_376_ = lean_ptr_addr(v_key_373_);
v___x_377_ = lean_usize_dec_eq(v___x_375_, v___x_376_);
if (v___x_377_ == 0)
{
lean_object* v___x_378_; 
v___x_378_ = lean_box(0);
return v___x_378_;
}
else
{
lean_object* v___x_379_; 
lean_inc(v_val_374_);
v___x_379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_379_, 0, v_val_374_);
return v___x_379_;
}
}
case 1:
{
lean_object* v_node_380_; size_t v___x_381_; size_t v___x_382_; 
v_node_380_ = lean_ctor_get(v___x_372_, 0);
v___x_381_ = ((size_t)5ULL);
v___x_382_ = lean_usize_shift_right(v_x_365_, v___x_381_);
v_x_364_ = v_node_380_;
v_x_365_ = v___x_382_;
goto _start;
}
default: 
{
lean_object* v___x_384_; 
v___x_384_ = lean_box(0);
return v___x_384_;
}
}
}
else
{
lean_object* v_ks_385_; lean_object* v_vs_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v_ks_385_ = lean_ctor_get(v_x_364_, 0);
v_vs_386_ = lean_ctor_get(v_x_364_, 1);
v___x_387_ = lean_unsigned_to_nat(0u);
v___x_388_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_385_, v_vs_386_, v___x_387_, v_x_366_);
return v___x_388_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_389_, lean_object* v_x_390_, lean_object* v_x_391_){
_start:
{
size_t v_x_890__boxed_392_; lean_object* v_res_393_; 
v_x_890__boxed_392_ = lean_unbox_usize(v_x_390_);
lean_dec(v_x_390_);
v_res_393_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___redArg(v_x_389_, v_x_890__boxed_392_, v_x_391_);
lean_dec_ref(v_x_391_);
lean_dec_ref(v_x_389_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0___redArg(lean_object* v_x_394_, lean_object* v_x_395_){
_start:
{
size_t v___x_396_; size_t v___x_397_; size_t v___x_398_; uint64_t v___x_399_; size_t v___x_400_; lean_object* v___x_401_; 
v___x_396_ = lean_ptr_addr(v_x_395_);
v___x_397_ = ((size_t)3ULL);
v___x_398_ = lean_usize_shift_right(v___x_396_, v___x_397_);
v___x_399_ = lean_usize_to_uint64(v___x_398_);
v___x_400_ = lean_uint64_to_usize(v___x_399_);
v___x_401_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___redArg(v_x_394_, v___x_400_, v_x_395_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0___redArg___boxed(lean_object* v_x_402_, lean_object* v_x_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0___redArg(v_x_402_, v_x_403_);
lean_dec_ref(v_x_403_);
lean_dec_ref(v_x_402_);
return v_res_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f___redArg(lean_object* v_e_405_, lean_object* v_a_406_, lean_object* v_a_407_){
_start:
{
lean_object* v___x_409_; 
v___x_409_ = l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_406_, v_a_407_);
if (lean_obj_tag(v___x_409_) == 0)
{
lean_object* v_a_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_419_; 
v_a_410_ = lean_ctor_get(v___x_409_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v___x_409_);
if (v_isSharedCheck_419_ == 0)
{
v___x_412_ = v___x_409_;
v_isShared_413_ = v_isSharedCheck_419_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_a_410_);
lean_dec(v___x_409_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_419_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v_exprToNCRingId_414_; lean_object* v___x_415_; lean_object* v___x_417_; 
v_exprToNCRingId_414_ = lean_ctor_get(v_a_410_, 7);
lean_inc_ref(v_exprToNCRingId_414_);
lean_dec(v_a_410_);
v___x_415_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0___redArg(v_exprToNCRingId_414_, v_e_405_);
lean_dec_ref(v_exprToNCRingId_414_);
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 0, v___x_415_);
v___x_417_ = v___x_412_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v___x_415_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
}
else
{
lean_object* v_a_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_427_; 
v_a_420_ = lean_ctor_get(v___x_409_, 0);
v_isSharedCheck_427_ = !lean_is_exclusive(v___x_409_);
if (v_isSharedCheck_427_ == 0)
{
v___x_422_ = v___x_409_;
v_isShared_423_ = v_isSharedCheck_427_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_a_420_);
lean_dec(v___x_409_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_427_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v___x_425_; 
if (v_isShared_423_ == 0)
{
v___x_425_ = v___x_422_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v_a_420_);
v___x_425_ = v_reuseFailAlloc_426_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
return v___x_425_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f___redArg___boxed(lean_object* v_e_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f___redArg(v_e_428_, v_a_429_, v_a_430_);
lean_dec_ref(v_a_430_);
lean_dec(v_a_429_);
lean_dec_ref(v_e_428_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f(lean_object* v_e_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_){
_start:
{
lean_object* v___x_445_; 
v___x_445_ = l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f___redArg(v_e_433_, v_a_434_, v_a_442_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f___boxed(lean_object* v_e_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f(v_e_446_, v_a_447_, v_a_448_, v_a_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_, v_a_454_, v_a_455_, v_a_456_);
lean_dec(v_a_456_);
lean_dec_ref(v_a_455_);
lean_dec(v_a_454_);
lean_dec_ref(v_a_453_);
lean_dec(v_a_452_);
lean_dec_ref(v_a_451_);
lean_dec(v_a_450_);
lean_dec_ref(v_a_449_);
lean_dec(v_a_448_);
lean_dec(v_a_447_);
lean_dec_ref(v_e_446_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0(lean_object* v_00_u03b2_459_, lean_object* v_x_460_, lean_object* v_x_461_){
_start:
{
lean_object* v___x_462_; 
v___x_462_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0___redArg(v_x_460_, v_x_461_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0___boxed(lean_object* v_00_u03b2_463_, lean_object* v_x_464_, lean_object* v_x_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0(v_00_u03b2_463_, v_x_464_, v_x_465_);
lean_dec_ref(v_x_465_);
lean_dec_ref(v_x_464_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_467_, lean_object* v_x_468_, size_t v_x_469_, lean_object* v_x_470_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___redArg(v_x_468_, v_x_469_, v_x_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_472_, lean_object* v_x_473_, lean_object* v_x_474_, lean_object* v_x_475_){
_start:
{
size_t v_x_1011__boxed_476_; lean_object* v_res_477_; 
v_x_1011__boxed_476_ = lean_unbox_usize(v_x_474_);
lean_dec(v_x_474_);
v_res_477_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0(v_00_u03b2_472_, v_x_473_, v_x_1011__boxed_476_, v_x_475_);
lean_dec_ref(v_x_475_);
lean_dec_ref(v_x_473_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_478_, lean_object* v_keys_479_, lean_object* v_vals_480_, lean_object* v_heq_481_, lean_object* v_i_482_, lean_object* v_k_483_){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_479_, v_vals_480_, v_i_482_, v_k_483_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_485_, lean_object* v_keys_486_, lean_object* v_vals_487_, lean_object* v_heq_488_, lean_object* v_i_489_, lean_object* v_k_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_485_, v_keys_486_, v_vals_487_, v_heq_488_, v_i_489_, v_k_490_);
lean_dec_ref(v_k_490_);
lean_dec_ref(v_vals_487_);
lean_dec_ref(v_keys_486_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_492_, lean_object* v_x_493_, lean_object* v_x_494_, lean_object* v_x_495_){
_start:
{
lean_object* v_ks_496_; lean_object* v_vs_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_523_; 
v_ks_496_ = lean_ctor_get(v_x_492_, 0);
v_vs_497_ = lean_ctor_get(v_x_492_, 1);
v_isSharedCheck_523_ = !lean_is_exclusive(v_x_492_);
if (v_isSharedCheck_523_ == 0)
{
v___x_499_ = v_x_492_;
v_isShared_500_ = v_isSharedCheck_523_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_vs_497_);
lean_inc(v_ks_496_);
lean_dec(v_x_492_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_523_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_501_; uint8_t v___x_502_; 
v___x_501_ = lean_array_get_size(v_ks_496_);
v___x_502_ = lean_nat_dec_lt(v_x_493_, v___x_501_);
if (v___x_502_ == 0)
{
lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_506_; 
lean_dec(v_x_493_);
v___x_503_ = lean_array_push(v_ks_496_, v_x_494_);
v___x_504_ = lean_array_push(v_vs_497_, v_x_495_);
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 1, v___x_504_);
lean_ctor_set(v___x_499_, 0, v___x_503_);
v___x_506_ = v___x_499_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v___x_503_);
lean_ctor_set(v_reuseFailAlloc_507_, 1, v___x_504_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
else
{
lean_object* v_k_x27_508_; size_t v___x_509_; size_t v___x_510_; uint8_t v___x_511_; 
v_k_x27_508_ = lean_array_fget_borrowed(v_ks_496_, v_x_493_);
v___x_509_ = lean_ptr_addr(v_x_494_);
v___x_510_ = lean_ptr_addr(v_k_x27_508_);
v___x_511_ = lean_usize_dec_eq(v___x_509_, v___x_510_);
if (v___x_511_ == 0)
{
lean_object* v___x_513_; 
if (v_isShared_500_ == 0)
{
v___x_513_ = v___x_499_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_ks_496_);
lean_ctor_set(v_reuseFailAlloc_517_, 1, v_vs_497_);
v___x_513_ = v_reuseFailAlloc_517_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_514_ = lean_unsigned_to_nat(1u);
v___x_515_ = lean_nat_add(v_x_493_, v___x_514_);
lean_dec(v_x_493_);
v_x_492_ = v___x_513_;
v_x_493_ = v___x_515_;
goto _start;
}
}
else
{
lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_521_; 
v___x_518_ = lean_array_fset(v_ks_496_, v_x_493_, v_x_494_);
v___x_519_ = lean_array_fset(v_vs_497_, v_x_493_, v_x_495_);
lean_dec(v_x_493_);
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 1, v___x_519_);
lean_ctor_set(v___x_499_, 0, v___x_518_);
v___x_521_ = v___x_499_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v___x_518_);
lean_ctor_set(v_reuseFailAlloc_522_, 1, v___x_519_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__1___redArg(lean_object* v_n_524_, lean_object* v_k_525_, lean_object* v_v_526_){
_start:
{
lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_527_ = lean_unsigned_to_nat(0u);
v___x_528_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__1_spec__2___redArg(v_n_524_, v___x_527_, v_k_525_, v_v_526_);
return v___x_528_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_529_; 
v___x_529_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg(lean_object* v_x_530_, size_t v_x_531_, size_t v_x_532_, lean_object* v_x_533_, lean_object* v_x_534_){
_start:
{
if (lean_obj_tag(v_x_530_) == 0)
{
lean_object* v_es_535_; size_t v___x_536_; size_t v___x_537_; lean_object* v_j_538_; lean_object* v___x_539_; uint8_t v___x_540_; 
v_es_535_ = lean_ctor_get(v_x_530_, 0);
v___x_536_ = ((size_t)31ULL);
v___x_537_ = lean_usize_land(v_x_531_, v___x_536_);
v_j_538_ = lean_usize_to_nat(v___x_537_);
v___x_539_ = lean_array_get_size(v_es_535_);
v___x_540_ = lean_nat_dec_lt(v_j_538_, v___x_539_);
if (v___x_540_ == 0)
{
lean_dec(v_j_538_);
lean_dec(v_x_534_);
lean_dec_ref(v_x_533_);
return v_x_530_;
}
else
{
lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_581_; 
lean_inc_ref(v_es_535_);
v_isSharedCheck_581_ = !lean_is_exclusive(v_x_530_);
if (v_isSharedCheck_581_ == 0)
{
lean_object* v_unused_582_; 
v_unused_582_ = lean_ctor_get(v_x_530_, 0);
lean_dec(v_unused_582_);
v___x_542_ = v_x_530_;
v_isShared_543_ = v_isSharedCheck_581_;
goto v_resetjp_541_;
}
else
{
lean_dec(v_x_530_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_581_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v_v_544_; lean_object* v___x_545_; lean_object* v_xs_x27_546_; lean_object* v___y_548_; 
v_v_544_ = lean_array_fget(v_es_535_, v_j_538_);
v___x_545_ = lean_box(0);
v_xs_x27_546_ = lean_array_fset(v_es_535_, v_j_538_, v___x_545_);
switch(lean_obj_tag(v_v_544_))
{
case 0:
{
lean_object* v_key_553_; lean_object* v_val_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_566_; 
v_key_553_ = lean_ctor_get(v_v_544_, 0);
v_val_554_ = lean_ctor_get(v_v_544_, 1);
v_isSharedCheck_566_ = !lean_is_exclusive(v_v_544_);
if (v_isSharedCheck_566_ == 0)
{
v___x_556_ = v_v_544_;
v_isShared_557_ = v_isSharedCheck_566_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_val_554_);
lean_inc(v_key_553_);
lean_dec(v_v_544_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_566_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
size_t v___x_558_; size_t v___x_559_; uint8_t v___x_560_; 
v___x_558_ = lean_ptr_addr(v_x_533_);
v___x_559_ = lean_ptr_addr(v_key_553_);
v___x_560_ = lean_usize_dec_eq(v___x_558_, v___x_559_);
if (v___x_560_ == 0)
{
lean_object* v___x_561_; lean_object* v___x_562_; 
lean_del_object(v___x_556_);
v___x_561_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_553_, v_val_554_, v_x_533_, v_x_534_);
v___x_562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_562_, 0, v___x_561_);
v___y_548_ = v___x_562_;
goto v___jp_547_;
}
else
{
lean_object* v___x_564_; 
lean_dec(v_val_554_);
lean_dec(v_key_553_);
if (v_isShared_557_ == 0)
{
lean_ctor_set(v___x_556_, 1, v_x_534_);
lean_ctor_set(v___x_556_, 0, v_x_533_);
v___x_564_ = v___x_556_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v_x_533_);
lean_ctor_set(v_reuseFailAlloc_565_, 1, v_x_534_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
v___y_548_ = v___x_564_;
goto v___jp_547_;
}
}
}
}
case 1:
{
lean_object* v_node_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_579_; 
v_node_567_ = lean_ctor_get(v_v_544_, 0);
v_isSharedCheck_579_ = !lean_is_exclusive(v_v_544_);
if (v_isSharedCheck_579_ == 0)
{
v___x_569_ = v_v_544_;
v_isShared_570_ = v_isSharedCheck_579_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_node_567_);
lean_dec(v_v_544_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_579_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
size_t v___x_571_; size_t v___x_572_; size_t v___x_573_; size_t v___x_574_; lean_object* v___x_575_; lean_object* v___x_577_; 
v___x_571_ = ((size_t)5ULL);
v___x_572_ = lean_usize_shift_right(v_x_531_, v___x_571_);
v___x_573_ = ((size_t)1ULL);
v___x_574_ = lean_usize_add(v_x_532_, v___x_573_);
v___x_575_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg(v_node_567_, v___x_572_, v___x_574_, v_x_533_, v_x_534_);
if (v_isShared_570_ == 0)
{
lean_ctor_set(v___x_569_, 0, v___x_575_);
v___x_577_ = v___x_569_;
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
v___y_548_ = v___x_577_;
goto v___jp_547_;
}
}
}
default: 
{
lean_object* v___x_580_; 
v___x_580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_580_, 0, v_x_533_);
lean_ctor_set(v___x_580_, 1, v_x_534_);
v___y_548_ = v___x_580_;
goto v___jp_547_;
}
}
v___jp_547_:
{
lean_object* v___x_549_; lean_object* v___x_551_; 
v___x_549_ = lean_array_fset(v_xs_x27_546_, v_j_538_, v___y_548_);
lean_dec(v_j_538_);
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 0, v___x_549_);
v___x_551_ = v___x_542_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v___x_549_);
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
else
{
lean_object* v_ks_583_; lean_object* v_vs_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_604_; 
v_ks_583_ = lean_ctor_get(v_x_530_, 0);
v_vs_584_ = lean_ctor_get(v_x_530_, 1);
v_isSharedCheck_604_ = !lean_is_exclusive(v_x_530_);
if (v_isSharedCheck_604_ == 0)
{
v___x_586_ = v_x_530_;
v_isShared_587_ = v_isSharedCheck_604_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_vs_584_);
lean_inc(v_ks_583_);
lean_dec(v_x_530_);
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
v_newNode_590_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__1___redArg(v___x_589_, v_x_533_, v_x_534_);
v___x_598_ = ((size_t)7ULL);
v___x_599_ = lean_usize_dec_le(v___x_598_, v_x_532_);
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
v___x_597_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__2___redArg(v_x_532_, v_ks_593_, v_vs_594_, v___x_595_, v___x_596_);
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
lean_object* v_k_612_; lean_object* v_v_613_; size_t v___x_614_; size_t v___x_615_; size_t v___x_616_; uint64_t v___x_617_; size_t v_h_618_; size_t v___x_619_; lean_object* v___x_620_; size_t v___x_621_; size_t v___x_622_; size_t v___x_623_; size_t v_h_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v_k_612_ = lean_array_fget_borrowed(v_keys_606_, v_i_608_);
v_v_613_ = lean_array_fget_borrowed(v_vals_607_, v_i_608_);
v___x_614_ = lean_ptr_addr(v_k_612_);
v___x_615_ = ((size_t)3ULL);
v___x_616_ = lean_usize_shift_right(v___x_614_, v___x_615_);
v___x_617_ = lean_usize_to_uint64(v___x_616_);
v_h_618_ = lean_uint64_to_usize(v___x_617_);
v___x_619_ = ((size_t)5ULL);
v___x_620_ = lean_unsigned_to_nat(1u);
v___x_621_ = ((size_t)1ULL);
v___x_622_ = lean_usize_sub(v_depth_605_, v___x_621_);
v___x_623_ = lean_usize_mul(v___x_619_, v___x_622_);
v_h_624_ = lean_usize_shift_right(v_h_618_, v___x_623_);
v___x_625_ = lean_nat_add(v_i_608_, v___x_620_);
lean_dec(v_i_608_);
lean_inc(v_v_613_);
lean_inc(v_k_612_);
v___x_626_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg(v_entries_609_, v_h_624_, v_depth_605_, v_k_612_, v_v_613_);
v_i_608_ = v___x_625_;
v_entries_609_ = v___x_626_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_628_, lean_object* v_keys_629_, lean_object* v_vals_630_, lean_object* v_i_631_, lean_object* v_entries_632_){
_start:
{
size_t v_depth_boxed_633_; lean_object* v_res_634_; 
v_depth_boxed_633_ = lean_unbox_usize(v_depth_628_);
lean_dec(v_depth_628_);
v_res_634_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__2___redArg(v_depth_boxed_633_, v_keys_629_, v_vals_630_, v_i_631_, v_entries_632_);
lean_dec_ref(v_vals_630_);
lean_dec_ref(v_keys_629_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg___boxed(lean_object* v_x_635_, lean_object* v_x_636_, lean_object* v_x_637_, lean_object* v_x_638_, lean_object* v_x_639_){
_start:
{
size_t v_x_8301__boxed_640_; size_t v_x_8302__boxed_641_; lean_object* v_res_642_; 
v_x_8301__boxed_640_ = lean_unbox_usize(v_x_636_);
lean_dec(v_x_636_);
v_x_8302__boxed_641_ = lean_unbox_usize(v_x_637_);
lean_dec(v_x_637_);
v_res_642_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg(v_x_635_, v_x_8301__boxed_640_, v_x_8302__boxed_641_, v_x_638_, v_x_639_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0___redArg(lean_object* v_x_643_, lean_object* v_x_644_, lean_object* v_x_645_){
_start:
{
size_t v___x_646_; size_t v___x_647_; size_t v___x_648_; uint64_t v___x_649_; size_t v___x_650_; size_t v___x_651_; lean_object* v___x_652_; 
v___x_646_ = lean_ptr_addr(v_x_644_);
v___x_647_ = ((size_t)3ULL);
v___x_648_ = lean_usize_shift_right(v___x_646_, v___x_647_);
v___x_649_ = lean_usize_to_uint64(v___x_648_);
v___x_650_ = lean_uint64_to_usize(v___x_649_);
v___x_651_ = ((size_t)1ULL);
v___x_652_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg(v_x_643_, v___x_650_, v___x_651_, v_x_644_, v_x_645_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg___lam__0(lean_object* v_e_653_, lean_object* v_a_654_, lean_object* v_s_655_){
_start:
{
lean_object* v_rings_656_; lean_object* v_typeIdOf_657_; lean_object* v_exprToRingId_658_; lean_object* v_semirings_659_; lean_object* v_stypeIdOf_660_; lean_object* v_exprToSemiringId_661_; lean_object* v_ncRings_662_; lean_object* v_exprToNCRingId_663_; lean_object* v_nctypeIdOf_664_; lean_object* v_ncSemirings_665_; lean_object* v_exprToNCSemiringId_666_; lean_object* v_ncstypeIdOf_667_; lean_object* v_steps_668_; uint8_t v_reportedMaxDegreeIssue_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_677_; 
v_rings_656_ = lean_ctor_get(v_s_655_, 0);
v_typeIdOf_657_ = lean_ctor_get(v_s_655_, 1);
v_exprToRingId_658_ = lean_ctor_get(v_s_655_, 2);
v_semirings_659_ = lean_ctor_get(v_s_655_, 3);
v_stypeIdOf_660_ = lean_ctor_get(v_s_655_, 4);
v_exprToSemiringId_661_ = lean_ctor_get(v_s_655_, 5);
v_ncRings_662_ = lean_ctor_get(v_s_655_, 6);
v_exprToNCRingId_663_ = lean_ctor_get(v_s_655_, 7);
v_nctypeIdOf_664_ = lean_ctor_get(v_s_655_, 8);
v_ncSemirings_665_ = lean_ctor_get(v_s_655_, 9);
v_exprToNCSemiringId_666_ = lean_ctor_get(v_s_655_, 10);
v_ncstypeIdOf_667_ = lean_ctor_get(v_s_655_, 11);
v_steps_668_ = lean_ctor_get(v_s_655_, 12);
v_reportedMaxDegreeIssue_669_ = lean_ctor_get_uint8(v_s_655_, sizeof(void*)*13);
v_isSharedCheck_677_ = !lean_is_exclusive(v_s_655_);
if (v_isSharedCheck_677_ == 0)
{
v___x_671_ = v_s_655_;
v_isShared_672_ = v_isSharedCheck_677_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_steps_668_);
lean_inc(v_ncstypeIdOf_667_);
lean_inc(v_exprToNCSemiringId_666_);
lean_inc(v_ncSemirings_665_);
lean_inc(v_nctypeIdOf_664_);
lean_inc(v_exprToNCRingId_663_);
lean_inc(v_ncRings_662_);
lean_inc(v_exprToSemiringId_661_);
lean_inc(v_stypeIdOf_660_);
lean_inc(v_semirings_659_);
lean_inc(v_exprToRingId_658_);
lean_inc(v_typeIdOf_657_);
lean_inc(v_rings_656_);
lean_dec(v_s_655_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_677_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_673_; lean_object* v___x_675_; 
lean_inc(v_a_654_);
v___x_673_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0___redArg(v_exprToNCRingId_663_, v_e_653_, v_a_654_);
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 7, v___x_673_);
v___x_675_ = v___x_671_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 13, 1);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_rings_656_);
lean_ctor_set(v_reuseFailAlloc_676_, 1, v_typeIdOf_657_);
lean_ctor_set(v_reuseFailAlloc_676_, 2, v_exprToRingId_658_);
lean_ctor_set(v_reuseFailAlloc_676_, 3, v_semirings_659_);
lean_ctor_set(v_reuseFailAlloc_676_, 4, v_stypeIdOf_660_);
lean_ctor_set(v_reuseFailAlloc_676_, 5, v_exprToSemiringId_661_);
lean_ctor_set(v_reuseFailAlloc_676_, 6, v_ncRings_662_);
lean_ctor_set(v_reuseFailAlloc_676_, 7, v___x_673_);
lean_ctor_set(v_reuseFailAlloc_676_, 8, v_nctypeIdOf_664_);
lean_ctor_set(v_reuseFailAlloc_676_, 9, v_ncSemirings_665_);
lean_ctor_set(v_reuseFailAlloc_676_, 10, v_exprToNCSemiringId_666_);
lean_ctor_set(v_reuseFailAlloc_676_, 11, v_ncstypeIdOf_667_);
lean_ctor_set(v_reuseFailAlloc_676_, 12, v_steps_668_);
lean_ctor_set_uint8(v_reuseFailAlloc_676_, sizeof(void*)*13, v_reportedMaxDegreeIssue_669_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg___lam__0___boxed(lean_object* v_e_678_, lean_object* v_a_679_, lean_object* v_s_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg___lam__0(v_e_678_, v_a_679_, v_s_680_);
lean_dec(v_a_679_);
return v_res_681_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg___closed__1(void){
_start:
{
lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_683_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg___closed__0));
v___x_684_ = l_Lean_stringToMessageData(v___x_683_);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg(lean_object* v_e_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_){
_start:
{
lean_object* v___x_698_; 
v___x_698_ = l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f___redArg(v_e_685_, v_a_687_, v_a_692_);
if (lean_obj_tag(v___x_698_) == 0)
{
lean_object* v_a_699_; 
v_a_699_ = lean_ctor_get(v___x_698_, 0);
lean_inc(v_a_699_);
lean_dec_ref_known(v___x_698_, 1);
if (lean_obj_tag(v_a_699_) == 1)
{
lean_object* v_val_700_; uint8_t v___x_701_; 
v_val_700_ = lean_ctor_get(v_a_699_, 0);
lean_inc(v_val_700_);
lean_dec_ref_known(v_a_699_, 1);
v___x_701_ = lean_nat_dec_eq(v_val_700_, v_a_686_);
lean_dec(v_val_700_);
if (v___x_701_ == 0)
{
lean_object* v___x_702_; 
v___x_702_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_688_);
if (lean_obj_tag(v___x_702_) == 0)
{
lean_object* v_a_703_; uint8_t v_verbose_704_; 
v_a_703_ = lean_ctor_get(v___x_702_, 0);
lean_inc(v_a_703_);
lean_dec_ref_known(v___x_702_, 1);
v_verbose_704_ = lean_ctor_get_uint8(v_a_703_, 0);
lean_dec(v_a_703_);
if (v_verbose_704_ == 0)
{
lean_dec_ref(v_e_685_);
goto v___jp_695_;
}
else
{
lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_705_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg___closed__1, &l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg___closed__1);
v___x_706_ = l_Lean_indentExpr(v_e_685_);
v___x_707_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_707_, 0, v___x_705_);
lean_ctor_set(v___x_707_, 1, v___x_706_);
v___x_708_ = l_Lean_Meta_Sym_reportIssue(v___x_707_, v_a_688_, v_a_689_, v_a_690_, v_a_691_, v_a_692_, v_a_693_);
if (lean_obj_tag(v___x_708_) == 0)
{
lean_dec_ref_known(v___x_708_, 1);
goto v___jp_695_;
}
else
{
return v___x_708_;
}
}
}
else
{
lean_object* v_a_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_716_; 
lean_dec_ref(v_e_685_);
v_a_709_ = lean_ctor_get(v___x_702_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_702_);
if (v_isSharedCheck_716_ == 0)
{
v___x_711_ = v___x_702_;
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_a_709_);
lean_dec(v___x_702_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_716_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_714_; 
if (v_isShared_712_ == 0)
{
v___x_714_ = v___x_711_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_a_709_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
}
else
{
lean_dec_ref(v_e_685_);
goto v___jp_695_;
}
}
else
{
lean_object* v___f_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
lean_dec(v_a_699_);
lean_inc(v_a_686_);
v___f_717_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_717_, 0, v_e_685_);
lean_closure_set(v___f_717_, 1, v_a_686_);
v___x_718_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
v___x_719_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_718_, v___f_717_, v_a_687_);
return v___x_719_;
}
}
else
{
lean_object* v_a_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_727_; 
lean_dec_ref(v_e_685_);
v_a_720_ = lean_ctor_get(v___x_698_, 0);
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_698_);
if (v_isSharedCheck_727_ == 0)
{
v___x_722_ = v___x_698_;
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_a_720_);
lean_dec(v___x_698_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_725_; 
if (v_isShared_723_ == 0)
{
v___x_725_ = v___x_722_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v_a_720_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
}
v___jp_695_:
{
lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_696_ = lean_box(0);
v___x_697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_697_, 0, v___x_696_);
return v___x_697_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg___boxed(lean_object* v_e_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg(v_e_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_);
lean_dec(v_a_736_);
lean_dec_ref(v_a_735_);
lean_dec(v_a_734_);
lean_dec_ref(v_a_733_);
lean_dec(v_a_732_);
lean_dec_ref(v_a_731_);
lean_dec(v_a_730_);
lean_dec(v_a_729_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId(lean_object* v_e_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_){
_start:
{
lean_object* v___x_752_; 
v___x_752_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg(v_e_739_, v_a_740_, v_a_741_, v_a_745_, v_a_746_, v_a_747_, v_a_748_, v_a_749_, v_a_750_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___boxed(lean_object* v_e_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_){
_start:
{
lean_object* v_res_766_; 
v_res_766_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId(v_e_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_, v_a_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_);
lean_dec(v_a_764_);
lean_dec_ref(v_a_763_);
lean_dec(v_a_762_);
lean_dec_ref(v_a_761_);
lean_dec(v_a_760_);
lean_dec_ref(v_a_759_);
lean_dec(v_a_758_);
lean_dec_ref(v_a_757_);
lean_dec(v_a_756_);
lean_dec(v_a_755_);
lean_dec(v_a_754_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0(lean_object* v_00_u03b2_767_, lean_object* v_x_768_, lean_object* v_x_769_, lean_object* v_x_770_){
_start:
{
lean_object* v___x_771_; 
v___x_771_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0___redArg(v_x_768_, v_x_769_, v_x_770_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0(lean_object* v_00_u03b2_772_, lean_object* v_x_773_, size_t v_x_774_, size_t v_x_775_, lean_object* v_x_776_, lean_object* v_x_777_){
_start:
{
lean_object* v___x_778_; 
v___x_778_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg(v_x_773_, v_x_774_, v_x_775_, v_x_776_, v_x_777_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___boxed(lean_object* v_00_u03b2_779_, lean_object* v_x_780_, lean_object* v_x_781_, lean_object* v_x_782_, lean_object* v_x_783_, lean_object* v_x_784_){
_start:
{
size_t v_x_8591__boxed_785_; size_t v_x_8592__boxed_786_; lean_object* v_res_787_; 
v_x_8591__boxed_785_ = lean_unbox_usize(v_x_781_);
lean_dec(v_x_781_);
v_x_8592__boxed_786_ = lean_unbox_usize(v_x_782_);
lean_dec(v_x_782_);
v_res_787_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0(v_00_u03b2_779_, v_x_780_, v_x_8591__boxed_785_, v_x_8592__boxed_786_, v_x_783_, v_x_784_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_788_, lean_object* v_n_789_, lean_object* v_k_790_, lean_object* v_v_791_){
_start:
{
lean_object* v___x_792_; 
v___x_792_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__1___redArg(v_n_789_, v_k_790_, v_v_791_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_793_, size_t v_depth_794_, lean_object* v_keys_795_, lean_object* v_vals_796_, lean_object* v_heq_797_, lean_object* v_i_798_, lean_object* v_entries_799_){
_start:
{
lean_object* v___x_800_; 
v___x_800_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__2___redArg(v_depth_794_, v_keys_795_, v_vals_796_, v_i_798_, v_entries_799_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_801_, lean_object* v_depth_802_, lean_object* v_keys_803_, lean_object* v_vals_804_, lean_object* v_heq_805_, lean_object* v_i_806_, lean_object* v_entries_807_){
_start:
{
size_t v_depth_boxed_808_; lean_object* v_res_809_; 
v_depth_boxed_808_ = lean_unbox_usize(v_depth_802_);
lean_dec(v_depth_802_);
v_res_809_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__2(v_00_u03b2_801_, v_depth_boxed_808_, v_keys_803_, v_vals_804_, v_heq_805_, v_i_806_, v_entries_807_);
lean_dec_ref(v_vals_804_);
lean_dec_ref(v_keys_803_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_810_, lean_object* v_x_811_, lean_object* v_x_812_, lean_object* v_x_813_, lean_object* v_x_814_){
_start:
{
lean_object* v___x_815_; 
v___x_815_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__1_spec__2___redArg(v_x_811_, v_x_812_, v_x_813_, v_x_814_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommRingM___lam__0(lean_object* v_e_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_){
_start:
{
lean_object* v___x_829_; 
v___x_829_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg(v_e_816_, v___y_817_, v___y_818_, v___y_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommRingM___lam__0___boxed(lean_object* v_e_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_){
_start:
{
lean_object* v_res_843_; 
v_res_843_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommRingM___lam__0(v_e_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_);
lean_dec(v___y_841_);
lean_dec_ref(v___y_840_);
lean_dec(v___y_839_);
lean_dec_ref(v___y_838_);
lean_dec(v___y_837_);
lean_dec_ref(v___y_836_);
lean_dec(v___y_835_);
lean_dec_ref(v___y_834_);
lean_dec(v___y_833_);
lean_dec(v___y_832_);
lean_dec(v___y_831_);
return v_res_843_;
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
