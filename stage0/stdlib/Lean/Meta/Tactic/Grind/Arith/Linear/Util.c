// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Linear.Util
// Imports: public import Lean.Meta.Tactic.Grind.Arith.Linear.LinearM import Lean.Meta.Tactic.Grind.Arith.Util import Init.Data.Int.Gcd
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
lean_object* l_Rat_ofInt(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l_instInhabitedRat;
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Rat_mul(lean_object*, lean_object*);
lean_object* l_Rat_add(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_outOfBounds___redArg(lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Linear_linearExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t l_Rat_instDecidableLe(lean_object*, lean_object*);
uint8_t l_Lean_Bool_toLBool(uint8_t);
uint8_t l_Rat_blt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* l_Int_gcd(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
uint64_t lean_usize_to_uint64(size_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_shrink(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isInconsistent___redArg(lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_instDecidableEqRat_decEq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getZero(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getZero___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOne(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOne___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isCommRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isCommRing___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isOrderedCommRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isOrderedCommRing___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isLinearOrder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isLinearOrder___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_hasNoNatZeroDivisors(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_hasNoNatZeroDivisors___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "expression in two different structure in linarith module"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 82, .m_capacity = 82, .m_length = 81, .m_data = "`grind linarith` internal error, structure does not implement `NoNatZeroDivisors`"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_getLEInst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 63, .m_capacity = 63, .m_length = 62, .m_data = "`grind linarith` internal error, structure does not support LE"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_getLEInst___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_getLEInst___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_getLEInst___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_getLEInst___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLEInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLEInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_getLTInst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 63, .m_capacity = 63, .m_length = 62, .m_data = "`grind linarith` internal error, structure does not support LT"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_getLTInst___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_getLTInst___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_getLTInst___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_getLTInst___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLTInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLTInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 78, .m_capacity = 78, .m_length = 77, .m_data = "`grind linarith` internal error, structure does not have a lawful LT instance"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "`grind linarith` internal error, structure is not a preorder"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "`grind linarith` internal error, structure is not an ordered module"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isOrderedAdd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isOrderedAdd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 72, .m_capacity = 72, .m_length = 71, .m_data = "`grind linarith` internal error, structure is not an ordered int module"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 65, .m_capacity = 65, .m_length = 64, .m_data = "`grind linarith` internal error, structure is not a linear order"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_getRingInst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "`grind linarith` internal error, structure is not a ring"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_getRingInst___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_getRingInst___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_getRingInst___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_getRingInst___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getRingInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getRingInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = "`grind linarith` internal error, structure is not a commutative ring"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getCommRingInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "`grind linarith` internal error, structure is not an ordered ring"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_eval_x3f_go_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_eval_x3f_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_eval_x3f_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Grind_Linarith_Poly_eval_x3f_spec__0(lean_object*);
static lean_once_cell_t l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0;
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_eval_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_eval_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00Lean_Grind_Linarith_Poly_eval_x3f_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_satisfied(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_satisfied___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_satisfied(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_satisfied___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_inconsistent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_inconsistent___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_eliminated(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_eliminated___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOccursOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOccursOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_addOcc___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_addOcc___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_addOcc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_addOcc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_updateOccs_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_updateOccs_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Grind_Linarith_Poly_updateOccs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 64, .m_capacity = 64, .m_length = 63, .m_data = "`grind linarith` internal error, unexpected constant polynomial"};
static const lean_object* l_Lean_Grind_Linarith_Poly_updateOccs___closed__0 = (const lean_object*)&l_Lean_Grind_Linarith_Poly_updateOccs___closed__0_value;
static lean_once_cell_t l_Lean_Grind_Linarith_Poly_updateOccs___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Grind_Linarith_Poly_updateOccs___closed__1;
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_updateOccs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_updateOccs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_findVarToSubst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_findVarToSubst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_gcdCoeffsAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_gcdCoeffsAux___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_gcdCoeffs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_gcdCoeffs___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_div___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_pickVarToElim_x3f(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_getZero(lean_object* v_a_1_, lean_object* v_a_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1_, v_a_2_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_, v_a_10_, v_a_11_);
if (lean_obj_tag(v___x_13_) == 0)
{
lean_object* v_a_14_; lean_object* v___x_16_; uint8_t v_isShared_17_; uint8_t v_isSharedCheck_22_; 
v_a_14_ = lean_ctor_get(v___x_13_, 0);
v_isSharedCheck_22_ = !lean_is_exclusive(v___x_13_);
if (v_isSharedCheck_22_ == 0)
{
v___x_16_ = v___x_13_;
v_isShared_17_ = v_isSharedCheck_22_;
goto v_resetjp_15_;
}
else
{
lean_inc(v_a_14_);
lean_dec(v___x_13_);
v___x_16_ = lean_box(0);
v_isShared_17_ = v_isSharedCheck_22_;
goto v_resetjp_15_;
}
v_resetjp_15_:
{
lean_object* v_zero_18_; lean_object* v___x_20_; 
v_zero_18_ = lean_ctor_get(v_a_14_, 17);
lean_inc_ref(v_zero_18_);
lean_dec(v_a_14_);
if (v_isShared_17_ == 0)
{
lean_ctor_set(v___x_16_, 0, v_zero_18_);
v___x_20_ = v___x_16_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_21_; 
v_reuseFailAlloc_21_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_21_, 0, v_zero_18_);
v___x_20_ = v_reuseFailAlloc_21_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
return v___x_20_;
}
}
}
else
{
lean_object* v_a_23_; lean_object* v___x_25_; uint8_t v_isShared_26_; uint8_t v_isSharedCheck_30_; 
v_a_23_ = lean_ctor_get(v___x_13_, 0);
v_isSharedCheck_30_ = !lean_is_exclusive(v___x_13_);
if (v_isSharedCheck_30_ == 0)
{
v___x_25_ = v___x_13_;
v_isShared_26_ = v_isSharedCheck_30_;
goto v_resetjp_24_;
}
else
{
lean_inc(v_a_23_);
lean_dec(v___x_13_);
v___x_25_ = lean_box(0);
v_isShared_26_ = v_isSharedCheck_30_;
goto v_resetjp_24_;
}
v_resetjp_24_:
{
lean_object* v___x_28_; 
if (v_isShared_26_ == 0)
{
v___x_28_ = v___x_25_;
goto v_reusejp_27_;
}
else
{
lean_object* v_reuseFailAlloc_29_; 
v_reuseFailAlloc_29_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_29_, 0, v_a_23_);
v___x_28_ = v_reuseFailAlloc_29_;
goto v_reusejp_27_;
}
v_reusejp_27_:
{
return v___x_28_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_getZero_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1_ = stack[0].m_obj;
lean_object* v_a_2_ = stack[1].m_obj;
lean_object* v_a_3_ = stack[2].m_obj;
lean_object* v_a_4_ = stack[3].m_obj;
lean_object* v_a_5_ = stack[4].m_obj;
lean_object* v_a_6_ = stack[5].m_obj;
lean_object* v_a_7_ = stack[6].m_obj;
lean_object* v_a_8_ = stack[7].m_obj;
lean_object* v_a_9_ = stack[8].m_obj;
lean_object* v_a_10_ = stack[9].m_obj;
lean_object* v_a_11_ = stack[10].m_obj;
lean_object* v_res_31_;
v_res_31_ = l_Lean_Meta_Grind_Arith_Linear_getZero(v_a_1_, v_a_2_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_, v_a_10_, v_a_11_);
stack->m_obj
 = v_res_31_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getZero___boxed(lean_object* v_a_32_, lean_object* v_a_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Lean_Meta_Grind_Arith_Linear_getZero(v_a_32_, v_a_33_, v_a_34_, v_a_35_, v_a_36_, v_a_37_, v_a_38_, v_a_39_, v_a_40_, v_a_41_, v_a_42_);
lean_dec(v_a_42_);
lean_dec_ref(v_a_41_);
lean_dec(v_a_40_);
lean_dec_ref(v_a_39_);
lean_dec(v_a_38_);
lean_dec_ref(v_a_37_);
lean_dec(v_a_36_);
lean_dec_ref(v_a_35_);
lean_dec(v_a_34_);
lean_dec(v_a_33_);
lean_dec(v_a_32_);
return v_res_44_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_getOne(lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_45_, v_a_46_, v_a_47_, v_a_48_, v_a_49_, v_a_50_, v_a_51_, v_a_52_, v_a_53_, v_a_54_, v_a_55_);
if (lean_obj_tag(v___x_57_) == 0)
{
lean_object* v_a_58_; lean_object* v___x_60_; uint8_t v_isShared_61_; uint8_t v_isSharedCheck_68_; 
v_a_58_ = lean_ctor_get(v___x_57_, 0);
v_isSharedCheck_68_ = !lean_is_exclusive(v___x_57_);
if (v_isSharedCheck_68_ == 0)
{
v___x_60_ = v___x_57_;
v_isShared_61_ = v_isSharedCheck_68_;
goto v_resetjp_59_;
}
else
{
lean_inc(v_a_58_);
lean_dec(v___x_57_);
v___x_60_ = lean_box(0);
v_isShared_61_ = v_isSharedCheck_68_;
goto v_resetjp_59_;
}
v_resetjp_59_:
{
lean_object* v_one_x3f_62_; 
v_one_x3f_62_ = lean_ctor_get(v_a_58_, 19);
lean_inc(v_one_x3f_62_);
lean_dec(v_a_58_);
if (lean_obj_tag(v_one_x3f_62_) == 1)
{
lean_object* v_val_63_; lean_object* v___x_65_; 
v_val_63_ = lean_ctor_get(v_one_x3f_62_, 0);
lean_inc(v_val_63_);
lean_dec_ref_known(v_one_x3f_62_, 1);
if (v_isShared_61_ == 0)
{
lean_ctor_set(v___x_60_, 0, v_val_63_);
v___x_65_ = v___x_60_;
goto v_reusejp_64_;
}
else
{
lean_object* v_reuseFailAlloc_66_; 
v_reuseFailAlloc_66_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_66_, 0, v_val_63_);
v___x_65_ = v_reuseFailAlloc_66_;
goto v_reusejp_64_;
}
v_reusejp_64_:
{
return v___x_65_;
}
}
else
{
lean_object* v___x_67_; 
lean_dec(v_one_x3f_62_);
lean_del_object(v___x_60_);
v___x_67_ = l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg(v_a_52_, v_a_53_, v_a_54_, v_a_55_);
return v___x_67_;
}
}
}
else
{
lean_object* v_a_69_; lean_object* v___x_71_; uint8_t v_isShared_72_; uint8_t v_isSharedCheck_76_; 
v_a_69_ = lean_ctor_get(v___x_57_, 0);
v_isSharedCheck_76_ = !lean_is_exclusive(v___x_57_);
if (v_isSharedCheck_76_ == 0)
{
v___x_71_ = v___x_57_;
v_isShared_72_ = v_isSharedCheck_76_;
goto v_resetjp_70_;
}
else
{
lean_inc(v_a_69_);
lean_dec(v___x_57_);
v___x_71_ = lean_box(0);
v_isShared_72_ = v_isSharedCheck_76_;
goto v_resetjp_70_;
}
v_resetjp_70_:
{
lean_object* v___x_74_; 
if (v_isShared_72_ == 0)
{
v___x_74_ = v___x_71_;
goto v_reusejp_73_;
}
else
{
lean_object* v_reuseFailAlloc_75_; 
v_reuseFailAlloc_75_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_75_, 0, v_a_69_);
v___x_74_ = v_reuseFailAlloc_75_;
goto v_reusejp_73_;
}
v_reusejp_73_:
{
return v___x_74_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_getOne_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_45_ = stack[0].m_obj;
lean_object* v_a_46_ = stack[1].m_obj;
lean_object* v_a_47_ = stack[2].m_obj;
lean_object* v_a_48_ = stack[3].m_obj;
lean_object* v_a_49_ = stack[4].m_obj;
lean_object* v_a_50_ = stack[5].m_obj;
lean_object* v_a_51_ = stack[6].m_obj;
lean_object* v_a_52_ = stack[7].m_obj;
lean_object* v_a_53_ = stack[8].m_obj;
lean_object* v_a_54_ = stack[9].m_obj;
lean_object* v_a_55_ = stack[10].m_obj;
lean_object* v_res_77_;
v_res_77_ = l_Lean_Meta_Grind_Arith_Linear_getOne(v_a_45_, v_a_46_, v_a_47_, v_a_48_, v_a_49_, v_a_50_, v_a_51_, v_a_52_, v_a_53_, v_a_54_, v_a_55_);
stack->m_obj
 = v_res_77_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOne___boxed(lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Lean_Meta_Grind_Arith_Linear_getOne(v_a_78_, v_a_79_, v_a_80_, v_a_81_, v_a_82_, v_a_83_, v_a_84_, v_a_85_, v_a_86_, v_a_87_, v_a_88_);
lean_dec(v_a_88_);
lean_dec_ref(v_a_87_);
lean_dec(v_a_86_);
lean_dec_ref(v_a_85_);
lean_dec(v_a_84_);
lean_dec_ref(v_a_83_);
lean_dec(v_a_82_);
lean_dec_ref(v_a_81_);
lean_dec(v_a_80_);
lean_dec(v_a_79_);
lean_dec(v_a_78_);
return v_res_90_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_isCommRing(lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_91_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_, v_a_101_);
if (lean_obj_tag(v___x_103_) == 0)
{
lean_object* v_a_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_119_; 
v_a_104_ = lean_ctor_get(v___x_103_, 0);
v_isSharedCheck_119_ = !lean_is_exclusive(v___x_103_);
if (v_isSharedCheck_119_ == 0)
{
v___x_106_ = v___x_103_;
v_isShared_107_ = v_isSharedCheck_119_;
goto v_resetjp_105_;
}
else
{
lean_inc(v_a_104_);
lean_dec(v___x_103_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_119_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
lean_object* v_ringId_x3f_108_; 
v_ringId_x3f_108_ = lean_ctor_get(v_a_104_, 1);
lean_inc(v_ringId_x3f_108_);
lean_dec(v_a_104_);
if (lean_obj_tag(v_ringId_x3f_108_) == 0)
{
uint8_t v___x_109_; lean_object* v___x_110_; lean_object* v___x_112_; 
v___x_109_ = 0;
v___x_110_ = lean_box(v___x_109_);
if (v_isShared_107_ == 0)
{
lean_ctor_set(v___x_106_, 0, v___x_110_);
v___x_112_ = v___x_106_;
goto v_reusejp_111_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v___x_110_);
v___x_112_ = v_reuseFailAlloc_113_;
goto v_reusejp_111_;
}
v_reusejp_111_:
{
return v___x_112_;
}
}
else
{
uint8_t v___x_114_; lean_object* v___x_115_; lean_object* v___x_117_; 
lean_dec_ref_known(v_ringId_x3f_108_, 1);
v___x_114_ = 1;
v___x_115_ = lean_box(v___x_114_);
if (v_isShared_107_ == 0)
{
lean_ctor_set(v___x_106_, 0, v___x_115_);
v___x_117_ = v___x_106_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v___x_115_);
v___x_117_ = v_reuseFailAlloc_118_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
return v___x_117_;
}
}
}
}
else
{
lean_object* v_a_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_127_; 
v_a_120_ = lean_ctor_get(v___x_103_, 0);
v_isSharedCheck_127_ = !lean_is_exclusive(v___x_103_);
if (v_isSharedCheck_127_ == 0)
{
v___x_122_ = v___x_103_;
v_isShared_123_ = v_isSharedCheck_127_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_a_120_);
lean_dec(v___x_103_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_127_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v___x_125_; 
if (v_isShared_123_ == 0)
{
v___x_125_ = v___x_122_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v_a_120_);
v___x_125_ = v_reuseFailAlloc_126_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
return v___x_125_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_isCommRing_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_91_ = stack[0].m_obj;
lean_object* v_a_92_ = stack[1].m_obj;
lean_object* v_a_93_ = stack[2].m_obj;
lean_object* v_a_94_ = stack[3].m_obj;
lean_object* v_a_95_ = stack[4].m_obj;
lean_object* v_a_96_ = stack[5].m_obj;
lean_object* v_a_97_ = stack[6].m_obj;
lean_object* v_a_98_ = stack[7].m_obj;
lean_object* v_a_99_ = stack[8].m_obj;
lean_object* v_a_100_ = stack[9].m_obj;
lean_object* v_a_101_ = stack[10].m_obj;
lean_object* v_res_128_;
v_res_128_ = l_Lean_Meta_Grind_Arith_Linear_isCommRing(v_a_91_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_, v_a_101_);
stack->m_obj
 = v_res_128_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isCommRing___boxed(lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Lean_Meta_Grind_Arith_Linear_isCommRing(v_a_129_, v_a_130_, v_a_131_, v_a_132_, v_a_133_, v_a_134_, v_a_135_, v_a_136_, v_a_137_, v_a_138_, v_a_139_);
lean_dec(v_a_139_);
lean_dec_ref(v_a_138_);
lean_dec(v_a_137_);
lean_dec_ref(v_a_136_);
lean_dec(v_a_135_);
lean_dec_ref(v_a_134_);
lean_dec(v_a_133_);
lean_dec_ref(v_a_132_);
lean_dec(v_a_131_);
lean_dec(v_a_130_);
lean_dec(v_a_129_);
return v_res_141_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_isOrderedCommRing(lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_){
_start:
{
lean_object* v___x_154_; 
v___x_154_ = l_Lean_Meta_Grind_Arith_Linear_isCommRing(v_a_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_, v_a_149_, v_a_150_, v_a_151_, v_a_152_);
if (lean_obj_tag(v___x_154_) == 0)
{
lean_object* v_a_155_; lean_object* v___x_156_; 
v_a_155_ = lean_ctor_get(v___x_154_, 0);
lean_inc(v_a_155_);
lean_dec_ref_known(v___x_154_, 1);
v___x_156_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_, v_a_149_, v_a_150_, v_a_151_, v_a_152_);
if (lean_obj_tag(v___x_156_) == 0)
{
uint8_t v___x_157_; 
v___x_157_ = lean_unbox(v_a_155_);
if (v___x_157_ == 0)
{
lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_164_; 
v_isSharedCheck_164_ = !lean_is_exclusive(v___x_156_);
if (v_isSharedCheck_164_ == 0)
{
lean_object* v_unused_165_; 
v_unused_165_ = lean_ctor_get(v___x_156_, 0);
lean_dec(v_unused_165_);
v___x_159_ = v___x_156_;
v_isShared_160_ = v_isSharedCheck_164_;
goto v_resetjp_158_;
}
else
{
lean_dec(v___x_156_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_164_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
lean_object* v___x_162_; 
if (v_isShared_160_ == 0)
{
lean_ctor_set(v___x_159_, 0, v_a_155_);
v___x_162_ = v___x_159_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v_a_155_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
return v___x_162_;
}
}
}
else
{
lean_object* v_a_166_; lean_object* v___x_168_; uint8_t v_isShared_169_; uint8_t v_isSharedCheck_179_; 
v_a_166_ = lean_ctor_get(v___x_156_, 0);
v_isSharedCheck_179_ = !lean_is_exclusive(v___x_156_);
if (v_isSharedCheck_179_ == 0)
{
v___x_168_ = v___x_156_;
v_isShared_169_ = v_isSharedCheck_179_;
goto v_resetjp_167_;
}
else
{
lean_inc(v_a_166_);
lean_dec(v___x_156_);
v___x_168_ = lean_box(0);
v_isShared_169_ = v_isSharedCheck_179_;
goto v_resetjp_167_;
}
v_resetjp_167_:
{
lean_object* v_orderedRingInst_x3f_170_; 
v_orderedRingInst_x3f_170_ = lean_ctor_get(v_a_166_, 14);
lean_inc(v_orderedRingInst_x3f_170_);
lean_dec(v_a_166_);
if (lean_obj_tag(v_orderedRingInst_x3f_170_) == 0)
{
uint8_t v___x_171_; lean_object* v___x_172_; lean_object* v___x_174_; 
lean_dec(v_a_155_);
v___x_171_ = 0;
v___x_172_ = lean_box(v___x_171_);
if (v_isShared_169_ == 0)
{
lean_ctor_set(v___x_168_, 0, v___x_172_);
v___x_174_ = v___x_168_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v___x_172_);
v___x_174_ = v_reuseFailAlloc_175_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
return v___x_174_;
}
}
else
{
lean_object* v___x_177_; 
lean_dec_ref_known(v_orderedRingInst_x3f_170_, 1);
if (v_isShared_169_ == 0)
{
lean_ctor_set(v___x_168_, 0, v_a_155_);
v___x_177_ = v___x_168_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v_a_155_);
v___x_177_ = v_reuseFailAlloc_178_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
return v___x_177_;
}
}
}
}
}
else
{
lean_object* v_a_180_; lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_187_; 
lean_dec(v_a_155_);
v_a_180_ = lean_ctor_get(v___x_156_, 0);
v_isSharedCheck_187_ = !lean_is_exclusive(v___x_156_);
if (v_isSharedCheck_187_ == 0)
{
v___x_182_ = v___x_156_;
v_isShared_183_ = v_isSharedCheck_187_;
goto v_resetjp_181_;
}
else
{
lean_inc(v_a_180_);
lean_dec(v___x_156_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_187_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
lean_object* v___x_185_; 
if (v_isShared_183_ == 0)
{
v___x_185_ = v___x_182_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v_a_180_);
v___x_185_ = v_reuseFailAlloc_186_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
return v___x_185_;
}
}
}
}
else
{
return v___x_154_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_isOrderedCommRing_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_142_ = stack[0].m_obj;
lean_object* v_a_143_ = stack[1].m_obj;
lean_object* v_a_144_ = stack[2].m_obj;
lean_object* v_a_145_ = stack[3].m_obj;
lean_object* v_a_146_ = stack[4].m_obj;
lean_object* v_a_147_ = stack[5].m_obj;
lean_object* v_a_148_ = stack[6].m_obj;
lean_object* v_a_149_ = stack[7].m_obj;
lean_object* v_a_150_ = stack[8].m_obj;
lean_object* v_a_151_ = stack[9].m_obj;
lean_object* v_a_152_ = stack[10].m_obj;
lean_object* v_res_188_;
v_res_188_ = l_Lean_Meta_Grind_Arith_Linear_isOrderedCommRing(v_a_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_, v_a_149_, v_a_150_, v_a_151_, v_a_152_);
stack->m_obj
 = v_res_188_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isOrderedCommRing___boxed(lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_Lean_Meta_Grind_Arith_Linear_isOrderedCommRing(v_a_189_, v_a_190_, v_a_191_, v_a_192_, v_a_193_, v_a_194_, v_a_195_, v_a_196_, v_a_197_, v_a_198_, v_a_199_);
lean_dec(v_a_199_);
lean_dec_ref(v_a_198_);
lean_dec(v_a_197_);
lean_dec_ref(v_a_196_);
lean_dec(v_a_195_);
lean_dec_ref(v_a_194_);
lean_dec(v_a_193_);
lean_dec_ref(v_a_192_);
lean_dec(v_a_191_);
lean_dec(v_a_190_);
lean_dec(v_a_189_);
return v_res_201_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_isLinearOrder(lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_);
if (lean_obj_tag(v___x_214_) == 0)
{
lean_object* v_a_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_230_; 
v_a_215_ = lean_ctor_get(v___x_214_, 0);
v_isSharedCheck_230_ = !lean_is_exclusive(v___x_214_);
if (v_isSharedCheck_230_ == 0)
{
v___x_217_ = v___x_214_;
v_isShared_218_ = v_isSharedCheck_230_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_a_215_);
lean_dec(v___x_214_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_230_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v_isLinearInst_x3f_219_; 
v_isLinearInst_x3f_219_ = lean_ctor_get(v_a_215_, 10);
lean_inc(v_isLinearInst_x3f_219_);
lean_dec(v_a_215_);
if (lean_obj_tag(v_isLinearInst_x3f_219_) == 0)
{
uint8_t v___x_220_; lean_object* v___x_221_; lean_object* v___x_223_; 
v___x_220_ = 0;
v___x_221_ = lean_box(v___x_220_);
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 0, v___x_221_);
v___x_223_ = v___x_217_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v___x_221_);
v___x_223_ = v_reuseFailAlloc_224_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
return v___x_223_;
}
}
else
{
uint8_t v___x_225_; lean_object* v___x_226_; lean_object* v___x_228_; 
lean_dec_ref_known(v_isLinearInst_x3f_219_, 1);
v___x_225_ = 1;
v___x_226_ = lean_box(v___x_225_);
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 0, v___x_226_);
v___x_228_ = v___x_217_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v___x_226_);
v___x_228_ = v_reuseFailAlloc_229_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
return v___x_228_;
}
}
}
}
else
{
lean_object* v_a_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_238_; 
v_a_231_ = lean_ctor_get(v___x_214_, 0);
v_isSharedCheck_238_ = !lean_is_exclusive(v___x_214_);
if (v_isSharedCheck_238_ == 0)
{
v___x_233_ = v___x_214_;
v_isShared_234_ = v_isSharedCheck_238_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_a_231_);
lean_dec(v___x_214_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_238_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v___x_236_; 
if (v_isShared_234_ == 0)
{
v___x_236_ = v___x_233_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v_a_231_);
v___x_236_ = v_reuseFailAlloc_237_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
return v___x_236_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_isLinearOrder_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_202_ = stack[0].m_obj;
lean_object* v_a_203_ = stack[1].m_obj;
lean_object* v_a_204_ = stack[2].m_obj;
lean_object* v_a_205_ = stack[3].m_obj;
lean_object* v_a_206_ = stack[4].m_obj;
lean_object* v_a_207_ = stack[5].m_obj;
lean_object* v_a_208_ = stack[6].m_obj;
lean_object* v_a_209_ = stack[7].m_obj;
lean_object* v_a_210_ = stack[8].m_obj;
lean_object* v_a_211_ = stack[9].m_obj;
lean_object* v_a_212_ = stack[10].m_obj;
lean_object* v_res_239_;
v_res_239_ = l_Lean_Meta_Grind_Arith_Linear_isLinearOrder(v_a_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_);
stack->m_obj
 = v_res_239_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isLinearOrder___boxed(lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Lean_Meta_Grind_Arith_Linear_isLinearOrder(v_a_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_, v_a_245_, v_a_246_, v_a_247_, v_a_248_, v_a_249_, v_a_250_);
lean_dec(v_a_250_);
lean_dec_ref(v_a_249_);
lean_dec(v_a_248_);
lean_dec_ref(v_a_247_);
lean_dec(v_a_246_);
lean_dec_ref(v_a_245_);
lean_dec(v_a_244_);
lean_dec_ref(v_a_243_);
lean_dec(v_a_242_);
lean_dec(v_a_241_);
lean_dec(v_a_240_);
return v_res_252_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_hasNoNatZeroDivisors(lean_object* v_a_253_, lean_object* v_a_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_){
_start:
{
lean_object* v___x_265_; 
v___x_265_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_253_, v_a_254_, v_a_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_, v_a_263_);
if (lean_obj_tag(v___x_265_) == 0)
{
lean_object* v_a_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_281_; 
v_a_266_ = lean_ctor_get(v___x_265_, 0);
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_265_);
if (v_isSharedCheck_281_ == 0)
{
v___x_268_ = v___x_265_;
v_isShared_269_ = v_isSharedCheck_281_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_a_266_);
lean_dec(v___x_265_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_281_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v_noNatDivInst_x3f_270_; 
v_noNatDivInst_x3f_270_ = lean_ctor_get(v_a_266_, 11);
lean_inc(v_noNatDivInst_x3f_270_);
lean_dec(v_a_266_);
if (lean_obj_tag(v_noNatDivInst_x3f_270_) == 0)
{
uint8_t v___x_271_; lean_object* v___x_272_; lean_object* v___x_274_; 
v___x_271_ = 0;
v___x_272_ = lean_box(v___x_271_);
if (v_isShared_269_ == 0)
{
lean_ctor_set(v___x_268_, 0, v___x_272_);
v___x_274_ = v___x_268_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v___x_272_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
else
{
uint8_t v___x_276_; lean_object* v___x_277_; lean_object* v___x_279_; 
lean_dec_ref_known(v_noNatDivInst_x3f_270_, 1);
v___x_276_ = 1;
v___x_277_ = lean_box(v___x_276_);
if (v_isShared_269_ == 0)
{
lean_ctor_set(v___x_268_, 0, v___x_277_);
v___x_279_ = v___x_268_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v___x_277_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
return v___x_279_;
}
}
}
}
else
{
lean_object* v_a_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_289_; 
v_a_282_ = lean_ctor_get(v___x_265_, 0);
v_isSharedCheck_289_ = !lean_is_exclusive(v___x_265_);
if (v_isSharedCheck_289_ == 0)
{
v___x_284_ = v___x_265_;
v_isShared_285_ = v_isSharedCheck_289_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_a_282_);
lean_dec(v___x_265_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_289_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v___x_287_; 
if (v_isShared_285_ == 0)
{
v___x_287_ = v___x_284_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v_a_282_);
v___x_287_ = v_reuseFailAlloc_288_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
return v___x_287_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_hasNoNatZeroDivisors_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_253_ = stack[0].m_obj;
lean_object* v_a_254_ = stack[1].m_obj;
lean_object* v_a_255_ = stack[2].m_obj;
lean_object* v_a_256_ = stack[3].m_obj;
lean_object* v_a_257_ = stack[4].m_obj;
lean_object* v_a_258_ = stack[5].m_obj;
lean_object* v_a_259_ = stack[6].m_obj;
lean_object* v_a_260_ = stack[7].m_obj;
lean_object* v_a_261_ = stack[8].m_obj;
lean_object* v_a_262_ = stack[9].m_obj;
lean_object* v_a_263_ = stack[10].m_obj;
lean_object* v_res_290_;
v_res_290_ = l_Lean_Meta_Grind_Arith_Linear_hasNoNatZeroDivisors(v_a_253_, v_a_254_, v_a_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_, v_a_263_);
stack->m_obj
 = v_res_290_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_hasNoNatZeroDivisors___boxed(lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_Lean_Meta_Grind_Arith_Linear_hasNoNatZeroDivisors(v_a_291_, v_a_292_, v_a_293_, v_a_294_, v_a_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_);
lean_dec(v_a_301_);
lean_dec_ref(v_a_300_);
lean_dec(v_a_299_);
lean_dec_ref(v_a_298_);
lean_dec(v_a_297_);
lean_dec_ref(v_a_296_);
lean_dec(v_a_295_);
lean_dec_ref(v_a_294_);
lean_dec(v_a_293_);
lean_dec(v_a_292_);
lean_dec(v_a_291_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_304_, lean_object* v_vals_305_, lean_object* v_i_306_, lean_object* v_k_307_){
_start:
{
lean_object* v___x_308_; uint8_t v___x_309_; 
v___x_308_ = lean_array_get_size(v_keys_304_);
v___x_309_ = lean_nat_dec_lt(v_i_306_, v___x_308_);
if (v___x_309_ == 0)
{
lean_object* v___x_310_; 
lean_dec(v_i_306_);
v___x_310_ = lean_box(0);
return v___x_310_;
}
else
{
lean_object* v_k_x27_311_; size_t v___x_312_; size_t v___x_313_; uint8_t v___x_314_; 
v_k_x27_311_ = lean_array_fget_borrowed(v_keys_304_, v_i_306_);
v___x_312_ = lean_ptr_addr(v_k_307_);
v___x_313_ = lean_ptr_addr(v_k_x27_311_);
v___x_314_ = lean_usize_dec_eq(v___x_312_, v___x_313_);
if (v___x_314_ == 0)
{
lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_315_ = lean_unsigned_to_nat(1u);
v___x_316_ = lean_nat_add(v_i_306_, v___x_315_);
lean_dec(v_i_306_);
v_i_306_ = v___x_316_;
goto _start;
}
else
{
lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_318_ = lean_array_fget_borrowed(v_vals_305_, v_i_306_);
lean_dec(v_i_306_);
lean_inc(v___x_318_);
v___x_319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_319_, 0, v___x_318_);
return v___x_319_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_320_, lean_object* v_vals_321_, lean_object* v_i_322_, lean_object* v_k_323_){
_start:
{
lean_object* v_res_324_; 
v_res_324_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_320_, v_vals_321_, v_i_322_, v_k_323_);
lean_dec_ref(v_k_323_);
lean_dec_ref(v_vals_321_);
lean_dec_ref(v_keys_320_);
return v_res_324_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg(lean_object* v_x_325_, size_t v_x_326_, lean_object* v_x_327_){
_start:
{
if (lean_obj_tag(v_x_325_) == 0)
{
lean_object* v_es_328_; lean_object* v___x_329_; size_t v___x_330_; size_t v___x_331_; lean_object* v_j_332_; lean_object* v___x_333_; 
v_es_328_ = lean_ctor_get(v_x_325_, 0);
v___x_329_ = lean_box(2);
v___x_330_ = ((size_t)31ULL);
v___x_331_ = lean_usize_land(v_x_326_, v___x_330_);
v_j_332_ = lean_usize_to_nat(v___x_331_);
v___x_333_ = lean_array_get_borrowed(v___x_329_, v_es_328_, v_j_332_);
lean_dec(v_j_332_);
switch(lean_obj_tag(v___x_333_))
{
case 0:
{
lean_object* v_key_334_; lean_object* v_val_335_; size_t v___x_336_; size_t v___x_337_; uint8_t v___x_338_; 
v_key_334_ = lean_ctor_get(v___x_333_, 0);
v_val_335_ = lean_ctor_get(v___x_333_, 1);
v___x_336_ = lean_ptr_addr(v_x_327_);
v___x_337_ = lean_ptr_addr(v_key_334_);
v___x_338_ = lean_usize_dec_eq(v___x_336_, v___x_337_);
if (v___x_338_ == 0)
{
lean_object* v___x_339_; 
v___x_339_ = lean_box(0);
return v___x_339_;
}
else
{
lean_object* v___x_340_; 
lean_inc(v_val_335_);
v___x_340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_340_, 0, v_val_335_);
return v___x_340_;
}
}
case 1:
{
lean_object* v_node_341_; size_t v___x_342_; size_t v___x_343_; 
v_node_341_ = lean_ctor_get(v___x_333_, 0);
v___x_342_ = ((size_t)5ULL);
v___x_343_ = lean_usize_shift_right(v_x_326_, v___x_342_);
v_x_325_ = v_node_341_;
v_x_326_ = v___x_343_;
goto _start;
}
default: 
{
lean_object* v___x_345_; 
v___x_345_ = lean_box(0);
return v___x_345_;
}
}
}
else
{
lean_object* v_ks_346_; lean_object* v_vs_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v_ks_346_ = lean_ctor_get(v_x_325_, 0);
v_vs_347_ = lean_ctor_get(v_x_325_, 1);
v___x_348_ = lean_unsigned_to_nat(0u);
v___x_349_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_346_, v_vs_347_, v___x_348_, v_x_327_);
return v___x_349_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_325_ = stack[0].m_obj;
size_t v_x_326_ = stack[1].m_num;
lean_object* v_x_327_ = stack[2].m_obj;
lean_object* v_res_350_;
v_res_350_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg(v_x_325_, v_x_326_, v_x_327_);
stack->m_obj
 = v_res_350_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_351_, lean_object* v_x_352_, lean_object* v_x_353_){
_start:
{
size_t v_x_916__boxed_354_; lean_object* v_res_355_; 
v_x_916__boxed_354_ = lean_unbox_usize(v_x_352_);
lean_dec(v_x_352_);
v_res_355_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg(v_x_351_, v_x_916__boxed_354_, v_x_353_);
lean_dec_ref(v_x_353_);
lean_dec_ref(v_x_351_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0___redArg(lean_object* v_x_356_, lean_object* v_x_357_){
_start:
{
size_t v___x_358_; size_t v___x_359_; size_t v___x_360_; uint64_t v___x_361_; size_t v___x_362_; lean_object* v___x_363_; 
v___x_358_ = lean_ptr_addr(v_x_357_);
v___x_359_ = ((size_t)3ULL);
v___x_360_ = lean_usize_shift_right(v___x_358_, v___x_359_);
v___x_361_ = lean_usize_to_uint64(v___x_360_);
v___x_362_ = lean_uint64_to_usize(v___x_361_);
v___x_363_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg(v_x_356_, v___x_362_, v_x_357_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0___redArg___boxed(lean_object* v_x_364_, lean_object* v_x_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0___redArg(v_x_364_, v_x_365_);
lean_dec_ref(v_x_365_);
lean_dec_ref(v_x_364_);
return v_res_366_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg(lean_object* v_e_367_, lean_object* v_a_368_, lean_object* v_a_369_){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_368_, v_a_369_);
if (lean_obj_tag(v___x_371_) == 0)
{
lean_object* v_a_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_381_; 
v_a_372_ = lean_ctor_get(v___x_371_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_371_);
if (v_isSharedCheck_381_ == 0)
{
v___x_374_ = v___x_371_;
v_isShared_375_ = v_isSharedCheck_381_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_a_372_);
lean_dec(v___x_371_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_381_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v_exprToStructId_376_; lean_object* v___x_377_; lean_object* v___x_379_; 
v_exprToStructId_376_ = lean_ctor_get(v_a_372_, 2);
lean_inc_ref(v_exprToStructId_376_);
lean_dec(v_a_372_);
v___x_377_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0___redArg(v_exprToStructId_376_, v_e_367_);
lean_dec_ref(v_exprToStructId_376_);
if (v_isShared_375_ == 0)
{
lean_ctor_set(v___x_374_, 0, v___x_377_);
v___x_379_ = v___x_374_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v___x_377_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
}
else
{
lean_object* v_a_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_389_; 
v_a_382_ = lean_ctor_get(v___x_371_, 0);
v_isSharedCheck_389_ = !lean_is_exclusive(v___x_371_);
if (v_isSharedCheck_389_ == 0)
{
v___x_384_ = v___x_371_;
v_isShared_385_ = v_isSharedCheck_389_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_a_382_);
lean_dec(v___x_371_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_389_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v___x_387_; 
if (v_isShared_385_ == 0)
{
v___x_387_ = v___x_384_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v_a_382_);
v___x_387_ = v_reuseFailAlloc_388_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
return v___x_387_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_367_ = stack[0].m_obj;
lean_object* v_a_368_ = stack[1].m_obj;
lean_object* v_a_369_ = stack[2].m_obj;
lean_object* v_res_390_;
v_res_390_ = l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg(v_e_367_, v_a_368_, v_a_369_);
stack->m_obj
 = v_res_390_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg___boxed(lean_object* v_e_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg(v_e_391_, v_a_392_, v_a_393_);
lean_dec_ref(v_a_393_);
lean_dec(v_a_392_);
lean_dec_ref(v_e_391_);
return v_res_395_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f(lean_object* v_e_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_){
_start:
{
lean_object* v___x_408_; 
v___x_408_ = l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg(v_e_396_, v_a_397_, v_a_405_);
return v___x_408_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_396_ = stack[0].m_obj;
lean_object* v_a_397_ = stack[1].m_obj;
lean_object* v_a_398_ = stack[2].m_obj;
lean_object* v_a_399_ = stack[3].m_obj;
lean_object* v_a_400_ = stack[4].m_obj;
lean_object* v_a_401_ = stack[5].m_obj;
lean_object* v_a_402_ = stack[6].m_obj;
lean_object* v_a_403_ = stack[7].m_obj;
lean_object* v_a_404_ = stack[8].m_obj;
lean_object* v_a_405_ = stack[9].m_obj;
lean_object* v_a_406_ = stack[10].m_obj;
lean_object* v_res_409_;
v_res_409_ = l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f(v_e_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_);
stack->m_obj
 = v_res_409_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___boxed(lean_object* v_e_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f(v_e_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_, v_a_418_, v_a_419_, v_a_420_);
lean_dec(v_a_420_);
lean_dec_ref(v_a_419_);
lean_dec(v_a_418_);
lean_dec_ref(v_a_417_);
lean_dec(v_a_416_);
lean_dec_ref(v_a_415_);
lean_dec(v_a_414_);
lean_dec_ref(v_a_413_);
lean_dec(v_a_412_);
lean_dec(v_a_411_);
lean_dec_ref(v_e_410_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0(lean_object* v_00_u03b2_423_, lean_object* v_x_424_, lean_object* v_x_425_){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0___redArg(v_x_424_, v_x_425_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0___boxed(lean_object* v_00_u03b2_427_, lean_object* v_x_428_, lean_object* v_x_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0(v_00_u03b2_427_, v_x_428_, v_x_429_);
lean_dec_ref(v_x_429_);
lean_dec_ref(v_x_428_);
return v_res_430_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_431_, lean_object* v_x_432_, size_t v_x_433_, lean_object* v_x_434_){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg(v_x_432_, v_x_433_, v_x_434_);
return v___x_435_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_432_ = stack[1].m_obj;
size_t v_x_433_ = stack[2].m_num;
lean_object* v_x_434_ = stack[3].m_obj;
lean_object* v_res_436_;
v_res_436_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0(lean_box(0), v_x_432_, v_x_433_, v_x_434_);
stack->m_obj
 = v_res_436_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_437_, lean_object* v_x_438_, lean_object* v_x_439_, lean_object* v_x_440_){
_start:
{
size_t v_x_1102__boxed_441_; lean_object* v_res_442_; 
v_x_1102__boxed_441_ = lean_unbox_usize(v_x_439_);
lean_dec(v_x_439_);
v_res_442_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0(v_00_u03b2_437_, v_x_438_, v_x_1102__boxed_441_, v_x_440_);
lean_dec_ref(v_x_440_);
lean_dec_ref(v_x_438_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_443_, lean_object* v_keys_444_, lean_object* v_vals_445_, lean_object* v_heq_446_, lean_object* v_i_447_, lean_object* v_k_448_){
_start:
{
lean_object* v___x_449_; 
v___x_449_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_444_, v_vals_445_, v_i_447_, v_k_448_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_450_, lean_object* v_keys_451_, lean_object* v_vals_452_, lean_object* v_heq_453_, lean_object* v_i_454_, lean_object* v_k_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_450_, v_keys_451_, v_vals_452_, v_heq_453_, v_i_454_, v_k_455_);
lean_dec_ref(v_k_455_);
lean_dec_ref(v_vals_452_);
lean_dec_ref(v_keys_451_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_457_, lean_object* v_x_458_, lean_object* v_x_459_, lean_object* v_x_460_){
_start:
{
lean_object* v_ks_461_; lean_object* v_vs_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_488_; 
v_ks_461_ = lean_ctor_get(v_x_457_, 0);
v_vs_462_ = lean_ctor_get(v_x_457_, 1);
v_isSharedCheck_488_ = !lean_is_exclusive(v_x_457_);
if (v_isSharedCheck_488_ == 0)
{
v___x_464_ = v_x_457_;
v_isShared_465_ = v_isSharedCheck_488_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_vs_462_);
lean_inc(v_ks_461_);
lean_dec(v_x_457_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_488_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_466_; uint8_t v___x_467_; 
v___x_466_ = lean_array_get_size(v_ks_461_);
v___x_467_ = lean_nat_dec_lt(v_x_458_, v___x_466_);
if (v___x_467_ == 0)
{
lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_471_; 
lean_dec(v_x_458_);
v___x_468_ = lean_array_push(v_ks_461_, v_x_459_);
v___x_469_ = lean_array_push(v_vs_462_, v_x_460_);
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 1, v___x_469_);
lean_ctor_set(v___x_464_, 0, v___x_468_);
v___x_471_ = v___x_464_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v___x_468_);
lean_ctor_set(v_reuseFailAlloc_472_, 1, v___x_469_);
v___x_471_ = v_reuseFailAlloc_472_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
return v___x_471_;
}
}
else
{
lean_object* v_k_x27_473_; size_t v___x_474_; size_t v___x_475_; uint8_t v___x_476_; 
v_k_x27_473_ = lean_array_fget_borrowed(v_ks_461_, v_x_458_);
v___x_474_ = lean_ptr_addr(v_x_459_);
v___x_475_ = lean_ptr_addr(v_k_x27_473_);
v___x_476_ = lean_usize_dec_eq(v___x_474_, v___x_475_);
if (v___x_476_ == 0)
{
lean_object* v___x_478_; 
if (v_isShared_465_ == 0)
{
v___x_478_ = v___x_464_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v_ks_461_);
lean_ctor_set(v_reuseFailAlloc_482_, 1, v_vs_462_);
v___x_478_ = v_reuseFailAlloc_482_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_479_ = lean_unsigned_to_nat(1u);
v___x_480_ = lean_nat_add(v_x_458_, v___x_479_);
lean_dec(v_x_458_);
v_x_457_ = v___x_478_;
v_x_458_ = v___x_480_;
goto _start;
}
}
else
{
lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_486_; 
v___x_483_ = lean_array_fset(v_ks_461_, v_x_458_, v_x_459_);
v___x_484_ = lean_array_fset(v_vs_462_, v_x_458_, v_x_460_);
lean_dec(v_x_458_);
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 1, v___x_484_);
lean_ctor_set(v___x_464_, 0, v___x_483_);
v___x_486_ = v___x_464_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v___x_483_);
lean_ctor_set(v_reuseFailAlloc_487_, 1, v___x_484_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
return v___x_486_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1___redArg(lean_object* v_n_489_, lean_object* v_k_490_, lean_object* v_v_491_){
_start:
{
lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_492_ = lean_unsigned_to_nat(0u);
v___x_493_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1_spec__2___redArg(v_n_489_, v___x_492_, v_k_490_, v_v_491_);
return v___x_493_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_494_; 
v___x_494_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_494_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg(lean_object* v_x_495_, size_t v_x_496_, size_t v_x_497_, lean_object* v_x_498_, lean_object* v_x_499_){
_start:
{
if (lean_obj_tag(v_x_495_) == 0)
{
lean_object* v_es_500_; size_t v___x_501_; size_t v___x_502_; lean_object* v_j_503_; lean_object* v___x_504_; uint8_t v___x_505_; 
v_es_500_ = lean_ctor_get(v_x_495_, 0);
v___x_501_ = ((size_t)31ULL);
v___x_502_ = lean_usize_land(v_x_496_, v___x_501_);
v_j_503_ = lean_usize_to_nat(v___x_502_);
v___x_504_ = lean_array_get_size(v_es_500_);
v___x_505_ = lean_nat_dec_lt(v_j_503_, v___x_504_);
if (v___x_505_ == 0)
{
lean_dec(v_j_503_);
lean_dec(v_x_499_);
lean_dec_ref(v_x_498_);
return v_x_495_;
}
else
{
lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_546_; 
lean_inc_ref(v_es_500_);
v_isSharedCheck_546_ = !lean_is_exclusive(v_x_495_);
if (v_isSharedCheck_546_ == 0)
{
lean_object* v_unused_547_; 
v_unused_547_ = lean_ctor_get(v_x_495_, 0);
lean_dec(v_unused_547_);
v___x_507_ = v_x_495_;
v_isShared_508_ = v_isSharedCheck_546_;
goto v_resetjp_506_;
}
else
{
lean_dec(v_x_495_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_546_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v_v_509_; lean_object* v___x_510_; lean_object* v_xs_x27_511_; lean_object* v___y_513_; 
v_v_509_ = lean_array_fget(v_es_500_, v_j_503_);
v___x_510_ = lean_box(0);
v_xs_x27_511_ = lean_array_fset(v_es_500_, v_j_503_, v___x_510_);
switch(lean_obj_tag(v_v_509_))
{
case 0:
{
lean_object* v_key_518_; lean_object* v_val_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_531_; 
v_key_518_ = lean_ctor_get(v_v_509_, 0);
v_val_519_ = lean_ctor_get(v_v_509_, 1);
v_isSharedCheck_531_ = !lean_is_exclusive(v_v_509_);
if (v_isSharedCheck_531_ == 0)
{
v___x_521_ = v_v_509_;
v_isShared_522_ = v_isSharedCheck_531_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_val_519_);
lean_inc(v_key_518_);
lean_dec(v_v_509_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_531_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
size_t v___x_523_; size_t v___x_524_; uint8_t v___x_525_; 
v___x_523_ = lean_ptr_addr(v_x_498_);
v___x_524_ = lean_ptr_addr(v_key_518_);
v___x_525_ = lean_usize_dec_eq(v___x_523_, v___x_524_);
if (v___x_525_ == 0)
{
lean_object* v___x_526_; lean_object* v___x_527_; 
lean_del_object(v___x_521_);
v___x_526_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_518_, v_val_519_, v_x_498_, v_x_499_);
v___x_527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_527_, 0, v___x_526_);
v___y_513_ = v___x_527_;
goto v___jp_512_;
}
else
{
lean_object* v___x_529_; 
lean_dec(v_val_519_);
lean_dec(v_key_518_);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 1, v_x_499_);
lean_ctor_set(v___x_521_, 0, v_x_498_);
v___x_529_ = v___x_521_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_x_498_);
lean_ctor_set(v_reuseFailAlloc_530_, 1, v_x_499_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
v___y_513_ = v___x_529_;
goto v___jp_512_;
}
}
}
}
case 1:
{
lean_object* v_node_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_544_; 
v_node_532_ = lean_ctor_get(v_v_509_, 0);
v_isSharedCheck_544_ = !lean_is_exclusive(v_v_509_);
if (v_isSharedCheck_544_ == 0)
{
v___x_534_ = v_v_509_;
v_isShared_535_ = v_isSharedCheck_544_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_node_532_);
lean_dec(v_v_509_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_544_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
size_t v___x_536_; size_t v___x_537_; size_t v___x_538_; size_t v___x_539_; lean_object* v___x_540_; lean_object* v___x_542_; 
v___x_536_ = ((size_t)5ULL);
v___x_537_ = lean_usize_shift_right(v_x_496_, v___x_536_);
v___x_538_ = ((size_t)1ULL);
v___x_539_ = lean_usize_add(v_x_497_, v___x_538_);
v___x_540_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg(v_node_532_, v___x_537_, v___x_539_, v_x_498_, v_x_499_);
if (v_isShared_535_ == 0)
{
lean_ctor_set(v___x_534_, 0, v___x_540_);
v___x_542_ = v___x_534_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v___x_540_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
v___y_513_ = v___x_542_;
goto v___jp_512_;
}
}
}
default: 
{
lean_object* v___x_545_; 
v___x_545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_545_, 0, v_x_498_);
lean_ctor_set(v___x_545_, 1, v_x_499_);
v___y_513_ = v___x_545_;
goto v___jp_512_;
}
}
v___jp_512_:
{
lean_object* v___x_514_; lean_object* v___x_516_; 
v___x_514_ = lean_array_fset(v_xs_x27_511_, v_j_503_, v___y_513_);
lean_dec(v_j_503_);
if (v_isShared_508_ == 0)
{
lean_ctor_set(v___x_507_, 0, v___x_514_);
v___x_516_ = v___x_507_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v___x_514_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
}
}
}
else
{
lean_object* v_ks_548_; lean_object* v_vs_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_567_; 
v_ks_548_ = lean_ctor_get(v_x_495_, 0);
v_vs_549_ = lean_ctor_get(v_x_495_, 1);
v_isSharedCheck_567_ = !lean_is_exclusive(v_x_495_);
if (v_isSharedCheck_567_ == 0)
{
v___x_551_ = v_x_495_;
v_isShared_552_ = v_isSharedCheck_567_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_vs_549_);
lean_inc(v_ks_548_);
lean_dec(v_x_495_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_567_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_554_; 
if (v_isShared_552_ == 0)
{
v___x_554_ = v___x_551_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_ks_548_);
lean_ctor_set(v_reuseFailAlloc_566_, 1, v_vs_549_);
v___x_554_ = v_reuseFailAlloc_566_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
lean_object* v_newNode_555_; size_t v___x_556_; uint8_t v___x_557_; 
v_newNode_555_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1___redArg(v___x_554_, v_x_498_, v_x_499_);
v___x_556_ = ((size_t)7ULL);
v___x_557_ = lean_usize_dec_le(v___x_556_, v_x_497_);
if (v___x_557_ == 0)
{
lean_object* v___x_558_; lean_object* v___x_559_; uint8_t v___x_560_; 
v___x_558_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_555_);
v___x_559_ = lean_unsigned_to_nat(4u);
v___x_560_ = lean_nat_dec_lt(v___x_558_, v___x_559_);
lean_dec(v___x_558_);
if (v___x_560_ == 0)
{
lean_object* v_ks_561_; lean_object* v_vs_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; 
v_ks_561_ = lean_ctor_get(v_newNode_555_, 0);
lean_inc_ref(v_ks_561_);
v_vs_562_ = lean_ctor_get(v_newNode_555_, 1);
lean_inc_ref(v_vs_562_);
lean_dec_ref(v_newNode_555_);
v___x_563_ = lean_unsigned_to_nat(0u);
v___x_564_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg___closed__0);
v___x_565_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2___redArg(v_x_497_, v_ks_561_, v_vs_562_, v___x_563_, v___x_564_);
lean_dec_ref(v_vs_562_);
lean_dec_ref(v_ks_561_);
return v___x_565_;
}
else
{
return v_newNode_555_;
}
}
else
{
return v_newNode_555_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_495_ = stack[0].m_obj;
size_t v_x_496_ = stack[1].m_num;
size_t v_x_497_ = stack[2].m_num;
lean_object* v_x_498_ = stack[3].m_obj;
lean_object* v_x_499_ = stack[4].m_obj;
lean_object* v_res_568_;
v_res_568_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg(v_x_495_, v_x_496_, v_x_497_, v_x_498_, v_x_499_);
stack->m_obj
 = v_res_568_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2___redArg(size_t v_depth_569_, lean_object* v_keys_570_, lean_object* v_vals_571_, lean_object* v_i_572_, lean_object* v_entries_573_){
_start:
{
lean_object* v___x_574_; uint8_t v___x_575_; 
v___x_574_ = lean_array_get_size(v_keys_570_);
v___x_575_ = lean_nat_dec_lt(v_i_572_, v___x_574_);
if (v___x_575_ == 0)
{
lean_dec(v_i_572_);
return v_entries_573_;
}
else
{
lean_object* v_k_576_; lean_object* v_v_577_; size_t v___x_578_; size_t v___x_579_; size_t v___x_580_; uint64_t v___x_581_; size_t v_h_582_; size_t v___x_583_; lean_object* v___x_584_; size_t v___x_585_; size_t v___x_586_; size_t v___x_587_; size_t v_h_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v_k_576_ = lean_array_fget_borrowed(v_keys_570_, v_i_572_);
v_v_577_ = lean_array_fget_borrowed(v_vals_571_, v_i_572_);
v___x_578_ = lean_ptr_addr(v_k_576_);
v___x_579_ = ((size_t)3ULL);
v___x_580_ = lean_usize_shift_right(v___x_578_, v___x_579_);
v___x_581_ = lean_usize_to_uint64(v___x_580_);
v_h_582_ = lean_uint64_to_usize(v___x_581_);
v___x_583_ = ((size_t)5ULL);
v___x_584_ = lean_unsigned_to_nat(1u);
v___x_585_ = ((size_t)1ULL);
v___x_586_ = lean_usize_sub(v_depth_569_, v___x_585_);
v___x_587_ = lean_usize_mul(v___x_583_, v___x_586_);
v_h_588_ = lean_usize_shift_right(v_h_582_, v___x_587_);
v___x_589_ = lean_nat_add(v_i_572_, v___x_584_);
lean_dec(v_i_572_);
lean_inc(v_v_577_);
lean_inc(v_k_576_);
v___x_590_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg(v_entries_573_, v_h_588_, v_depth_569_, v_k_576_, v_v_577_);
v_i_572_ = v___x_589_;
v_entries_573_ = v___x_590_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_569_ = stack[0].m_num;
lean_object* v_keys_570_ = stack[1].m_obj;
lean_object* v_vals_571_ = stack[2].m_obj;
lean_object* v_i_572_ = stack[3].m_obj;
lean_object* v_entries_573_ = stack[4].m_obj;
lean_object* v_res_592_;
v_res_592_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2___redArg(v_depth_569_, v_keys_570_, v_vals_571_, v_i_572_, v_entries_573_);
stack->m_obj
 = v_res_592_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_593_, lean_object* v_keys_594_, lean_object* v_vals_595_, lean_object* v_i_596_, lean_object* v_entries_597_){
_start:
{
size_t v_depth_boxed_598_; lean_object* v_res_599_; 
v_depth_boxed_598_ = lean_unbox_usize(v_depth_593_);
lean_dec(v_depth_593_);
v_res_599_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2___redArg(v_depth_boxed_598_, v_keys_594_, v_vals_595_, v_i_596_, v_entries_597_);
lean_dec_ref(v_vals_595_);
lean_dec_ref(v_keys_594_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg___boxed(lean_object* v_x_600_, lean_object* v_x_601_, lean_object* v_x_602_, lean_object* v_x_603_, lean_object* v_x_604_){
_start:
{
size_t v_x_6501__boxed_605_; size_t v_x_6502__boxed_606_; lean_object* v_res_607_; 
v_x_6501__boxed_605_ = lean_unbox_usize(v_x_601_);
lean_dec(v_x_601_);
v_x_6502__boxed_606_ = lean_unbox_usize(v_x_602_);
lean_dec(v_x_602_);
v_res_607_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg(v_x_600_, v_x_6501__boxed_605_, v_x_6502__boxed_606_, v_x_603_, v_x_604_);
return v_res_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0___redArg(lean_object* v_x_608_, lean_object* v_x_609_, lean_object* v_x_610_){
_start:
{
size_t v___x_611_; size_t v___x_612_; size_t v___x_613_; uint64_t v___x_614_; size_t v___x_615_; size_t v___x_616_; lean_object* v___x_617_; 
v___x_611_ = lean_ptr_addr(v_x_609_);
v___x_612_ = ((size_t)3ULL);
v___x_613_ = lean_usize_shift_right(v___x_611_, v___x_612_);
v___x_614_ = lean_usize_to_uint64(v___x_613_);
v___x_615_ = lean_uint64_to_usize(v___x_614_);
v___x_616_ = ((size_t)1ULL);
v___x_617_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg(v_x_608_, v___x_615_, v___x_616_, v_x_609_, v_x_610_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___lam__0(lean_object* v_e_618_, lean_object* v_a_619_, lean_object* v_s_620_){
_start:
{
lean_object* v_structs_621_; lean_object* v_typeIdOf_622_; lean_object* v_exprToStructId_623_; lean_object* v_exprToStructIdEntries_624_; lean_object* v_forbiddenNatModules_625_; lean_object* v_natStructs_626_; lean_object* v_natTypeIdOf_627_; lean_object* v_exprToNatStructId_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_638_; 
v_structs_621_ = lean_ctor_get(v_s_620_, 0);
v_typeIdOf_622_ = lean_ctor_get(v_s_620_, 1);
v_exprToStructId_623_ = lean_ctor_get(v_s_620_, 2);
v_exprToStructIdEntries_624_ = lean_ctor_get(v_s_620_, 3);
v_forbiddenNatModules_625_ = lean_ctor_get(v_s_620_, 4);
v_natStructs_626_ = lean_ctor_get(v_s_620_, 5);
v_natTypeIdOf_627_ = lean_ctor_get(v_s_620_, 6);
v_exprToNatStructId_628_ = lean_ctor_get(v_s_620_, 7);
v_isSharedCheck_638_ = !lean_is_exclusive(v_s_620_);
if (v_isSharedCheck_638_ == 0)
{
v___x_630_ = v_s_620_;
v_isShared_631_ = v_isSharedCheck_638_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_exprToNatStructId_628_);
lean_inc(v_natTypeIdOf_627_);
lean_inc(v_natStructs_626_);
lean_inc(v_forbiddenNatModules_625_);
lean_inc(v_exprToStructIdEntries_624_);
lean_inc(v_exprToStructId_623_);
lean_inc(v_typeIdOf_622_);
lean_inc(v_structs_621_);
lean_dec(v_s_620_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_638_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_636_; 
lean_inc_n(v_a_619_, 2);
lean_inc_ref(v_e_618_);
v___x_632_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0___redArg(v_exprToStructId_623_, v_e_618_, v_a_619_);
v___x_633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_633_, 0, v_e_618_);
lean_ctor_set(v___x_633_, 1, v_a_619_);
v___x_634_ = l_Lean_PersistentArray_push___redArg(v_exprToStructIdEntries_624_, v___x_633_);
if (v_isShared_631_ == 0)
{
lean_ctor_set(v___x_630_, 3, v___x_634_);
lean_ctor_set(v___x_630_, 2, v___x_632_);
v___x_636_ = v___x_630_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_structs_621_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v_typeIdOf_622_);
lean_ctor_set(v_reuseFailAlloc_637_, 2, v___x_632_);
lean_ctor_set(v_reuseFailAlloc_637_, 3, v___x_634_);
lean_ctor_set(v_reuseFailAlloc_637_, 4, v_forbiddenNatModules_625_);
lean_ctor_set(v_reuseFailAlloc_637_, 5, v_natStructs_626_);
lean_ctor_set(v_reuseFailAlloc_637_, 6, v_natTypeIdOf_627_);
lean_ctor_set(v_reuseFailAlloc_637_, 7, v_exprToNatStructId_628_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___lam__0___boxed(lean_object* v_e_639_, lean_object* v_a_640_, lean_object* v_s_641_){
_start:
{
lean_object* v_res_642_; 
v_res_642_ = l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___lam__0(v_e_639_, v_a_640_, v_s_641_);
lean_dec(v_a_640_);
return v_res_642_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___closed__1(void){
_start:
{
lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_644_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___closed__0));
v___x_645_ = l_Lean_stringToMessageData(v___x_644_);
return v___x_645_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg(lean_object* v_e_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_){
_start:
{
lean_object* v___f_659_; lean_object* v___x_660_; 
lean_inc(v_a_647_);
lean_inc_ref(v_e_646_);
v___f_659_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_659_, 0, v_e_646_);
lean_closure_set(v___f_659_, 1, v_a_647_);
v___x_660_ = l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg(v_e_646_, v_a_648_, v_a_653_);
if (lean_obj_tag(v___x_660_) == 0)
{
lean_object* v_a_661_; 
v_a_661_ = lean_ctor_get(v___x_660_, 0);
lean_inc(v_a_661_);
lean_dec_ref_known(v___x_660_, 1);
if (lean_obj_tag(v_a_661_) == 1)
{
lean_object* v_val_662_; uint8_t v___x_663_; 
lean_dec_ref(v___f_659_);
v_val_662_ = lean_ctor_get(v_a_661_, 0);
lean_inc(v_val_662_);
lean_dec_ref_known(v_a_661_, 1);
v___x_663_ = lean_nat_dec_eq(v_val_662_, v_a_647_);
lean_dec(v_val_662_);
if (v___x_663_ == 0)
{
lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_664_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___closed__1);
v___x_665_ = l_Lean_indentExpr(v_e_646_);
v___x_666_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_666_, 0, v___x_664_);
lean_ctor_set(v___x_666_, 1, v___x_665_);
v___x_667_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_649_);
if (lean_obj_tag(v___x_667_) == 0)
{
lean_object* v_a_668_; uint8_t v_verbose_669_; 
v_a_668_ = lean_ctor_get(v___x_667_, 0);
lean_inc(v_a_668_);
lean_dec_ref_known(v___x_667_, 1);
v_verbose_669_ = lean_ctor_get_uint8(v_a_668_, 0);
lean_dec(v_a_668_);
if (v_verbose_669_ == 0)
{
lean_dec_ref_known(v___x_666_, 2);
goto v___jp_656_;
}
else
{
lean_object* v___x_670_; 
v___x_670_ = l_Lean_Meta_Sym_reportIssue(v___x_666_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_);
if (lean_obj_tag(v___x_670_) == 0)
{
lean_dec_ref_known(v___x_670_, 1);
goto v___jp_656_;
}
else
{
return v___x_670_;
}
}
}
else
{
lean_object* v_a_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_678_; 
lean_dec_ref_known(v___x_666_, 2);
v_a_671_ = lean_ctor_get(v___x_667_, 0);
v_isSharedCheck_678_ = !lean_is_exclusive(v___x_667_);
if (v_isSharedCheck_678_ == 0)
{
v___x_673_ = v___x_667_;
v_isShared_674_ = v_isSharedCheck_678_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_a_671_);
lean_dec(v___x_667_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_678_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v___x_676_; 
if (v_isShared_674_ == 0)
{
v___x_676_ = v___x_673_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v_a_671_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
return v___x_676_;
}
}
}
}
else
{
lean_dec_ref(v_e_646_);
goto v___jp_656_;
}
}
else
{
lean_object* v___x_679_; lean_object* v___x_680_; 
lean_dec(v_a_661_);
lean_dec_ref(v_e_646_);
v___x_679_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_680_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_679_, v___f_659_, v_a_648_);
return v___x_680_;
}
}
else
{
lean_object* v_a_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_688_; 
lean_dec_ref(v___f_659_);
lean_dec_ref(v_e_646_);
v_a_681_ = lean_ctor_get(v___x_660_, 0);
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_660_);
if (v_isSharedCheck_688_ == 0)
{
v___x_683_ = v___x_660_;
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_a_681_);
lean_dec(v___x_660_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v___x_686_; 
if (v_isShared_684_ == 0)
{
v___x_686_ = v___x_683_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_a_681_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
}
v___jp_656_:
{
lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_657_ = lean_box(0);
v___x_658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_658_, 0, v___x_657_);
return v___x_658_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_646_ = stack[0].m_obj;
lean_object* v_a_647_ = stack[1].m_obj;
lean_object* v_a_648_ = stack[2].m_obj;
lean_object* v_a_649_ = stack[3].m_obj;
lean_object* v_a_650_ = stack[4].m_obj;
lean_object* v_a_651_ = stack[5].m_obj;
lean_object* v_a_652_ = stack[6].m_obj;
lean_object* v_a_653_ = stack[7].m_obj;
lean_object* v_a_654_ = stack[8].m_obj;
lean_object* v_res_689_;
v_res_689_ = l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg(v_e_646_, v_a_647_, v_a_648_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_);
stack->m_obj
 = v_res_689_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___boxed(lean_object* v_e_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg(v_e_690_, v_a_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_);
lean_dec(v_a_698_);
lean_dec_ref(v_a_697_);
lean_dec(v_a_696_);
lean_dec_ref(v_a_695_);
lean_dec(v_a_694_);
lean_dec_ref(v_a_693_);
lean_dec(v_a_692_);
lean_dec(v_a_691_);
return v_res_700_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId(lean_object* v_e_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_){
_start:
{
lean_object* v___x_714_; 
v___x_714_ = l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg(v_e_701_, v_a_702_, v_a_703_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_);
return v___x_714_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_setTermStructId_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_701_ = stack[0].m_obj;
lean_object* v_a_702_ = stack[1].m_obj;
lean_object* v_a_703_ = stack[2].m_obj;
lean_object* v_a_704_ = stack[3].m_obj;
lean_object* v_a_705_ = stack[4].m_obj;
lean_object* v_a_706_ = stack[5].m_obj;
lean_object* v_a_707_ = stack[6].m_obj;
lean_object* v_a_708_ = stack[7].m_obj;
lean_object* v_a_709_ = stack[8].m_obj;
lean_object* v_a_710_ = stack[9].m_obj;
lean_object* v_a_711_ = stack[10].m_obj;
lean_object* v_a_712_ = stack[11].m_obj;
lean_object* v_res_715_;
v_res_715_ = l_Lean_Meta_Grind_Arith_Linear_setTermStructId(v_e_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_);
stack->m_obj
 = v_res_715_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId___boxed(lean_object* v_e_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l_Lean_Meta_Grind_Arith_Linear_setTermStructId(v_e_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_, v_a_726_, v_a_727_);
lean_dec(v_a_727_);
lean_dec_ref(v_a_726_);
lean_dec(v_a_725_);
lean_dec_ref(v_a_724_);
lean_dec(v_a_723_);
lean_dec_ref(v_a_722_);
lean_dec(v_a_721_);
lean_dec_ref(v_a_720_);
lean_dec(v_a_719_);
lean_dec(v_a_718_);
lean_dec(v_a_717_);
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0(lean_object* v_00_u03b2_730_, lean_object* v_x_731_, lean_object* v_x_732_, lean_object* v_x_733_){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0___redArg(v_x_731_, v_x_732_, v_x_733_);
return v___x_734_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0(lean_object* v_00_u03b2_735_, lean_object* v_x_736_, size_t v_x_737_, size_t v_x_738_, lean_object* v_x_739_, lean_object* v_x_740_){
_start:
{
lean_object* v___x_741_; 
v___x_741_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg(v_x_736_, v_x_737_, v_x_738_, v_x_739_, v_x_740_);
return v___x_741_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_736_ = stack[1].m_obj;
size_t v_x_737_ = stack[2].m_num;
size_t v_x_738_ = stack[3].m_num;
lean_object* v_x_739_ = stack[4].m_obj;
lean_object* v_x_740_ = stack[5].m_obj;
lean_object* v_res_742_;
v_res_742_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0(lean_box(0), v_x_736_, v_x_737_, v_x_738_, v_x_739_, v_x_740_);
stack->m_obj
 = v_res_742_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___boxed(lean_object* v_00_u03b2_743_, lean_object* v_x_744_, lean_object* v_x_745_, lean_object* v_x_746_, lean_object* v_x_747_, lean_object* v_x_748_){
_start:
{
size_t v_x_6944__boxed_749_; size_t v_x_6945__boxed_750_; lean_object* v_res_751_; 
v_x_6944__boxed_749_ = lean_unbox_usize(v_x_745_);
lean_dec(v_x_745_);
v_x_6945__boxed_750_ = lean_unbox_usize(v_x_746_);
lean_dec(v_x_746_);
v_res_751_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0(v_00_u03b2_743_, v_x_744_, v_x_6944__boxed_749_, v_x_6945__boxed_750_, v_x_747_, v_x_748_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_752_, lean_object* v_n_753_, lean_object* v_k_754_, lean_object* v_v_755_){
_start:
{
lean_object* v___x_756_; 
v___x_756_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1___redArg(v_n_753_, v_k_754_, v_v_755_);
return v___x_756_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_757_, size_t v_depth_758_, lean_object* v_keys_759_, lean_object* v_vals_760_, lean_object* v_heq_761_, lean_object* v_i_762_, lean_object* v_entries_763_){
_start:
{
lean_object* v___x_764_; 
v___x_764_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2___redArg(v_depth_758_, v_keys_759_, v_vals_760_, v_i_762_, v_entries_763_);
return v___x_764_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_depth_758_ = stack[1].m_num;
lean_object* v_keys_759_ = stack[2].m_obj;
lean_object* v_vals_760_ = stack[3].m_obj;
lean_object* v_i_762_ = stack[5].m_obj;
lean_object* v_entries_763_ = stack[6].m_obj;
lean_object* v_res_765_;
v_res_765_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2(lean_box(0), v_depth_758_, v_keys_759_, v_vals_760_, lean_box(0), v_i_762_, v_entries_763_);
stack->m_obj
 = v_res_765_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_766_, lean_object* v_depth_767_, lean_object* v_keys_768_, lean_object* v_vals_769_, lean_object* v_heq_770_, lean_object* v_i_771_, lean_object* v_entries_772_){
_start:
{
size_t v_depth_boxed_773_; lean_object* v_res_774_; 
v_depth_boxed_773_ = lean_unbox_usize(v_depth_767_);
lean_dec(v_depth_767_);
v_res_774_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2(v_00_u03b2_766_, v_depth_boxed_773_, v_keys_768_, v_vals_769_, v_heq_770_, v_i_771_, v_entries_772_);
lean_dec_ref(v_vals_769_);
lean_dec_ref(v_keys_768_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_775_, lean_object* v_x_776_, lean_object* v_x_777_, lean_object* v_x_778_, lean_object* v_x_779_){
_start:
{
lean_object* v___x_780_; 
v___x_780_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1_spec__2___redArg(v_x_776_, v_x_777_, v_x_778_, v_x_779_);
return v___x_780_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0_spec__0(lean_object* v_msgData_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_){
_start:
{
lean_object* v___x_787_; lean_object* v_env_788_; uint8_t v___x_789_; lean_object* v_env_790_; lean_object* v___x_791_; lean_object* v_toCold_792_; lean_object* v_mctx_793_; lean_object* v_lctx_794_; lean_object* v_options_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_787_ = lean_st_ref_get(v___y_785_);
v_env_788_ = lean_ctor_get(v___x_787_, 0);
lean_inc_ref(v_env_788_);
lean_dec(v___x_787_);
v___x_789_ = 0;
v_env_790_ = l_Lean_Environment_setRecordingDeps(v_env_788_, v___x_789_);
v___x_791_ = lean_st_ref_get(v___y_783_);
v_toCold_792_ = lean_ctor_get(v___y_784_, 0);
v_mctx_793_ = lean_ctor_get(v___x_791_, 0);
lean_inc_ref(v_mctx_793_);
lean_dec(v___x_791_);
v_lctx_794_ = lean_ctor_get(v___y_782_, 2);
v_options_795_ = lean_ctor_get(v_toCold_792_, 2);
lean_inc_ref(v_options_795_);
lean_inc_ref(v_lctx_794_);
v___x_796_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_796_, 0, v_env_790_);
lean_ctor_set(v___x_796_, 1, v_mctx_793_);
lean_ctor_set(v___x_796_, 2, v_lctx_794_);
lean_ctor_set(v___x_796_, 3, v_options_795_);
v___x_797_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_797_, 0, v___x_796_);
lean_ctor_set(v___x_797_, 1, v_msgData_781_);
v___x_798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_798_, 0, v___x_797_);
return v___x_798_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_781_ = stack[0].m_obj;
lean_object* v___y_782_ = stack[1].m_obj;
lean_object* v___y_783_ = stack[2].m_obj;
lean_object* v___y_784_ = stack[3].m_obj;
lean_object* v___y_785_ = stack[4].m_obj;
lean_object* v_res_799_;
v_res_799_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0_spec__0(v_msgData_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_);
stack->m_obj
 = v_res_799_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0_spec__0___boxed(lean_object* v_msgData_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0_spec__0(v_msgData_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_);
lean_dec(v___y_804_);
lean_dec_ref(v___y_803_);
lean_dec(v___y_802_);
lean_dec_ref(v___y_801_);
return v_res_806_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(lean_object* v_msg_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_){
_start:
{
lean_object* v_ref_813_; lean_object* v___x_814_; lean_object* v_a_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_823_; 
v_ref_813_ = lean_ctor_get(v___y_810_, 2);
v___x_814_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0_spec__0(v_msg_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_);
v_a_815_ = lean_ctor_get(v___x_814_, 0);
v_isSharedCheck_823_ = !lean_is_exclusive(v___x_814_);
if (v_isSharedCheck_823_ == 0)
{
v___x_817_ = v___x_814_;
v_isShared_818_ = v_isSharedCheck_823_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_a_815_);
lean_dec(v___x_814_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_823_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v___x_819_; lean_object* v___x_821_; 
lean_inc(v_ref_813_);
v___x_819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_819_, 0, v_ref_813_);
lean_ctor_set(v___x_819_, 1, v_a_815_);
if (v_isShared_818_ == 0)
{
lean_ctor_set_tag(v___x_817_, 1);
lean_ctor_set(v___x_817_, 0, v___x_819_);
v___x_821_ = v___x_817_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v___x_819_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_807_ = stack[0].m_obj;
lean_object* v___y_808_ = stack[1].m_obj;
lean_object* v___y_809_ = stack[2].m_obj;
lean_object* v___y_810_ = stack[3].m_obj;
lean_object* v___y_811_ = stack[4].m_obj;
lean_object* v_res_824_;
v_res_824_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v_msg_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_);
stack->m_obj
 = v_res_824_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg___boxed(lean_object* v_msg_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v_msg_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_);
lean_dec(v___y_829_);
lean_dec_ref(v___y_828_);
lean_dec(v___y_827_);
lean_dec_ref(v___y_826_);
return v_res_831_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___closed__1(void){
_start:
{
lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_833_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___closed__0));
v___x_834_ = l_Lean_stringToMessageData(v___x_833_);
return v___x_834_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst(lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_){
_start:
{
lean_object* v___x_847_; 
v___x_847_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_);
if (lean_obj_tag(v___x_847_) == 0)
{
lean_object* v_a_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_859_; 
v_a_848_ = lean_ctor_get(v___x_847_, 0);
v_isSharedCheck_859_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_859_ == 0)
{
v___x_850_ = v___x_847_;
v_isShared_851_ = v_isSharedCheck_859_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_a_848_);
lean_dec(v___x_847_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_859_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v_noNatDivInst_x3f_852_; 
v_noNatDivInst_x3f_852_ = lean_ctor_get(v_a_848_, 11);
lean_inc(v_noNatDivInst_x3f_852_);
lean_dec(v_a_848_);
if (lean_obj_tag(v_noNatDivInst_x3f_852_) == 1)
{
lean_object* v_val_853_; lean_object* v___x_855_; 
v_val_853_ = lean_ctor_get(v_noNatDivInst_x3f_852_, 0);
lean_inc(v_val_853_);
lean_dec_ref_known(v_noNatDivInst_x3f_852_, 1);
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 0, v_val_853_);
v___x_855_ = v___x_850_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_val_853_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
else
{
lean_object* v___x_857_; lean_object* v___x_858_; 
lean_dec(v_noNatDivInst_x3f_852_);
lean_del_object(v___x_850_);
v___x_857_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___closed__1);
v___x_858_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_857_, v_a_842_, v_a_843_, v_a_844_, v_a_845_);
return v___x_858_;
}
}
}
else
{
lean_object* v_a_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_867_; 
v_a_860_ = lean_ctor_get(v___x_847_, 0);
v_isSharedCheck_867_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_867_ == 0)
{
v___x_862_ = v___x_847_;
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_a_860_);
lean_dec(v___x_847_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___x_865_; 
if (v_isShared_863_ == 0)
{
v___x_865_ = v___x_862_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v_a_860_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_835_ = stack[0].m_obj;
lean_object* v_a_836_ = stack[1].m_obj;
lean_object* v_a_837_ = stack[2].m_obj;
lean_object* v_a_838_ = stack[3].m_obj;
lean_object* v_a_839_ = stack[4].m_obj;
lean_object* v_a_840_ = stack[5].m_obj;
lean_object* v_a_841_ = stack[6].m_obj;
lean_object* v_a_842_ = stack[7].m_obj;
lean_object* v_a_843_ = stack[8].m_obj;
lean_object* v_a_844_ = stack[9].m_obj;
lean_object* v_a_845_ = stack[10].m_obj;
lean_object* v_res_868_;
v_res_868_ = l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst(v_a_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_);
stack->m_obj
 = v_res_868_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___boxed(lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst(v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_);
lean_dec(v_a_879_);
lean_dec_ref(v_a_878_);
lean_dec(v_a_877_);
lean_dec_ref(v_a_876_);
lean_dec(v_a_875_);
lean_dec_ref(v_a_874_);
lean_dec(v_a_873_);
lean_dec_ref(v_a_872_);
lean_dec(v_a_871_);
lean_dec(v_a_870_);
lean_dec(v_a_869_);
return v_res_881_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0(lean_object* v_00_u03b1_882_, lean_object* v_msg_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_){
_start:
{
lean_object* v___x_896_; 
v___x_896_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v_msg_883_, v___y_891_, v___y_892_, v___y_893_, v___y_894_);
return v___x_896_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_883_ = stack[1].m_obj;
lean_object* v___y_884_ = stack[2].m_obj;
lean_object* v___y_885_ = stack[3].m_obj;
lean_object* v___y_886_ = stack[4].m_obj;
lean_object* v___y_887_ = stack[5].m_obj;
lean_object* v___y_888_ = stack[6].m_obj;
lean_object* v___y_889_ = stack[7].m_obj;
lean_object* v___y_890_ = stack[8].m_obj;
lean_object* v___y_891_ = stack[9].m_obj;
lean_object* v___y_892_ = stack[10].m_obj;
lean_object* v___y_893_ = stack[11].m_obj;
lean_object* v___y_894_ = stack[12].m_obj;
lean_object* v_res_897_;
v_res_897_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0(lean_box(0), v_msg_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_);
stack->m_obj
 = v_res_897_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___boxed(lean_object* v_00_u03b1_898_, lean_object* v_msg_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0(v_00_u03b1_898_, v_msg_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_);
lean_dec(v___y_910_);
lean_dec_ref(v___y_909_);
lean_dec(v___y_908_);
lean_dec_ref(v___y_907_);
lean_dec(v___y_906_);
lean_dec_ref(v___y_905_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
lean_dec(v___y_902_);
lean_dec(v___y_901_);
lean_dec(v___y_900_);
return v_res_912_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLEInst___closed__1(void){
_start:
{
lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_914_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLEInst___closed__0));
v___x_915_ = l_Lean_stringToMessageData(v___x_914_);
return v___x_915_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_getLEInst(lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_){
_start:
{
lean_object* v___x_928_; 
v___x_928_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_916_, v_a_917_, v_a_918_, v_a_919_, v_a_920_, v_a_921_, v_a_922_, v_a_923_, v_a_924_, v_a_925_, v_a_926_);
if (lean_obj_tag(v___x_928_) == 0)
{
lean_object* v_a_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_940_; 
v_a_929_ = lean_ctor_get(v___x_928_, 0);
v_isSharedCheck_940_ = !lean_is_exclusive(v___x_928_);
if (v_isSharedCheck_940_ == 0)
{
v___x_931_ = v___x_928_;
v_isShared_932_ = v_isSharedCheck_940_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_a_929_);
lean_dec(v___x_928_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_940_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v_leInst_x3f_933_; 
v_leInst_x3f_933_ = lean_ctor_get(v_a_929_, 5);
lean_inc(v_leInst_x3f_933_);
lean_dec(v_a_929_);
if (lean_obj_tag(v_leInst_x3f_933_) == 1)
{
lean_object* v_val_934_; lean_object* v___x_936_; 
v_val_934_ = lean_ctor_get(v_leInst_x3f_933_, 0);
lean_inc(v_val_934_);
lean_dec_ref_known(v_leInst_x3f_933_, 1);
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 0, v_val_934_);
v___x_936_ = v___x_931_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v_val_934_);
v___x_936_ = v_reuseFailAlloc_937_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
return v___x_936_;
}
}
else
{
lean_object* v___x_938_; lean_object* v___x_939_; 
lean_dec(v_leInst_x3f_933_);
lean_del_object(v___x_931_);
v___x_938_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLEInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLEInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLEInst___closed__1);
v___x_939_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_938_, v_a_923_, v_a_924_, v_a_925_, v_a_926_);
return v___x_939_;
}
}
}
else
{
lean_object* v_a_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_948_; 
v_a_941_ = lean_ctor_get(v___x_928_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_928_);
if (v_isSharedCheck_948_ == 0)
{
v___x_943_ = v___x_928_;
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_a_941_);
lean_dec(v___x_928_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_946_; 
if (v_isShared_944_ == 0)
{
v___x_946_ = v___x_943_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_a_941_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_getLEInst_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_916_ = stack[0].m_obj;
lean_object* v_a_917_ = stack[1].m_obj;
lean_object* v_a_918_ = stack[2].m_obj;
lean_object* v_a_919_ = stack[3].m_obj;
lean_object* v_a_920_ = stack[4].m_obj;
lean_object* v_a_921_ = stack[5].m_obj;
lean_object* v_a_922_ = stack[6].m_obj;
lean_object* v_a_923_ = stack[7].m_obj;
lean_object* v_a_924_ = stack[8].m_obj;
lean_object* v_a_925_ = stack[9].m_obj;
lean_object* v_a_926_ = stack[10].m_obj;
lean_object* v_res_949_;
v_res_949_ = l_Lean_Meta_Grind_Arith_Linear_getLEInst(v_a_916_, v_a_917_, v_a_918_, v_a_919_, v_a_920_, v_a_921_, v_a_922_, v_a_923_, v_a_924_, v_a_925_, v_a_926_);
stack->m_obj
 = v_res_949_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLEInst___boxed(lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l_Lean_Meta_Grind_Arith_Linear_getLEInst(v_a_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_);
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
lean_dec(v_a_950_);
return v_res_962_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLTInst___closed__1(void){
_start:
{
lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_964_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLTInst___closed__0));
v___x_965_ = l_Lean_stringToMessageData(v___x_964_);
return v___x_965_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_getLTInst(lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_){
_start:
{
lean_object* v___x_978_; 
v___x_978_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, v_a_976_);
if (lean_obj_tag(v___x_978_) == 0)
{
lean_object* v_a_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_990_; 
v_a_979_ = lean_ctor_get(v___x_978_, 0);
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_978_);
if (v_isSharedCheck_990_ == 0)
{
v___x_981_ = v___x_978_;
v_isShared_982_ = v_isSharedCheck_990_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_a_979_);
lean_dec(v___x_978_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_990_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v_ltInst_x3f_983_; 
v_ltInst_x3f_983_ = lean_ctor_get(v_a_979_, 6);
lean_inc(v_ltInst_x3f_983_);
lean_dec(v_a_979_);
if (lean_obj_tag(v_ltInst_x3f_983_) == 1)
{
lean_object* v_val_984_; lean_object* v___x_986_; 
v_val_984_ = lean_ctor_get(v_ltInst_x3f_983_, 0);
lean_inc(v_val_984_);
lean_dec_ref_known(v_ltInst_x3f_983_, 1);
if (v_isShared_982_ == 0)
{
lean_ctor_set(v___x_981_, 0, v_val_984_);
v___x_986_ = v___x_981_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_val_984_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
return v___x_986_;
}
}
else
{
lean_object* v___x_988_; lean_object* v___x_989_; 
lean_dec(v_ltInst_x3f_983_);
lean_del_object(v___x_981_);
v___x_988_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLTInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLTInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLTInst___closed__1);
v___x_989_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_988_, v_a_973_, v_a_974_, v_a_975_, v_a_976_);
return v___x_989_;
}
}
}
else
{
lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_998_; 
v_a_991_ = lean_ctor_get(v___x_978_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_978_);
if (v_isSharedCheck_998_ == 0)
{
v___x_993_ = v___x_978_;
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_dec(v___x_978_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_996_; 
if (v_isShared_994_ == 0)
{
v___x_996_ = v___x_993_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_a_991_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_getLTInst_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_966_ = stack[0].m_obj;
lean_object* v_a_967_ = stack[1].m_obj;
lean_object* v_a_968_ = stack[2].m_obj;
lean_object* v_a_969_ = stack[3].m_obj;
lean_object* v_a_970_ = stack[4].m_obj;
lean_object* v_a_971_ = stack[5].m_obj;
lean_object* v_a_972_ = stack[6].m_obj;
lean_object* v_a_973_ = stack[7].m_obj;
lean_object* v_a_974_ = stack[8].m_obj;
lean_object* v_a_975_ = stack[9].m_obj;
lean_object* v_a_976_ = stack[10].m_obj;
lean_object* v_res_999_;
v_res_999_ = l_Lean_Meta_Grind_Arith_Linear_getLTInst(v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, v_a_976_);
stack->m_obj
 = v_res_999_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLTInst___boxed(lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l_Lean_Meta_Grind_Arith_Linear_getLTInst(v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_);
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
lean_dec(v_a_1000_);
return v_res_1012_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___closed__1(void){
_start:
{
lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1014_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___closed__0));
v___x_1015_ = l_Lean_stringToMessageData(v___x_1014_);
return v___x_1015_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst(lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_){
_start:
{
lean_object* v___x_1028_; 
v___x_1028_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_);
if (lean_obj_tag(v___x_1028_) == 0)
{
lean_object* v_a_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1040_; 
v_a_1029_ = lean_ctor_get(v___x_1028_, 0);
v_isSharedCheck_1040_ = !lean_is_exclusive(v___x_1028_);
if (v_isSharedCheck_1040_ == 0)
{
v___x_1031_ = v___x_1028_;
v_isShared_1032_ = v_isSharedCheck_1040_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_a_1029_);
lean_dec(v___x_1028_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1040_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v_lawfulOrderLTInst_x3f_1033_; 
v_lawfulOrderLTInst_x3f_1033_ = lean_ctor_get(v_a_1029_, 7);
lean_inc(v_lawfulOrderLTInst_x3f_1033_);
lean_dec(v_a_1029_);
if (lean_obj_tag(v_lawfulOrderLTInst_x3f_1033_) == 1)
{
lean_object* v_val_1034_; lean_object* v___x_1036_; 
v_val_1034_ = lean_ctor_get(v_lawfulOrderLTInst_x3f_1033_, 0);
lean_inc(v_val_1034_);
lean_dec_ref_known(v_lawfulOrderLTInst_x3f_1033_, 1);
if (v_isShared_1032_ == 0)
{
lean_ctor_set(v___x_1031_, 0, v_val_1034_);
v___x_1036_ = v___x_1031_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_val_1034_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
else
{
lean_object* v___x_1038_; lean_object* v___x_1039_; 
lean_dec(v_lawfulOrderLTInst_x3f_1033_);
lean_del_object(v___x_1031_);
v___x_1038_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___closed__1);
v___x_1039_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_1038_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_);
return v___x_1039_;
}
}
}
else
{
lean_object* v_a_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1048_; 
v_a_1041_ = lean_ctor_get(v___x_1028_, 0);
v_isSharedCheck_1048_ = !lean_is_exclusive(v___x_1028_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1043_ = v___x_1028_;
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_a_1041_);
lean_dec(v___x_1028_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___x_1046_; 
if (v_isShared_1044_ == 0)
{
v___x_1046_ = v___x_1043_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v_a_1041_);
v___x_1046_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
return v___x_1046_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1016_ = stack[0].m_obj;
lean_object* v_a_1017_ = stack[1].m_obj;
lean_object* v_a_1018_ = stack[2].m_obj;
lean_object* v_a_1019_ = stack[3].m_obj;
lean_object* v_a_1020_ = stack[4].m_obj;
lean_object* v_a_1021_ = stack[5].m_obj;
lean_object* v_a_1022_ = stack[6].m_obj;
lean_object* v_a_1023_ = stack[7].m_obj;
lean_object* v_a_1024_ = stack[8].m_obj;
lean_object* v_a_1025_ = stack[9].m_obj;
lean_object* v_a_1026_ = stack[10].m_obj;
lean_object* v_res_1049_;
v_res_1049_ = l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst(v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_);
stack->m_obj
 = v_res_1049_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___boxed(lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_){
_start:
{
lean_object* v_res_1062_; 
v_res_1062_ = l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst(v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_, v_a_1058_, v_a_1059_, v_a_1060_);
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
lean_dec(v_a_1050_);
return v_res_1062_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___closed__1(void){
_start:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1064_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___closed__0));
v___x_1065_ = l_Lean_stringToMessageData(v___x_1064_);
return v___x_1065_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst(lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_){
_start:
{
lean_object* v___x_1078_; 
v___x_1078_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_);
if (lean_obj_tag(v___x_1078_) == 0)
{
lean_object* v_a_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1090_; 
v_a_1079_ = lean_ctor_get(v___x_1078_, 0);
v_isSharedCheck_1090_ = !lean_is_exclusive(v___x_1078_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1081_ = v___x_1078_;
v_isShared_1082_ = v_isSharedCheck_1090_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_a_1079_);
lean_dec(v___x_1078_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1090_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v_isPreorderInst_x3f_1083_; 
v_isPreorderInst_x3f_1083_ = lean_ctor_get(v_a_1079_, 8);
lean_inc(v_isPreorderInst_x3f_1083_);
lean_dec(v_a_1079_);
if (lean_obj_tag(v_isPreorderInst_x3f_1083_) == 1)
{
lean_object* v_val_1084_; lean_object* v___x_1086_; 
v_val_1084_ = lean_ctor_get(v_isPreorderInst_x3f_1083_, 0);
lean_inc(v_val_1084_);
lean_dec_ref_known(v_isPreorderInst_x3f_1083_, 1);
if (v_isShared_1082_ == 0)
{
lean_ctor_set(v___x_1081_, 0, v_val_1084_);
v___x_1086_ = v___x_1081_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_val_1084_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
}
}
else
{
lean_object* v___x_1088_; lean_object* v___x_1089_; 
lean_dec(v_isPreorderInst_x3f_1083_);
lean_del_object(v___x_1081_);
v___x_1088_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___closed__1);
v___x_1089_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_1088_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_);
return v___x_1089_;
}
}
}
else
{
lean_object* v_a_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1098_; 
v_a_1091_ = lean_ctor_get(v___x_1078_, 0);
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_1078_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1093_ = v___x_1078_;
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_a_1091_);
lean_dec(v___x_1078_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1096_; 
if (v_isShared_1094_ == 0)
{
v___x_1096_ = v___x_1093_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_a_1091_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
return v___x_1096_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1066_ = stack[0].m_obj;
lean_object* v_a_1067_ = stack[1].m_obj;
lean_object* v_a_1068_ = stack[2].m_obj;
lean_object* v_a_1069_ = stack[3].m_obj;
lean_object* v_a_1070_ = stack[4].m_obj;
lean_object* v_a_1071_ = stack[5].m_obj;
lean_object* v_a_1072_ = stack[6].m_obj;
lean_object* v_a_1073_ = stack[7].m_obj;
lean_object* v_a_1074_ = stack[8].m_obj;
lean_object* v_a_1075_ = stack[9].m_obj;
lean_object* v_a_1076_ = stack[10].m_obj;
lean_object* v_res_1099_;
v_res_1099_ = l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst(v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_);
stack->m_obj
 = v_res_1099_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___boxed(lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_){
_start:
{
lean_object* v_res_1112_; 
v_res_1112_ = l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst(v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_);
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
lean_dec(v_a_1100_);
return v_res_1112_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1(void){
_start:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1114_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__0));
v___x_1115_ = l_Lean_stringToMessageData(v___x_1114_);
return v___x_1115_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst(lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_){
_start:
{
lean_object* v___x_1128_; 
v___x_1128_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_);
if (lean_obj_tag(v___x_1128_) == 0)
{
lean_object* v_a_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1140_; 
v_a_1129_ = lean_ctor_get(v___x_1128_, 0);
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_1128_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1131_ = v___x_1128_;
v_isShared_1132_ = v_isSharedCheck_1140_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_a_1129_);
lean_dec(v___x_1128_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1140_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v_orderedAddInst_x3f_1133_; 
v_orderedAddInst_x3f_1133_ = lean_ctor_get(v_a_1129_, 9);
lean_inc(v_orderedAddInst_x3f_1133_);
lean_dec(v_a_1129_);
if (lean_obj_tag(v_orderedAddInst_x3f_1133_) == 1)
{
lean_object* v_val_1134_; lean_object* v___x_1136_; 
v_val_1134_ = lean_ctor_get(v_orderedAddInst_x3f_1133_, 0);
lean_inc(v_val_1134_);
lean_dec_ref_known(v_orderedAddInst_x3f_1133_, 1);
if (v_isShared_1132_ == 0)
{
lean_ctor_set(v___x_1131_, 0, v_val_1134_);
v___x_1136_ = v___x_1131_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_val_1134_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
else
{
lean_object* v___x_1138_; lean_object* v___x_1139_; 
lean_dec(v_orderedAddInst_x3f_1133_);
lean_del_object(v___x_1131_);
v___x_1138_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1);
v___x_1139_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_1138_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_);
return v___x_1139_;
}
}
}
else
{
lean_object* v_a_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1148_; 
v_a_1141_ = lean_ctor_get(v___x_1128_, 0);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1128_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1143_ = v___x_1128_;
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_a_1141_);
lean_dec(v___x_1128_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1146_; 
if (v_isShared_1144_ == 0)
{
v___x_1146_ = v___x_1143_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_a_1141_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1116_ = stack[0].m_obj;
lean_object* v_a_1117_ = stack[1].m_obj;
lean_object* v_a_1118_ = stack[2].m_obj;
lean_object* v_a_1119_ = stack[3].m_obj;
lean_object* v_a_1120_ = stack[4].m_obj;
lean_object* v_a_1121_ = stack[5].m_obj;
lean_object* v_a_1122_ = stack[6].m_obj;
lean_object* v_a_1123_ = stack[7].m_obj;
lean_object* v_a_1124_ = stack[8].m_obj;
lean_object* v_a_1125_ = stack[9].m_obj;
lean_object* v_a_1126_ = stack[10].m_obj;
lean_object* v_res_1149_;
v_res_1149_ = l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst(v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_);
stack->m_obj
 = v_res_1149_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___boxed(lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_){
_start:
{
lean_object* v_res_1162_; 
v_res_1162_ = l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst(v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_);
lean_dec(v_a_1160_);
lean_dec_ref(v_a_1159_);
lean_dec(v_a_1158_);
lean_dec_ref(v_a_1157_);
lean_dec(v_a_1156_);
lean_dec_ref(v_a_1155_);
lean_dec(v_a_1154_);
lean_dec_ref(v_a_1153_);
lean_dec(v_a_1152_);
lean_dec(v_a_1151_);
lean_dec(v_a_1150_);
return v_res_1162_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_isOrderedAdd(lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_){
_start:
{
lean_object* v___x_1175_; 
v___x_1175_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_, v_a_1173_);
if (lean_obj_tag(v___x_1175_) == 0)
{
lean_object* v_a_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1191_; 
v_a_1176_ = lean_ctor_get(v___x_1175_, 0);
v_isSharedCheck_1191_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1178_ = v___x_1175_;
v_isShared_1179_ = v_isSharedCheck_1191_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_a_1176_);
lean_dec(v___x_1175_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1191_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v_orderedAddInst_x3f_1180_; 
v_orderedAddInst_x3f_1180_ = lean_ctor_get(v_a_1176_, 9);
lean_inc(v_orderedAddInst_x3f_1180_);
lean_dec(v_a_1176_);
if (lean_obj_tag(v_orderedAddInst_x3f_1180_) == 0)
{
uint8_t v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1184_; 
v___x_1181_ = 0;
v___x_1182_ = lean_box(v___x_1181_);
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 0, v___x_1182_);
v___x_1184_ = v___x_1178_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v___x_1182_);
v___x_1184_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
return v___x_1184_;
}
}
else
{
uint8_t v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1189_; 
lean_dec_ref_known(v_orderedAddInst_x3f_1180_, 1);
v___x_1186_ = 1;
v___x_1187_ = lean_box(v___x_1186_);
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 0, v___x_1187_);
v___x_1189_ = v___x_1178_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v___x_1187_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
}
}
else
{
lean_object* v_a_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1199_; 
v_a_1192_ = lean_ctor_get(v___x_1175_, 0);
v_isSharedCheck_1199_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1194_ = v___x_1175_;
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_a_1192_);
lean_dec(v___x_1175_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1197_; 
if (v_isShared_1195_ == 0)
{
v___x_1197_ = v___x_1194_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v_a_1192_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
return v___x_1197_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_isOrderedAdd_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1163_ = stack[0].m_obj;
lean_object* v_a_1164_ = stack[1].m_obj;
lean_object* v_a_1165_ = stack[2].m_obj;
lean_object* v_a_1166_ = stack[3].m_obj;
lean_object* v_a_1167_ = stack[4].m_obj;
lean_object* v_a_1168_ = stack[5].m_obj;
lean_object* v_a_1169_ = stack[6].m_obj;
lean_object* v_a_1170_ = stack[7].m_obj;
lean_object* v_a_1171_ = stack[8].m_obj;
lean_object* v_a_1172_ = stack[9].m_obj;
lean_object* v_a_1173_ = stack[10].m_obj;
lean_object* v_res_1200_;
v_res_1200_ = l_Lean_Meta_Grind_Arith_Linear_isOrderedAdd(v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_, v_a_1173_);
stack->m_obj
 = v_res_1200_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isOrderedAdd___boxed(lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_){
_start:
{
lean_object* v_res_1213_; 
v_res_1213_ = l_Lean_Meta_Grind_Arith_Linear_isOrderedAdd(v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_);
lean_dec(v_a_1211_);
lean_dec_ref(v_a_1210_);
lean_dec(v_a_1209_);
lean_dec_ref(v_a_1208_);
lean_dec(v_a_1207_);
lean_dec_ref(v_a_1206_);
lean_dec(v_a_1205_);
lean_dec_ref(v_a_1204_);
lean_dec(v_a_1203_);
lean_dec(v_a_1202_);
lean_dec(v_a_1201_);
return v_res_1213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___redArg___lam__0(lean_object* v_toPure_1214_, lean_object* v_inst_1215_, lean_object* v_inst_1216_, lean_object* v_____do__lift_1217_){
_start:
{
lean_object* v_ltFn_x3f_1218_; 
v_ltFn_x3f_1218_ = lean_ctor_get(v_____do__lift_1217_, 21);
lean_inc(v_ltFn_x3f_1218_);
lean_dec_ref(v_____do__lift_1217_);
if (lean_obj_tag(v_ltFn_x3f_1218_) == 1)
{
lean_object* v_val_1219_; lean_object* v___x_1220_; 
lean_dec_ref(v_inst_1216_);
lean_dec_ref(v_inst_1215_);
v_val_1219_ = lean_ctor_get(v_ltFn_x3f_1218_, 0);
lean_inc(v_val_1219_);
lean_dec_ref_known(v_ltFn_x3f_1218_, 1);
v___x_1220_ = lean_apply_2(v_toPure_1214_, lean_box(0), v_val_1219_);
return v___x_1220_;
}
else
{
lean_object* v___x_1221_; lean_object* v___x_1222_; 
lean_dec(v_ltFn_x3f_1218_);
lean_dec(v_toPure_1214_);
v___x_1221_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1);
v___x_1222_ = l_Lean_throwError___redArg(v_inst_1215_, v_inst_1216_, v___x_1221_);
return v___x_1222_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___redArg(lean_object* v_inst_1223_, lean_object* v_inst_1224_, lean_object* v_inst_1225_){
_start:
{
lean_object* v_toApplicative_1226_; lean_object* v_toBind_1227_; lean_object* v_toPure_1228_; lean_object* v___f_1229_; lean_object* v___x_1230_; 
v_toApplicative_1226_ = lean_ctor_get(v_inst_1223_, 0);
v_toBind_1227_ = lean_ctor_get(v_inst_1223_, 1);
lean_inc(v_toBind_1227_);
v_toPure_1228_ = lean_ctor_get(v_toApplicative_1226_, 1);
lean_inc(v_toPure_1228_);
v___f_1229_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_getLtFn___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1229_, 0, v_toPure_1228_);
lean_closure_set(v___f_1229_, 1, v_inst_1223_);
lean_closure_set(v___f_1229_, 2, v_inst_1224_);
v___x_1230_ = lean_apply_4(v_toBind_1227_, lean_box(0), lean_box(0), v_inst_1225_, v___f_1229_);
return v___x_1230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn(lean_object* v_m_1231_, lean_object* v_inst_1232_, lean_object* v_inst_1233_, lean_object* v_inst_1234_){
_start:
{
lean_object* v___x_1235_; 
v___x_1235_ = l_Lean_Meta_Grind_Arith_Linear_getLtFn___redArg(v_inst_1232_, v_inst_1233_, v_inst_1234_);
return v___x_1235_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; 
v___x_1237_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0___closed__0));
v___x_1238_ = l_Lean_stringToMessageData(v___x_1237_);
return v___x_1238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0(lean_object* v_toPure_1239_, lean_object* v_inst_1240_, lean_object* v_inst_1241_, lean_object* v_____do__lift_1242_){
_start:
{
lean_object* v_leFn_x3f_1243_; 
v_leFn_x3f_1243_ = lean_ctor_get(v_____do__lift_1242_, 20);
lean_inc(v_leFn_x3f_1243_);
lean_dec_ref(v_____do__lift_1242_);
if (lean_obj_tag(v_leFn_x3f_1243_) == 1)
{
lean_object* v_val_1244_; lean_object* v___x_1245_; 
lean_dec_ref(v_inst_1241_);
lean_dec_ref(v_inst_1240_);
v_val_1244_ = lean_ctor_get(v_leFn_x3f_1243_, 0);
lean_inc(v_val_1244_);
lean_dec_ref_known(v_leFn_x3f_1243_, 1);
v___x_1245_ = lean_apply_2(v_toPure_1239_, lean_box(0), v_val_1244_);
return v___x_1245_;
}
else
{
lean_object* v___x_1246_; lean_object* v___x_1247_; 
lean_dec(v_leFn_x3f_1243_);
lean_dec(v_toPure_1239_);
v___x_1246_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0___closed__1);
v___x_1247_ = l_Lean_throwError___redArg(v_inst_1240_, v_inst_1241_, v___x_1246_);
return v___x_1247_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg(lean_object* v_inst_1248_, lean_object* v_inst_1249_, lean_object* v_inst_1250_){
_start:
{
lean_object* v_toApplicative_1251_; lean_object* v_toBind_1252_; lean_object* v_toPure_1253_; lean_object* v___f_1254_; lean_object* v___x_1255_; 
v_toApplicative_1251_ = lean_ctor_get(v_inst_1248_, 0);
v_toBind_1252_ = lean_ctor_get(v_inst_1248_, 1);
lean_inc(v_toBind_1252_);
v_toPure_1253_ = lean_ctor_get(v_toApplicative_1251_, 1);
lean_inc(v_toPure_1253_);
v___f_1254_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1254_, 0, v_toPure_1253_);
lean_closure_set(v___f_1254_, 1, v_inst_1248_);
lean_closure_set(v___f_1254_, 2, v_inst_1249_);
v___x_1255_ = lean_apply_4(v_toBind_1252_, lean_box(0), lean_box(0), v_inst_1250_, v___f_1254_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn(lean_object* v_m_1256_, lean_object* v_inst_1257_, lean_object* v_inst_1258_, lean_object* v_inst_1259_){
_start:
{
lean_object* v___x_1260_; 
v___x_1260_ = l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg(v_inst_1257_, v_inst_1258_, v_inst_1259_);
return v___x_1260_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___closed__1(void){
_start:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1262_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___closed__0));
v___x_1263_ = l_Lean_stringToMessageData(v___x_1262_);
return v___x_1263_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst(lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_){
_start:
{
lean_object* v___x_1276_; 
v___x_1276_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_);
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_object* v_a_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1288_; 
v_a_1277_ = lean_ctor_get(v___x_1276_, 0);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___x_1276_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1279_ = v___x_1276_;
v_isShared_1280_ = v_isSharedCheck_1288_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_a_1277_);
lean_dec(v___x_1276_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1288_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v_isLinearInst_x3f_1281_; 
v_isLinearInst_x3f_1281_ = lean_ctor_get(v_a_1277_, 10);
lean_inc(v_isLinearInst_x3f_1281_);
lean_dec(v_a_1277_);
if (lean_obj_tag(v_isLinearInst_x3f_1281_) == 1)
{
lean_object* v_val_1282_; lean_object* v___x_1284_; 
v_val_1282_ = lean_ctor_get(v_isLinearInst_x3f_1281_, 0);
lean_inc(v_val_1282_);
lean_dec_ref_known(v_isLinearInst_x3f_1281_, 1);
if (v_isShared_1280_ == 0)
{
lean_ctor_set(v___x_1279_, 0, v_val_1282_);
v___x_1284_ = v___x_1279_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v_val_1282_);
v___x_1284_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
return v___x_1284_;
}
}
else
{
lean_object* v___x_1286_; lean_object* v___x_1287_; 
lean_dec(v_isLinearInst_x3f_1281_);
lean_del_object(v___x_1279_);
v___x_1286_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___closed__1);
v___x_1287_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_1286_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_);
return v___x_1287_;
}
}
}
else
{
lean_object* v_a_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1296_; 
v_a_1289_ = lean_ctor_get(v___x_1276_, 0);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___x_1276_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1291_ = v___x_1276_;
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_a_1289_);
lean_dec(v___x_1276_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1296_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v___x_1294_; 
if (v_isShared_1292_ == 0)
{
v___x_1294_ = v___x_1291_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_a_1289_);
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
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1264_ = stack[0].m_obj;
lean_object* v_a_1265_ = stack[1].m_obj;
lean_object* v_a_1266_ = stack[2].m_obj;
lean_object* v_a_1267_ = stack[3].m_obj;
lean_object* v_a_1268_ = stack[4].m_obj;
lean_object* v_a_1269_ = stack[5].m_obj;
lean_object* v_a_1270_ = stack[6].m_obj;
lean_object* v_a_1271_ = stack[7].m_obj;
lean_object* v_a_1272_ = stack[8].m_obj;
lean_object* v_a_1273_ = stack[9].m_obj;
lean_object* v_a_1274_ = stack[10].m_obj;
lean_object* v_res_1297_;
v_res_1297_ = l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst(v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_);
stack->m_obj
 = v_res_1297_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___boxed(lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_){
_start:
{
lean_object* v_res_1310_; 
v_res_1310_ = l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst(v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_);
lean_dec(v_a_1308_);
lean_dec_ref(v_a_1307_);
lean_dec(v_a_1306_);
lean_dec_ref(v_a_1305_);
lean_dec(v_a_1304_);
lean_dec_ref(v_a_1303_);
lean_dec(v_a_1302_);
lean_dec_ref(v_a_1301_);
lean_dec(v_a_1300_);
lean_dec(v_a_1299_);
lean_dec(v_a_1298_);
return v_res_1310_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getRingInst___closed__1(void){
_start:
{
lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1312_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getRingInst___closed__0));
v___x_1313_ = l_Lean_stringToMessageData(v___x_1312_);
return v___x_1313_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_getRingInst(lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_){
_start:
{
lean_object* v___x_1326_; 
v___x_1326_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
if (lean_obj_tag(v___x_1326_) == 0)
{
lean_object* v_a_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1338_; 
v_a_1327_ = lean_ctor_get(v___x_1326_, 0);
v_isSharedCheck_1338_ = !lean_is_exclusive(v___x_1326_);
if (v_isSharedCheck_1338_ == 0)
{
v___x_1329_ = v___x_1326_;
v_isShared_1330_ = v_isSharedCheck_1338_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_a_1327_);
lean_dec(v___x_1326_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1338_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v_ringInst_x3f_1331_; 
v_ringInst_x3f_1331_ = lean_ctor_get(v_a_1327_, 12);
lean_inc(v_ringInst_x3f_1331_);
lean_dec(v_a_1327_);
if (lean_obj_tag(v_ringInst_x3f_1331_) == 1)
{
lean_object* v_val_1332_; lean_object* v___x_1334_; 
v_val_1332_ = lean_ctor_get(v_ringInst_x3f_1331_, 0);
lean_inc(v_val_1332_);
lean_dec_ref_known(v_ringInst_x3f_1331_, 1);
if (v_isShared_1330_ == 0)
{
lean_ctor_set(v___x_1329_, 0, v_val_1332_);
v___x_1334_ = v___x_1329_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v_val_1332_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
return v___x_1334_;
}
}
else
{
lean_object* v___x_1336_; lean_object* v___x_1337_; 
lean_dec(v_ringInst_x3f_1331_);
lean_del_object(v___x_1329_);
v___x_1336_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getRingInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getRingInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getRingInst___closed__1);
v___x_1337_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_1336_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
return v___x_1337_;
}
}
}
else
{
lean_object* v_a_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1346_; 
v_a_1339_ = lean_ctor_get(v___x_1326_, 0);
v_isSharedCheck_1346_ = !lean_is_exclusive(v___x_1326_);
if (v_isSharedCheck_1346_ == 0)
{
v___x_1341_ = v___x_1326_;
v_isShared_1342_ = v_isSharedCheck_1346_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_a_1339_);
lean_dec(v___x_1326_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1346_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v___x_1344_; 
if (v_isShared_1342_ == 0)
{
v___x_1344_ = v___x_1341_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v_a_1339_);
v___x_1344_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
return v___x_1344_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_getRingInst_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1314_ = stack[0].m_obj;
lean_object* v_a_1315_ = stack[1].m_obj;
lean_object* v_a_1316_ = stack[2].m_obj;
lean_object* v_a_1317_ = stack[3].m_obj;
lean_object* v_a_1318_ = stack[4].m_obj;
lean_object* v_a_1319_ = stack[5].m_obj;
lean_object* v_a_1320_ = stack[6].m_obj;
lean_object* v_a_1321_ = stack[7].m_obj;
lean_object* v_a_1322_ = stack[8].m_obj;
lean_object* v_a_1323_ = stack[9].m_obj;
lean_object* v_a_1324_ = stack[10].m_obj;
lean_object* v_res_1347_;
v_res_1347_ = l_Lean_Meta_Grind_Arith_Linear_getRingInst(v_a_1314_, v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
stack->m_obj
 = v_res_1347_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getRingInst___boxed(lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_){
_start:
{
lean_object* v_res_1360_; 
v_res_1360_ = l_Lean_Meta_Grind_Arith_Linear_getRingInst(v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_);
lean_dec(v_a_1358_);
lean_dec_ref(v_a_1357_);
lean_dec(v_a_1356_);
lean_dec_ref(v_a_1355_);
lean_dec(v_a_1354_);
lean_dec_ref(v_a_1353_);
lean_dec(v_a_1352_);
lean_dec_ref(v_a_1351_);
lean_dec(v_a_1350_);
lean_dec(v_a_1349_);
lean_dec(v_a_1348_);
return v_res_1360_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___closed__1(void){
_start:
{
lean_object* v___x_1362_; lean_object* v___x_1363_; 
v___x_1362_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___closed__0));
v___x_1363_ = l_Lean_stringToMessageData(v___x_1362_);
return v___x_1363_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_getCommRingInst(lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_){
_start:
{
lean_object* v___x_1376_; 
v___x_1376_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_);
if (lean_obj_tag(v___x_1376_) == 0)
{
lean_object* v_a_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1388_; 
v_a_1377_ = lean_ctor_get(v___x_1376_, 0);
v_isSharedCheck_1388_ = !lean_is_exclusive(v___x_1376_);
if (v_isSharedCheck_1388_ == 0)
{
v___x_1379_ = v___x_1376_;
v_isShared_1380_ = v_isSharedCheck_1388_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_a_1377_);
lean_dec(v___x_1376_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1388_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v_commRingInst_x3f_1381_; 
v_commRingInst_x3f_1381_ = lean_ctor_get(v_a_1377_, 13);
lean_inc(v_commRingInst_x3f_1381_);
lean_dec(v_a_1377_);
if (lean_obj_tag(v_commRingInst_x3f_1381_) == 1)
{
lean_object* v_val_1382_; lean_object* v___x_1384_; 
v_val_1382_ = lean_ctor_get(v_commRingInst_x3f_1381_, 0);
lean_inc(v_val_1382_);
lean_dec_ref_known(v_commRingInst_x3f_1381_, 1);
if (v_isShared_1380_ == 0)
{
lean_ctor_set(v___x_1379_, 0, v_val_1382_);
v___x_1384_ = v___x_1379_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v_val_1382_);
v___x_1384_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
return v___x_1384_;
}
}
else
{
lean_object* v___x_1386_; lean_object* v___x_1387_; 
lean_dec(v_commRingInst_x3f_1381_);
lean_del_object(v___x_1379_);
v___x_1386_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___closed__1);
v___x_1387_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_1386_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_);
return v___x_1387_;
}
}
}
else
{
lean_object* v_a_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1396_; 
v_a_1389_ = lean_ctor_get(v___x_1376_, 0);
v_isSharedCheck_1396_ = !lean_is_exclusive(v___x_1376_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1391_ = v___x_1376_;
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_a_1389_);
lean_dec(v___x_1376_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1394_; 
if (v_isShared_1392_ == 0)
{
v___x_1394_ = v___x_1391_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v_a_1389_);
v___x_1394_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
return v___x_1394_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_getCommRingInst_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1364_ = stack[0].m_obj;
lean_object* v_a_1365_ = stack[1].m_obj;
lean_object* v_a_1366_ = stack[2].m_obj;
lean_object* v_a_1367_ = stack[3].m_obj;
lean_object* v_a_1368_ = stack[4].m_obj;
lean_object* v_a_1369_ = stack[5].m_obj;
lean_object* v_a_1370_ = stack[6].m_obj;
lean_object* v_a_1371_ = stack[7].m_obj;
lean_object* v_a_1372_ = stack[8].m_obj;
lean_object* v_a_1373_ = stack[9].m_obj;
lean_object* v_a_1374_ = stack[10].m_obj;
lean_object* v_res_1397_;
v_res_1397_ = l_Lean_Meta_Grind_Arith_Linear_getCommRingInst(v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_);
stack->m_obj
 = v_res_1397_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___boxed(lean_object* v_a_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_){
_start:
{
lean_object* v_res_1410_; 
v_res_1410_ = l_Lean_Meta_Grind_Arith_Linear_getCommRingInst(v_a_1398_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_, v_a_1404_, v_a_1405_, v_a_1406_, v_a_1407_, v_a_1408_);
lean_dec(v_a_1408_);
lean_dec_ref(v_a_1407_);
lean_dec(v_a_1406_);
lean_dec_ref(v_a_1405_);
lean_dec(v_a_1404_);
lean_dec_ref(v_a_1403_);
lean_dec(v_a_1402_);
lean_dec_ref(v_a_1401_);
lean_dec(v_a_1400_);
lean_dec(v_a_1399_);
lean_dec(v_a_1398_);
return v_res_1410_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___closed__1(void){
_start:
{
lean_object* v___x_1412_; lean_object* v___x_1413_; 
v___x_1412_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___closed__0));
v___x_1413_ = l_Lean_stringToMessageData(v___x_1412_);
return v___x_1413_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst(lean_object* v_a_1414_, lean_object* v_a_1415_, lean_object* v_a_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_){
_start:
{
lean_object* v___x_1426_; 
v___x_1426_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1414_, v_a_1415_, v_a_1416_, v_a_1417_, v_a_1418_, v_a_1419_, v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_, v_a_1424_);
if (lean_obj_tag(v___x_1426_) == 0)
{
lean_object* v_a_1427_; lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1438_; 
v_a_1427_ = lean_ctor_get(v___x_1426_, 0);
v_isSharedCheck_1438_ = !lean_is_exclusive(v___x_1426_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1429_ = v___x_1426_;
v_isShared_1430_ = v_isSharedCheck_1438_;
goto v_resetjp_1428_;
}
else
{
lean_inc(v_a_1427_);
lean_dec(v___x_1426_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1438_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
lean_object* v_orderedRingInst_x3f_1431_; 
v_orderedRingInst_x3f_1431_ = lean_ctor_get(v_a_1427_, 14);
lean_inc(v_orderedRingInst_x3f_1431_);
lean_dec(v_a_1427_);
if (lean_obj_tag(v_orderedRingInst_x3f_1431_) == 1)
{
lean_object* v_val_1432_; lean_object* v___x_1434_; 
v_val_1432_ = lean_ctor_get(v_orderedRingInst_x3f_1431_, 0);
lean_inc(v_val_1432_);
lean_dec_ref_known(v_orderedRingInst_x3f_1431_, 1);
if (v_isShared_1430_ == 0)
{
lean_ctor_set(v___x_1429_, 0, v_val_1432_);
v___x_1434_ = v___x_1429_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v_val_1432_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
return v___x_1434_;
}
}
else
{
lean_object* v___x_1436_; lean_object* v___x_1437_; 
lean_dec(v_orderedRingInst_x3f_1431_);
lean_del_object(v___x_1429_);
v___x_1436_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___closed__1);
v___x_1437_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_1436_, v_a_1421_, v_a_1422_, v_a_1423_, v_a_1424_);
return v___x_1437_;
}
}
}
else
{
lean_object* v_a_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1446_; 
v_a_1439_ = lean_ctor_get(v___x_1426_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___x_1426_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1441_ = v___x_1426_;
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_a_1439_);
lean_dec(v___x_1426_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1444_; 
if (v_isShared_1442_ == 0)
{
v___x_1444_ = v___x_1441_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_a_1439_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1414_ = stack[0].m_obj;
lean_object* v_a_1415_ = stack[1].m_obj;
lean_object* v_a_1416_ = stack[2].m_obj;
lean_object* v_a_1417_ = stack[3].m_obj;
lean_object* v_a_1418_ = stack[4].m_obj;
lean_object* v_a_1419_ = stack[5].m_obj;
lean_object* v_a_1420_ = stack[6].m_obj;
lean_object* v_a_1421_ = stack[7].m_obj;
lean_object* v_a_1422_ = stack[8].m_obj;
lean_object* v_a_1423_ = stack[9].m_obj;
lean_object* v_a_1424_ = stack[10].m_obj;
lean_object* v_res_1447_;
v_res_1447_ = l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst(v_a_1414_, v_a_1415_, v_a_1416_, v_a_1417_, v_a_1418_, v_a_1419_, v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_, v_a_1424_);
stack->m_obj
 = v_res_1447_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___boxed(lean_object* v_a_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_){
_start:
{
lean_object* v_res_1460_; 
v_res_1460_ = l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst(v_a_1448_, v_a_1449_, v_a_1450_, v_a_1451_, v_a_1452_, v_a_1453_, v_a_1454_, v_a_1455_, v_a_1456_, v_a_1457_, v_a_1458_);
lean_dec(v_a_1458_);
lean_dec_ref(v_a_1457_);
lean_dec(v_a_1456_);
lean_dec_ref(v_a_1455_);
lean_dec(v_a_1454_);
lean_dec_ref(v_a_1453_);
lean_dec(v_a_1452_);
lean_dec_ref(v_a_1451_);
lean_dec(v_a_1450_);
lean_dec(v_a_1449_);
lean_dec(v_a_1448_);
return v_res_1460_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_eval_x3f_go_spec__0(lean_object* v_a_1461_){
_start:
{
lean_object* v___x_1462_; 
v___x_1462_ = l_Rat_ofInt(v_a_1461_);
return v___x_1462_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_eval_x3f_go(lean_object* v_a_1463_, lean_object* v_v_1464_, lean_object* v_a_1465_){
_start:
{
if (lean_obj_tag(v_a_1465_) == 0)
{
lean_object* v___x_1466_; 
v___x_1466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1466_, 0, v_v_1464_);
return v___x_1466_;
}
else
{
lean_object* v_k_1467_; lean_object* v_v_1468_; lean_object* v_p_1469_; lean_object* v_size_1470_; uint8_t v___x_1471_; 
v_k_1467_ = lean_ctor_get(v_a_1465_, 0);
lean_inc(v_k_1467_);
v_v_1468_ = lean_ctor_get(v_a_1465_, 1);
lean_inc(v_v_1468_);
v_p_1469_ = lean_ctor_get(v_a_1465_, 2);
lean_inc(v_p_1469_);
lean_dec_ref_known(v_a_1465_, 3);
v_size_1470_ = lean_ctor_get(v_a_1463_, 2);
v___x_1471_ = lean_nat_dec_lt(v_v_1468_, v_size_1470_);
if (v___x_1471_ == 0)
{
lean_object* v___x_1472_; 
lean_dec(v_p_1469_);
lean_dec(v_v_1468_);
lean_dec(v_k_1467_);
lean_dec_ref(v_v_1464_);
v___x_1472_ = lean_box(0);
return v___x_1472_;
}
else
{
lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; 
v___x_1473_ = l_instInhabitedRat;
v___x_1474_ = l_Rat_ofInt(v_k_1467_);
v___x_1475_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1473_, v_a_1463_, v_v_1468_);
lean_dec(v_v_1468_);
v___x_1476_ = l_Rat_mul(v___x_1474_, v___x_1475_);
lean_dec_ref(v___x_1474_);
v___x_1477_ = l_Rat_add(v_v_1464_, v___x_1476_);
v_v_1464_ = v___x_1477_;
v_a_1465_ = v_p_1469_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_eval_x3f_go___boxed(lean_object* v_a_1479_, lean_object* v_v_1480_, lean_object* v_a_1481_){
_start:
{
lean_object* v_res_1482_; 
v_res_1482_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_eval_x3f_go(v_a_1479_, v_v_1480_, v_a_1481_);
lean_dec_ref(v_a_1479_);
return v_res_1482_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Grind_Linarith_Poly_eval_x3f_spec__0(lean_object* v_a_1483_){
_start:
{
lean_object* v___x_1484_; lean_object* v___x_1485_; 
v___x_1484_ = lean_nat_to_int(v_a_1483_);
v___x_1485_ = l_Rat_ofInt(v___x_1484_);
return v___x_1485_;
}
}
static lean_object* _init_l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0(void){
_start:
{
lean_object* v___x_1486_; lean_object* v___x_1487_; 
v___x_1486_ = lean_unsigned_to_nat(0u);
v___x_1487_ = l_Nat_cast___at___00Lean_Grind_Linarith_Poly_eval_x3f_spec__0(v___x_1486_);
return v___x_1487_;
}
}
lean_object* l_Lean_Grind_Linarith_Poly_eval_x3f(lean_object* v_p_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_){
_start:
{
lean_object* v___x_1501_; 
v___x_1501_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_);
if (lean_obj_tag(v___x_1501_) == 0)
{
lean_object* v_a_1502_; lean_object* v___x_1504_; uint8_t v_isShared_1505_; uint8_t v_isSharedCheck_1512_; 
v_a_1502_ = lean_ctor_get(v___x_1501_, 0);
v_isSharedCheck_1512_ = !lean_is_exclusive(v___x_1501_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1504_ = v___x_1501_;
v_isShared_1505_ = v_isSharedCheck_1512_;
goto v_resetjp_1503_;
}
else
{
lean_inc(v_a_1502_);
lean_dec(v___x_1501_);
v___x_1504_ = lean_box(0);
v_isShared_1505_ = v_isSharedCheck_1512_;
goto v_resetjp_1503_;
}
v_resetjp_1503_:
{
lean_object* v_assignment_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1510_; 
v_assignment_1506_ = lean_ctor_get(v_a_1502_, 35);
lean_inc_ref(v_assignment_1506_);
lean_dec(v_a_1502_);
v___x_1507_ = lean_obj_once(&l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0, &l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0_once, _init_l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0);
v___x_1508_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_eval_x3f_go(v_assignment_1506_, v___x_1507_, v_p_1488_);
lean_dec_ref(v_assignment_1506_);
if (v_isShared_1505_ == 0)
{
lean_ctor_set(v___x_1504_, 0, v___x_1508_);
v___x_1510_ = v___x_1504_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v___x_1508_);
v___x_1510_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
return v___x_1510_;
}
}
}
else
{
lean_object* v_a_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1520_; 
lean_dec(v_p_1488_);
v_a_1513_ = lean_ctor_get(v___x_1501_, 0);
v_isSharedCheck_1520_ = !lean_is_exclusive(v___x_1501_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1515_ = v___x_1501_;
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_a_1513_);
lean_dec(v___x_1501_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v___x_1518_; 
if (v_isShared_1516_ == 0)
{
v___x_1518_ = v___x_1515_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1519_; 
v_reuseFailAlloc_1519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1519_, 0, v_a_1513_);
v___x_1518_ = v_reuseFailAlloc_1519_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
return v___x_1518_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Grind_Linarith_Poly_eval_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1488_ = stack[0].m_obj;
lean_object* v_a_1489_ = stack[1].m_obj;
lean_object* v_a_1490_ = stack[2].m_obj;
lean_object* v_a_1491_ = stack[3].m_obj;
lean_object* v_a_1492_ = stack[4].m_obj;
lean_object* v_a_1493_ = stack[5].m_obj;
lean_object* v_a_1494_ = stack[6].m_obj;
lean_object* v_a_1495_ = stack[7].m_obj;
lean_object* v_a_1496_ = stack[8].m_obj;
lean_object* v_a_1497_ = stack[9].m_obj;
lean_object* v_a_1498_ = stack[10].m_obj;
lean_object* v_a_1499_ = stack[11].m_obj;
lean_object* v_res_1521_;
v_res_1521_ = l_Lean_Grind_Linarith_Poly_eval_x3f(v_p_1488_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_);
stack->m_obj
 = v_res_1521_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_eval_x3f___boxed(lean_object* v_p_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_){
_start:
{
lean_object* v_res_1535_; 
v_res_1535_ = l_Lean_Grind_Linarith_Poly_eval_x3f(v_p_1522_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_, v_a_1527_, v_a_1528_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_);
lean_dec(v_a_1533_);
lean_dec_ref(v_a_1532_);
lean_dec(v_a_1531_);
lean_dec_ref(v_a_1530_);
lean_dec(v_a_1529_);
lean_dec_ref(v_a_1528_);
lean_dec(v_a_1527_);
lean_dec_ref(v_a_1526_);
lean_dec(v_a_1525_);
lean_dec(v_a_1524_);
lean_dec(v_a_1523_);
return v_res_1535_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00Lean_Grind_Linarith_Poly_eval_x3f_spec__0_spec__0(lean_object* v_a_1536_){
_start:
{
lean_object* v___x_1537_; 
v___x_1537_ = lean_nat_to_int(v_a_1536_);
return v___x_1537_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_satisfied(lean_object* v_c_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_){
_start:
{
lean_object* v_p_1551_; uint8_t v_strict_1552_; lean_object* v___x_1553_; 
v_p_1551_ = lean_ctor_get(v_c_1538_, 0);
lean_inc(v_p_1551_);
v_strict_1552_ = lean_ctor_get_uint8(v_c_1538_, sizeof(void*)*2);
lean_dec_ref(v_c_1538_);
v___x_1553_ = l_Lean_Grind_Linarith_Poly_eval_x3f(v_p_1551_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_, v_a_1543_, v_a_1544_, v_a_1545_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_);
if (lean_obj_tag(v___x_1553_) == 0)
{
lean_object* v_a_1554_; lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1579_; 
v_a_1554_ = lean_ctor_get(v___x_1553_, 0);
v_isSharedCheck_1579_ = !lean_is_exclusive(v___x_1553_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1556_ = v___x_1553_;
v_isShared_1557_ = v_isSharedCheck_1579_;
goto v_resetjp_1555_;
}
else
{
lean_inc(v_a_1554_);
lean_dec(v___x_1553_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1579_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
if (lean_obj_tag(v_a_1554_) == 1)
{
if (v_strict_1552_ == 0)
{
lean_object* v_val_1558_; lean_object* v___x_1559_; uint8_t v___x_1560_; uint8_t v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1564_; 
v_val_1558_ = lean_ctor_get(v_a_1554_, 0);
lean_inc(v_val_1558_);
lean_dec_ref_known(v_a_1554_, 1);
v___x_1559_ = lean_obj_once(&l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0, &l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0_once, _init_l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0);
v___x_1560_ = l_Rat_instDecidableLe(v_val_1558_, v___x_1559_);
v___x_1561_ = l_Lean_Bool_toLBool(v___x_1560_);
v___x_1562_ = lean_box(v___x_1561_);
if (v_isShared_1557_ == 0)
{
lean_ctor_set(v___x_1556_, 0, v___x_1562_);
v___x_1564_ = v___x_1556_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v___x_1562_);
v___x_1564_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
return v___x_1564_;
}
}
else
{
lean_object* v_val_1566_; lean_object* v___x_1567_; uint8_t v___x_1568_; uint8_t v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1572_; 
v_val_1566_ = lean_ctor_get(v_a_1554_, 0);
lean_inc(v_val_1566_);
lean_dec_ref_known(v_a_1554_, 1);
v___x_1567_ = lean_obj_once(&l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0, &l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0_once, _init_l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0);
v___x_1568_ = l_Rat_blt(v_val_1566_, v___x_1567_);
v___x_1569_ = l_Lean_Bool_toLBool(v___x_1568_);
v___x_1570_ = lean_box(v___x_1569_);
if (v_isShared_1557_ == 0)
{
lean_ctor_set(v___x_1556_, 0, v___x_1570_);
v___x_1572_ = v___x_1556_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v___x_1570_);
v___x_1572_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
return v___x_1572_;
}
}
}
else
{
uint8_t v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1577_; 
lean_dec(v_a_1554_);
v___x_1574_ = 2;
v___x_1575_ = lean_box(v___x_1574_);
if (v_isShared_1557_ == 0)
{
lean_ctor_set(v___x_1556_, 0, v___x_1575_);
v___x_1577_ = v___x_1556_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v___x_1575_);
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
else
{
lean_object* v_a_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1587_; 
v_a_1580_ = lean_ctor_get(v___x_1553_, 0);
v_isSharedCheck_1587_ = !lean_is_exclusive(v___x_1553_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1582_ = v___x_1553_;
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_a_1580_);
lean_dec(v___x_1553_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
lean_object* v___x_1585_; 
if (v_isShared_1583_ == 0)
{
v___x_1585_ = v___x_1582_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v_a_1580_);
v___x_1585_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
return v___x_1585_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_satisfied_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_1538_ = stack[0].m_obj;
lean_object* v_a_1539_ = stack[1].m_obj;
lean_object* v_a_1540_ = stack[2].m_obj;
lean_object* v_a_1541_ = stack[3].m_obj;
lean_object* v_a_1542_ = stack[4].m_obj;
lean_object* v_a_1543_ = stack[5].m_obj;
lean_object* v_a_1544_ = stack[6].m_obj;
lean_object* v_a_1545_ = stack[7].m_obj;
lean_object* v_a_1546_ = stack[8].m_obj;
lean_object* v_a_1547_ = stack[9].m_obj;
lean_object* v_a_1548_ = stack[10].m_obj;
lean_object* v_a_1549_ = stack[11].m_obj;
lean_object* v_res_1588_;
v_res_1588_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_satisfied(v_c_1538_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_, v_a_1543_, v_a_1544_, v_a_1545_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_);
stack->m_obj
 = v_res_1588_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_satisfied___boxed(lean_object* v_c_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_){
_start:
{
lean_object* v_res_1602_; 
v_res_1602_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_satisfied(v_c_1589_, v_a_1590_, v_a_1591_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_);
lean_dec(v_a_1600_);
lean_dec_ref(v_a_1599_);
lean_dec(v_a_1598_);
lean_dec_ref(v_a_1597_);
lean_dec(v_a_1596_);
lean_dec_ref(v_a_1595_);
lean_dec(v_a_1594_);
lean_dec_ref(v_a_1593_);
lean_dec(v_a_1592_);
lean_dec(v_a_1591_);
lean_dec(v_a_1590_);
return v_res_1602_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_satisfied(lean_object* v_c_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_){
_start:
{
lean_object* v_p_1616_; lean_object* v___x_1617_; 
v_p_1616_ = lean_ctor_get(v_c_1603_, 0);
lean_inc(v_p_1616_);
lean_dec_ref(v_c_1603_);
v___x_1617_ = l_Lean_Grind_Linarith_Poly_eval_x3f(v_p_1616_, v_a_1604_, v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_, v_a_1609_, v_a_1610_, v_a_1611_, v_a_1612_, v_a_1613_, v_a_1614_);
if (lean_obj_tag(v___x_1617_) == 0)
{
lean_object* v_a_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1637_; 
v_a_1618_ = lean_ctor_get(v___x_1617_, 0);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1617_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1620_ = v___x_1617_;
v_isShared_1621_ = v_isSharedCheck_1637_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_a_1618_);
lean_dec(v___x_1617_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1637_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
uint8_t v___y_1623_; 
if (lean_obj_tag(v_a_1618_) == 1)
{
lean_object* v_val_1629_; lean_object* v___x_1630_; uint8_t v___x_1631_; 
v_val_1629_ = lean_ctor_get(v_a_1618_, 0);
lean_inc(v_val_1629_);
lean_dec_ref_known(v_a_1618_, 1);
v___x_1630_ = lean_obj_once(&l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0, &l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0_once, _init_l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0);
v___x_1631_ = l_instDecidableEqRat_decEq(v_val_1629_, v___x_1630_);
lean_dec(v_val_1629_);
if (v___x_1631_ == 0)
{
uint8_t v___x_1632_; 
v___x_1632_ = 1;
v___y_1623_ = v___x_1632_;
goto v___jp_1622_;
}
else
{
uint8_t v___x_1633_; 
v___x_1633_ = 0;
v___y_1623_ = v___x_1633_;
goto v___jp_1622_;
}
}
else
{
uint8_t v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; 
lean_del_object(v___x_1620_);
lean_dec(v_a_1618_);
v___x_1634_ = 2;
v___x_1635_ = lean_box(v___x_1634_);
v___x_1636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1635_);
return v___x_1636_;
}
v___jp_1622_:
{
uint8_t v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1627_; 
v___x_1624_ = l_Lean_Bool_toLBool(v___y_1623_);
v___x_1625_ = lean_box(v___x_1624_);
if (v_isShared_1621_ == 0)
{
lean_ctor_set(v___x_1620_, 0, v___x_1625_);
v___x_1627_ = v___x_1620_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v___x_1625_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
}
}
}
}
else
{
lean_object* v_a_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1645_; 
v_a_1638_ = lean_ctor_get(v___x_1617_, 0);
v_isSharedCheck_1645_ = !lean_is_exclusive(v___x_1617_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1640_ = v___x_1617_;
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_a_1638_);
lean_dec(v___x_1617_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1643_; 
if (v_isShared_1641_ == 0)
{
v___x_1643_ = v___x_1640_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_a_1638_);
v___x_1643_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
return v___x_1643_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_satisfied_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_1603_ = stack[0].m_obj;
lean_object* v_a_1604_ = stack[1].m_obj;
lean_object* v_a_1605_ = stack[2].m_obj;
lean_object* v_a_1606_ = stack[3].m_obj;
lean_object* v_a_1607_ = stack[4].m_obj;
lean_object* v_a_1608_ = stack[5].m_obj;
lean_object* v_a_1609_ = stack[6].m_obj;
lean_object* v_a_1610_ = stack[7].m_obj;
lean_object* v_a_1611_ = stack[8].m_obj;
lean_object* v_a_1612_ = stack[9].m_obj;
lean_object* v_a_1613_ = stack[10].m_obj;
lean_object* v_a_1614_ = stack[11].m_obj;
lean_object* v_res_1646_;
v_res_1646_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_satisfied(v_c_1603_, v_a_1604_, v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_, v_a_1609_, v_a_1610_, v_a_1611_, v_a_1612_, v_a_1613_, v_a_1614_);
stack->m_obj
 = v_res_1646_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_satisfied___boxed(lean_object* v_c_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_){
_start:
{
lean_object* v_res_1660_; 
v_res_1660_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_satisfied(v_c_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_, v_a_1658_);
lean_dec(v_a_1658_);
lean_dec_ref(v_a_1657_);
lean_dec(v_a_1656_);
lean_dec_ref(v_a_1655_);
lean_dec(v_a_1654_);
lean_dec_ref(v_a_1653_);
lean_dec(v_a_1652_);
lean_dec_ref(v_a_1651_);
lean_dec(v_a_1650_);
lean_dec(v_a_1649_);
lean_dec(v_a_1648_);
return v_res_1660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg___lam__0(lean_object* v_a_1661_, lean_object* v_x_1662_, lean_object* v_s_1663_){
_start:
{
lean_object* v_structs_1664_; lean_object* v_typeIdOf_1665_; lean_object* v_exprToStructId_1666_; lean_object* v_exprToStructIdEntries_1667_; lean_object* v_forbiddenNatModules_1668_; lean_object* v_natStructs_1669_; lean_object* v_natTypeIdOf_1670_; lean_object* v_exprToNatStructId_1671_; lean_object* v___x_1672_; uint8_t v___x_1673_; 
v_structs_1664_ = lean_ctor_get(v_s_1663_, 0);
v_typeIdOf_1665_ = lean_ctor_get(v_s_1663_, 1);
v_exprToStructId_1666_ = lean_ctor_get(v_s_1663_, 2);
v_exprToStructIdEntries_1667_ = lean_ctor_get(v_s_1663_, 3);
v_forbiddenNatModules_1668_ = lean_ctor_get(v_s_1663_, 4);
v_natStructs_1669_ = lean_ctor_get(v_s_1663_, 5);
v_natTypeIdOf_1670_ = lean_ctor_get(v_s_1663_, 6);
v_exprToNatStructId_1671_ = lean_ctor_get(v_s_1663_, 7);
v___x_1672_ = lean_array_get_size(v_structs_1664_);
v___x_1673_ = lean_nat_dec_lt(v_a_1661_, v___x_1672_);
if (v___x_1673_ == 0)
{
return v_s_1663_;
}
else
{
lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1735_; 
lean_inc_ref(v_exprToNatStructId_1671_);
lean_inc_ref(v_natTypeIdOf_1670_);
lean_inc_ref(v_natStructs_1669_);
lean_inc_ref(v_forbiddenNatModules_1668_);
lean_inc_ref(v_exprToStructIdEntries_1667_);
lean_inc_ref(v_exprToStructId_1666_);
lean_inc_ref(v_typeIdOf_1665_);
lean_inc_ref(v_structs_1664_);
v_isSharedCheck_1735_ = !lean_is_exclusive(v_s_1663_);
if (v_isSharedCheck_1735_ == 0)
{
lean_object* v_unused_1736_; lean_object* v_unused_1737_; lean_object* v_unused_1738_; lean_object* v_unused_1739_; lean_object* v_unused_1740_; lean_object* v_unused_1741_; lean_object* v_unused_1742_; lean_object* v_unused_1743_; 
v_unused_1736_ = lean_ctor_get(v_s_1663_, 7);
lean_dec(v_unused_1736_);
v_unused_1737_ = lean_ctor_get(v_s_1663_, 6);
lean_dec(v_unused_1737_);
v_unused_1738_ = lean_ctor_get(v_s_1663_, 5);
lean_dec(v_unused_1738_);
v_unused_1739_ = lean_ctor_get(v_s_1663_, 4);
lean_dec(v_unused_1739_);
v_unused_1740_ = lean_ctor_get(v_s_1663_, 3);
lean_dec(v_unused_1740_);
v_unused_1741_ = lean_ctor_get(v_s_1663_, 2);
lean_dec(v_unused_1741_);
v_unused_1742_ = lean_ctor_get(v_s_1663_, 1);
lean_dec(v_unused_1742_);
v_unused_1743_ = lean_ctor_get(v_s_1663_, 0);
lean_dec(v_unused_1743_);
v___x_1675_ = v_s_1663_;
v_isShared_1676_ = v_isSharedCheck_1735_;
goto v_resetjp_1674_;
}
else
{
lean_dec(v_s_1663_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1735_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v_v_1677_; lean_object* v_id_1678_; lean_object* v_ringId_x3f_1679_; lean_object* v_type_1680_; lean_object* v_u_1681_; lean_object* v_intModuleInst_1682_; lean_object* v_leInst_x3f_1683_; lean_object* v_ltInst_x3f_1684_; lean_object* v_lawfulOrderLTInst_x3f_1685_; lean_object* v_isPreorderInst_x3f_1686_; lean_object* v_orderedAddInst_x3f_1687_; lean_object* v_isLinearInst_x3f_1688_; lean_object* v_noNatDivInst_x3f_1689_; lean_object* v_ringInst_x3f_1690_; lean_object* v_commRingInst_x3f_1691_; lean_object* v_orderedRingInst_x3f_1692_; lean_object* v_fieldInst_x3f_1693_; lean_object* v_charInst_x3f_1694_; lean_object* v_zero_1695_; lean_object* v_ofNatZero_1696_; lean_object* v_one_x3f_1697_; lean_object* v_leFn_x3f_1698_; lean_object* v_ltFn_x3f_1699_; lean_object* v_addFn_1700_; lean_object* v_zsmulFn_1701_; lean_object* v_nsmulFn_1702_; lean_object* v_zsmulFn_x3f_1703_; lean_object* v_nsmulFn_x3f_1704_; lean_object* v_homomulFn_x3f_1705_; lean_object* v_subFn_1706_; lean_object* v_negFn_1707_; lean_object* v_vars_1708_; lean_object* v_varMap_1709_; lean_object* v_lowers_1710_; lean_object* v_uppers_1711_; lean_object* v_diseqs_1712_; lean_object* v_assignment_1713_; uint8_t v_caseSplits_1714_; lean_object* v_conflict_x3f_1715_; lean_object* v_diseqSplits_1716_; lean_object* v_elimEqs_1717_; lean_object* v_elimStack_1718_; lean_object* v_occurs_1719_; lean_object* v_ignored_1720_; lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1734_; 
v_v_1677_ = lean_array_fget(v_structs_1664_, v_a_1661_);
v_id_1678_ = lean_ctor_get(v_v_1677_, 0);
v_ringId_x3f_1679_ = lean_ctor_get(v_v_1677_, 1);
v_type_1680_ = lean_ctor_get(v_v_1677_, 2);
v_u_1681_ = lean_ctor_get(v_v_1677_, 3);
v_intModuleInst_1682_ = lean_ctor_get(v_v_1677_, 4);
v_leInst_x3f_1683_ = lean_ctor_get(v_v_1677_, 5);
v_ltInst_x3f_1684_ = lean_ctor_get(v_v_1677_, 6);
v_lawfulOrderLTInst_x3f_1685_ = lean_ctor_get(v_v_1677_, 7);
v_isPreorderInst_x3f_1686_ = lean_ctor_get(v_v_1677_, 8);
v_orderedAddInst_x3f_1687_ = lean_ctor_get(v_v_1677_, 9);
v_isLinearInst_x3f_1688_ = lean_ctor_get(v_v_1677_, 10);
v_noNatDivInst_x3f_1689_ = lean_ctor_get(v_v_1677_, 11);
v_ringInst_x3f_1690_ = lean_ctor_get(v_v_1677_, 12);
v_commRingInst_x3f_1691_ = lean_ctor_get(v_v_1677_, 13);
v_orderedRingInst_x3f_1692_ = lean_ctor_get(v_v_1677_, 14);
v_fieldInst_x3f_1693_ = lean_ctor_get(v_v_1677_, 15);
v_charInst_x3f_1694_ = lean_ctor_get(v_v_1677_, 16);
v_zero_1695_ = lean_ctor_get(v_v_1677_, 17);
v_ofNatZero_1696_ = lean_ctor_get(v_v_1677_, 18);
v_one_x3f_1697_ = lean_ctor_get(v_v_1677_, 19);
v_leFn_x3f_1698_ = lean_ctor_get(v_v_1677_, 20);
v_ltFn_x3f_1699_ = lean_ctor_get(v_v_1677_, 21);
v_addFn_1700_ = lean_ctor_get(v_v_1677_, 22);
v_zsmulFn_1701_ = lean_ctor_get(v_v_1677_, 23);
v_nsmulFn_1702_ = lean_ctor_get(v_v_1677_, 24);
v_zsmulFn_x3f_1703_ = lean_ctor_get(v_v_1677_, 25);
v_nsmulFn_x3f_1704_ = lean_ctor_get(v_v_1677_, 26);
v_homomulFn_x3f_1705_ = lean_ctor_get(v_v_1677_, 27);
v_subFn_1706_ = lean_ctor_get(v_v_1677_, 28);
v_negFn_1707_ = lean_ctor_get(v_v_1677_, 29);
v_vars_1708_ = lean_ctor_get(v_v_1677_, 30);
v_varMap_1709_ = lean_ctor_get(v_v_1677_, 31);
v_lowers_1710_ = lean_ctor_get(v_v_1677_, 32);
v_uppers_1711_ = lean_ctor_get(v_v_1677_, 33);
v_diseqs_1712_ = lean_ctor_get(v_v_1677_, 34);
v_assignment_1713_ = lean_ctor_get(v_v_1677_, 35);
v_caseSplits_1714_ = lean_ctor_get_uint8(v_v_1677_, sizeof(void*)*42);
v_conflict_x3f_1715_ = lean_ctor_get(v_v_1677_, 36);
v_diseqSplits_1716_ = lean_ctor_get(v_v_1677_, 37);
v_elimEqs_1717_ = lean_ctor_get(v_v_1677_, 38);
v_elimStack_1718_ = lean_ctor_get(v_v_1677_, 39);
v_occurs_1719_ = lean_ctor_get(v_v_1677_, 40);
v_ignored_1720_ = lean_ctor_get(v_v_1677_, 41);
v_isSharedCheck_1734_ = !lean_is_exclusive(v_v_1677_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1722_ = v_v_1677_;
v_isShared_1723_ = v_isSharedCheck_1734_;
goto v_resetjp_1721_;
}
else
{
lean_inc(v_ignored_1720_);
lean_inc(v_occurs_1719_);
lean_inc(v_elimStack_1718_);
lean_inc(v_elimEqs_1717_);
lean_inc(v_diseqSplits_1716_);
lean_inc(v_conflict_x3f_1715_);
lean_inc(v_assignment_1713_);
lean_inc(v_diseqs_1712_);
lean_inc(v_uppers_1711_);
lean_inc(v_lowers_1710_);
lean_inc(v_varMap_1709_);
lean_inc(v_vars_1708_);
lean_inc(v_negFn_1707_);
lean_inc(v_subFn_1706_);
lean_inc(v_homomulFn_x3f_1705_);
lean_inc(v_nsmulFn_x3f_1704_);
lean_inc(v_zsmulFn_x3f_1703_);
lean_inc(v_nsmulFn_1702_);
lean_inc(v_zsmulFn_1701_);
lean_inc(v_addFn_1700_);
lean_inc(v_ltFn_x3f_1699_);
lean_inc(v_leFn_x3f_1698_);
lean_inc(v_one_x3f_1697_);
lean_inc(v_ofNatZero_1696_);
lean_inc(v_zero_1695_);
lean_inc(v_charInst_x3f_1694_);
lean_inc(v_fieldInst_x3f_1693_);
lean_inc(v_orderedRingInst_x3f_1692_);
lean_inc(v_commRingInst_x3f_1691_);
lean_inc(v_ringInst_x3f_1690_);
lean_inc(v_noNatDivInst_x3f_1689_);
lean_inc(v_isLinearInst_x3f_1688_);
lean_inc(v_orderedAddInst_x3f_1687_);
lean_inc(v_isPreorderInst_x3f_1686_);
lean_inc(v_lawfulOrderLTInst_x3f_1685_);
lean_inc(v_ltInst_x3f_1684_);
lean_inc(v_leInst_x3f_1683_);
lean_inc(v_intModuleInst_1682_);
lean_inc(v_u_1681_);
lean_inc(v_type_1680_);
lean_inc(v_ringId_x3f_1679_);
lean_inc(v_id_1678_);
lean_dec(v_v_1677_);
v___x_1722_ = lean_box(0);
v_isShared_1723_ = v_isSharedCheck_1734_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
lean_object* v___x_1724_; lean_object* v_xs_x27_1725_; lean_object* v___x_1726_; lean_object* v___x_1728_; 
v___x_1724_ = lean_box(0);
v_xs_x27_1725_ = lean_array_fset(v_structs_1664_, v_a_1661_, v___x_1724_);
v___x_1726_ = l_Lean_Meta_Grind_Arith_shrink(v_assignment_1713_, v_x_1662_);
if (v_isShared_1723_ == 0)
{
lean_ctor_set(v___x_1722_, 35, v___x_1726_);
v___x_1728_ = v___x_1722_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v_id_1678_);
lean_ctor_set(v_reuseFailAlloc_1733_, 1, v_ringId_x3f_1679_);
lean_ctor_set(v_reuseFailAlloc_1733_, 2, v_type_1680_);
lean_ctor_set(v_reuseFailAlloc_1733_, 3, v_u_1681_);
lean_ctor_set(v_reuseFailAlloc_1733_, 4, v_intModuleInst_1682_);
lean_ctor_set(v_reuseFailAlloc_1733_, 5, v_leInst_x3f_1683_);
lean_ctor_set(v_reuseFailAlloc_1733_, 6, v_ltInst_x3f_1684_);
lean_ctor_set(v_reuseFailAlloc_1733_, 7, v_lawfulOrderLTInst_x3f_1685_);
lean_ctor_set(v_reuseFailAlloc_1733_, 8, v_isPreorderInst_x3f_1686_);
lean_ctor_set(v_reuseFailAlloc_1733_, 9, v_orderedAddInst_x3f_1687_);
lean_ctor_set(v_reuseFailAlloc_1733_, 10, v_isLinearInst_x3f_1688_);
lean_ctor_set(v_reuseFailAlloc_1733_, 11, v_noNatDivInst_x3f_1689_);
lean_ctor_set(v_reuseFailAlloc_1733_, 12, v_ringInst_x3f_1690_);
lean_ctor_set(v_reuseFailAlloc_1733_, 13, v_commRingInst_x3f_1691_);
lean_ctor_set(v_reuseFailAlloc_1733_, 14, v_orderedRingInst_x3f_1692_);
lean_ctor_set(v_reuseFailAlloc_1733_, 15, v_fieldInst_x3f_1693_);
lean_ctor_set(v_reuseFailAlloc_1733_, 16, v_charInst_x3f_1694_);
lean_ctor_set(v_reuseFailAlloc_1733_, 17, v_zero_1695_);
lean_ctor_set(v_reuseFailAlloc_1733_, 18, v_ofNatZero_1696_);
lean_ctor_set(v_reuseFailAlloc_1733_, 19, v_one_x3f_1697_);
lean_ctor_set(v_reuseFailAlloc_1733_, 20, v_leFn_x3f_1698_);
lean_ctor_set(v_reuseFailAlloc_1733_, 21, v_ltFn_x3f_1699_);
lean_ctor_set(v_reuseFailAlloc_1733_, 22, v_addFn_1700_);
lean_ctor_set(v_reuseFailAlloc_1733_, 23, v_zsmulFn_1701_);
lean_ctor_set(v_reuseFailAlloc_1733_, 24, v_nsmulFn_1702_);
lean_ctor_set(v_reuseFailAlloc_1733_, 25, v_zsmulFn_x3f_1703_);
lean_ctor_set(v_reuseFailAlloc_1733_, 26, v_nsmulFn_x3f_1704_);
lean_ctor_set(v_reuseFailAlloc_1733_, 27, v_homomulFn_x3f_1705_);
lean_ctor_set(v_reuseFailAlloc_1733_, 28, v_subFn_1706_);
lean_ctor_set(v_reuseFailAlloc_1733_, 29, v_negFn_1707_);
lean_ctor_set(v_reuseFailAlloc_1733_, 30, v_vars_1708_);
lean_ctor_set(v_reuseFailAlloc_1733_, 31, v_varMap_1709_);
lean_ctor_set(v_reuseFailAlloc_1733_, 32, v_lowers_1710_);
lean_ctor_set(v_reuseFailAlloc_1733_, 33, v_uppers_1711_);
lean_ctor_set(v_reuseFailAlloc_1733_, 34, v_diseqs_1712_);
lean_ctor_set(v_reuseFailAlloc_1733_, 35, v___x_1726_);
lean_ctor_set(v_reuseFailAlloc_1733_, 36, v_conflict_x3f_1715_);
lean_ctor_set(v_reuseFailAlloc_1733_, 37, v_diseqSplits_1716_);
lean_ctor_set(v_reuseFailAlloc_1733_, 38, v_elimEqs_1717_);
lean_ctor_set(v_reuseFailAlloc_1733_, 39, v_elimStack_1718_);
lean_ctor_set(v_reuseFailAlloc_1733_, 40, v_occurs_1719_);
lean_ctor_set(v_reuseFailAlloc_1733_, 41, v_ignored_1720_);
lean_ctor_set_uint8(v_reuseFailAlloc_1733_, sizeof(void*)*42, v_caseSplits_1714_);
v___x_1728_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
lean_object* v___x_1729_; lean_object* v___x_1731_; 
v___x_1729_ = lean_array_fset(v_xs_x27_1725_, v_a_1661_, v___x_1728_);
if (v_isShared_1676_ == 0)
{
lean_ctor_set(v___x_1675_, 0, v___x_1729_);
v___x_1731_ = v___x_1675_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v___x_1729_);
lean_ctor_set(v_reuseFailAlloc_1732_, 1, v_typeIdOf_1665_);
lean_ctor_set(v_reuseFailAlloc_1732_, 2, v_exprToStructId_1666_);
lean_ctor_set(v_reuseFailAlloc_1732_, 3, v_exprToStructIdEntries_1667_);
lean_ctor_set(v_reuseFailAlloc_1732_, 4, v_forbiddenNatModules_1668_);
lean_ctor_set(v_reuseFailAlloc_1732_, 5, v_natStructs_1669_);
lean_ctor_set(v_reuseFailAlloc_1732_, 6, v_natTypeIdOf_1670_);
lean_ctor_set(v_reuseFailAlloc_1732_, 7, v_exprToNatStructId_1671_);
v___x_1731_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
return v___x_1731_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg___lam__0___boxed(lean_object* v_a_1744_, lean_object* v_x_1745_, lean_object* v_s_1746_){
_start:
{
lean_object* v_res_1747_; 
v_res_1747_ = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg___lam__0(v_a_1744_, v_x_1745_, v_s_1746_);
lean_dec(v_x_1745_);
lean_dec(v_a_1744_);
return v_res_1747_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg(lean_object* v_x_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_){
_start:
{
lean_object* v___f_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; 
lean_inc(v_a_1749_);
v___f_1752_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1752_, 0, v_a_1749_);
lean_closure_set(v___f_1752_, 1, v_x_1748_);
v___x_1753_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_1754_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1753_, v___f_1752_, v_a_1750_);
return v___x_1754_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1748_ = stack[0].m_obj;
lean_object* v_a_1749_ = stack[1].m_obj;
lean_object* v_a_1750_ = stack[2].m_obj;
lean_object* v_res_1755_;
v_res_1755_ = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg(v_x_1748_, v_a_1749_, v_a_1750_);
stack->m_obj
 = v_res_1755_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg___boxed(lean_object* v_x_1756_, lean_object* v_a_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_){
_start:
{
lean_object* v_res_1760_; 
v_res_1760_ = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg(v_x_1756_, v_a_1757_, v_a_1758_);
lean_dec(v_a_1758_);
lean_dec(v_a_1757_);
return v_res_1760_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom(lean_object* v_x_1761_, lean_object* v_a_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_){
_start:
{
lean_object* v___x_1774_; 
v___x_1774_ = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg(v_x_1761_, v_a_1762_, v_a_1763_);
return v___x_1774_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1761_ = stack[0].m_obj;
lean_object* v_a_1762_ = stack[1].m_obj;
lean_object* v_a_1763_ = stack[2].m_obj;
lean_object* v_a_1764_ = stack[3].m_obj;
lean_object* v_a_1765_ = stack[4].m_obj;
lean_object* v_a_1766_ = stack[5].m_obj;
lean_object* v_a_1767_ = stack[6].m_obj;
lean_object* v_a_1768_ = stack[7].m_obj;
lean_object* v_a_1769_ = stack[8].m_obj;
lean_object* v_a_1770_ = stack[9].m_obj;
lean_object* v_a_1771_ = stack[10].m_obj;
lean_object* v_a_1772_ = stack[11].m_obj;
lean_object* v_res_1775_;
v_res_1775_ = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom(v_x_1761_, v_a_1762_, v_a_1763_, v_a_1764_, v_a_1765_, v_a_1766_, v_a_1767_, v_a_1768_, v_a_1769_, v_a_1770_, v_a_1771_, v_a_1772_);
stack->m_obj
 = v_res_1775_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___boxed(lean_object* v_x_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_){
_start:
{
lean_object* v_res_1789_; 
v_res_1789_ = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom(v_x_1776_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_);
lean_dec(v_a_1787_);
lean_dec_ref(v_a_1786_);
lean_dec(v_a_1785_);
lean_dec_ref(v_a_1784_);
lean_dec(v_a_1783_);
lean_dec_ref(v_a_1782_);
lean_dec(v_a_1781_);
lean_dec_ref(v_a_1780_);
lean_dec(v_a_1779_);
lean_dec(v_a_1778_);
lean_dec(v_a_1777_);
return v_res_1789_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_getVar(lean_object* v_x_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_){
_start:
{
lean_object* v___x_1803_; lean_object* v___x_1804_; 
v___x_1803_ = l_Lean_instInhabitedExpr;
v___x_1804_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1791_, v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_);
if (lean_obj_tag(v___x_1804_) == 0)
{
lean_object* v_a_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1820_; 
v_a_1805_ = lean_ctor_get(v___x_1804_, 0);
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1804_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1807_ = v___x_1804_;
v_isShared_1808_ = v_isSharedCheck_1820_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_a_1805_);
lean_dec(v___x_1804_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1820_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
lean_object* v_vars_1809_; lean_object* v_size_1810_; uint8_t v___x_1811_; 
v_vars_1809_ = lean_ctor_get(v_a_1805_, 30);
lean_inc_ref(v_vars_1809_);
lean_dec(v_a_1805_);
v_size_1810_ = lean_ctor_get(v_vars_1809_, 2);
v___x_1811_ = lean_nat_dec_lt(v_x_1790_, v_size_1810_);
if (v___x_1811_ == 0)
{
lean_object* v___x_1812_; lean_object* v___x_1814_; 
lean_dec_ref(v_vars_1809_);
v___x_1812_ = l_outOfBounds___redArg(v___x_1803_);
if (v_isShared_1808_ == 0)
{
lean_ctor_set(v___x_1807_, 0, v___x_1812_);
v___x_1814_ = v___x_1807_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v___x_1812_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
return v___x_1814_;
}
}
else
{
lean_object* v___x_1816_; lean_object* v___x_1818_; 
v___x_1816_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1803_, v_vars_1809_, v_x_1790_);
lean_dec_ref(v_vars_1809_);
if (v_isShared_1808_ == 0)
{
lean_ctor_set(v___x_1807_, 0, v___x_1816_);
v___x_1818_ = v___x_1807_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v___x_1816_);
v___x_1818_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
return v___x_1818_;
}
}
}
}
else
{
lean_object* v_a_1821_; lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1828_; 
v_a_1821_ = lean_ctor_get(v___x_1804_, 0);
v_isSharedCheck_1828_ = !lean_is_exclusive(v___x_1804_);
if (v_isSharedCheck_1828_ == 0)
{
v___x_1823_ = v___x_1804_;
v_isShared_1824_ = v_isSharedCheck_1828_;
goto v_resetjp_1822_;
}
else
{
lean_inc(v_a_1821_);
lean_dec(v___x_1804_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1828_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
lean_object* v___x_1826_; 
if (v_isShared_1824_ == 0)
{
v___x_1826_ = v___x_1823_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_a_1821_);
v___x_1826_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
return v___x_1826_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_getVar_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1790_ = stack[0].m_obj;
lean_object* v_a_1791_ = stack[1].m_obj;
lean_object* v_a_1792_ = stack[2].m_obj;
lean_object* v_a_1793_ = stack[3].m_obj;
lean_object* v_a_1794_ = stack[4].m_obj;
lean_object* v_a_1795_ = stack[5].m_obj;
lean_object* v_a_1796_ = stack[6].m_obj;
lean_object* v_a_1797_ = stack[7].m_obj;
lean_object* v_a_1798_ = stack[8].m_obj;
lean_object* v_a_1799_ = stack[9].m_obj;
lean_object* v_a_1800_ = stack[10].m_obj;
lean_object* v_a_1801_ = stack[11].m_obj;
lean_object* v_res_1829_;
v_res_1829_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_x_1790_, v_a_1791_, v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_);
stack->m_obj
 = v_res_1829_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getVar___boxed(lean_object* v_x_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_){
_start:
{
lean_object* v_res_1843_; 
v_res_1843_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_x_1830_, v_a_1831_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_);
lean_dec(v_a_1841_);
lean_dec_ref(v_a_1840_);
lean_dec(v_a_1839_);
lean_dec_ref(v_a_1838_);
lean_dec(v_a_1837_);
lean_dec_ref(v_a_1836_);
lean_dec(v_a_1835_);
lean_dec_ref(v_a_1834_);
lean_dec(v_a_1833_);
lean_dec(v_a_1832_);
lean_dec(v_a_1831_);
lean_dec(v_x_1830_);
return v_res_1843_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_inconsistent(lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_){
_start:
{
lean_object* v___x_1856_; 
v___x_1856_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_1845_);
if (lean_obj_tag(v___x_1856_) == 0)
{
lean_object* v_a_1857_; uint8_t v___x_1858_; 
v_a_1857_ = lean_ctor_get(v___x_1856_, 0);
v___x_1858_ = lean_unbox(v_a_1857_);
if (v___x_1858_ == 0)
{
lean_object* v___x_1859_; 
lean_inc(v_a_1857_);
lean_dec_ref_known(v___x_1856_, 1);
v___x_1859_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1844_, v_a_1845_, v_a_1846_, v_a_1847_, v_a_1848_, v_a_1849_, v_a_1850_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_);
if (lean_obj_tag(v___x_1859_) == 0)
{
lean_object* v_a_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1873_; 
v_a_1860_ = lean_ctor_get(v___x_1859_, 0);
v_isSharedCheck_1873_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1862_ = v___x_1859_;
v_isShared_1863_ = v_isSharedCheck_1873_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_a_1860_);
lean_dec(v___x_1859_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1873_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
lean_object* v_conflict_x3f_1864_; 
v_conflict_x3f_1864_ = lean_ctor_get(v_a_1860_, 36);
lean_inc(v_conflict_x3f_1864_);
lean_dec(v_a_1860_);
if (lean_obj_tag(v_conflict_x3f_1864_) == 0)
{
lean_object* v___x_1866_; 
if (v_isShared_1863_ == 0)
{
lean_ctor_set(v___x_1862_, 0, v_a_1857_);
v___x_1866_ = v___x_1862_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v_a_1857_);
v___x_1866_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
return v___x_1866_;
}
}
else
{
uint8_t v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1871_; 
lean_dec_ref_known(v_conflict_x3f_1864_, 1);
lean_dec(v_a_1857_);
v___x_1868_ = 1;
v___x_1869_ = lean_box(v___x_1868_);
if (v_isShared_1863_ == 0)
{
lean_ctor_set(v___x_1862_, 0, v___x_1869_);
v___x_1871_ = v___x_1862_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v___x_1869_);
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
else
{
lean_object* v_a_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1881_; 
lean_dec(v_a_1857_);
v_a_1874_ = lean_ctor_get(v___x_1859_, 0);
v_isSharedCheck_1881_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1876_ = v___x_1859_;
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_a_1874_);
lean_dec(v___x_1859_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1879_; 
if (v_isShared_1877_ == 0)
{
v___x_1879_ = v___x_1876_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_a_1874_);
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
return v___x_1856_;
}
}
else
{
return v___x_1856_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_inconsistent_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1844_ = stack[0].m_obj;
lean_object* v_a_1845_ = stack[1].m_obj;
lean_object* v_a_1846_ = stack[2].m_obj;
lean_object* v_a_1847_ = stack[3].m_obj;
lean_object* v_a_1848_ = stack[4].m_obj;
lean_object* v_a_1849_ = stack[5].m_obj;
lean_object* v_a_1850_ = stack[6].m_obj;
lean_object* v_a_1851_ = stack[7].m_obj;
lean_object* v_a_1852_ = stack[8].m_obj;
lean_object* v_a_1853_ = stack[9].m_obj;
lean_object* v_a_1854_ = stack[10].m_obj;
lean_object* v_res_1882_;
v_res_1882_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v_a_1844_, v_a_1845_, v_a_1846_, v_a_1847_, v_a_1848_, v_a_1849_, v_a_1850_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_);
stack->m_obj
 = v_res_1882_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_inconsistent___boxed(lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_){
_start:
{
lean_object* v_res_1895_; 
v_res_1895_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_);
lean_dec(v_a_1893_);
lean_dec_ref(v_a_1892_);
lean_dec(v_a_1891_);
lean_dec_ref(v_a_1890_);
lean_dec(v_a_1889_);
lean_dec_ref(v_a_1888_);
lean_dec(v_a_1887_);
lean_dec_ref(v_a_1886_);
lean_dec(v_a_1885_);
lean_dec(v_a_1884_);
lean_dec(v_a_1883_);
return v_res_1895_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_eliminated(lean_object* v_x_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_){
_start:
{
lean_object* v___x_1909_; lean_object* v___x_1910_; 
v___x_1909_ = lean_box(0);
v___x_1910_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_);
if (lean_obj_tag(v___x_1910_) == 0)
{
lean_object* v_a_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1932_; 
v_a_1911_ = lean_ctor_get(v___x_1910_, 0);
v_isSharedCheck_1932_ = !lean_is_exclusive(v___x_1910_);
if (v_isSharedCheck_1932_ == 0)
{
v___x_1913_ = v___x_1910_;
v_isShared_1914_ = v_isSharedCheck_1932_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_a_1911_);
lean_dec(v___x_1910_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1932_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v___y_1916_; lean_object* v_elimEqs_1927_; lean_object* v_size_1928_; uint8_t v___x_1929_; 
v_elimEqs_1927_ = lean_ctor_get(v_a_1911_, 38);
lean_inc_ref(v_elimEqs_1927_);
lean_dec(v_a_1911_);
v_size_1928_ = lean_ctor_get(v_elimEqs_1927_, 2);
v___x_1929_ = lean_nat_dec_lt(v_x_1896_, v_size_1928_);
if (v___x_1929_ == 0)
{
lean_object* v___x_1930_; 
lean_dec_ref(v_elimEqs_1927_);
v___x_1930_ = l_outOfBounds___redArg(v___x_1909_);
v___y_1916_ = v___x_1930_;
goto v___jp_1915_;
}
else
{
lean_object* v___x_1931_; 
v___x_1931_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1909_, v_elimEqs_1927_, v_x_1896_);
lean_dec_ref(v_elimEqs_1927_);
v___y_1916_ = v___x_1931_;
goto v___jp_1915_;
}
v___jp_1915_:
{
if (lean_obj_tag(v___y_1916_) == 0)
{
uint8_t v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1920_; 
v___x_1917_ = 0;
v___x_1918_ = lean_box(v___x_1917_);
if (v_isShared_1914_ == 0)
{
lean_ctor_set(v___x_1913_, 0, v___x_1918_);
v___x_1920_ = v___x_1913_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v___x_1918_);
v___x_1920_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
return v___x_1920_;
}
}
else
{
uint8_t v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1925_; 
lean_dec_ref_known(v___y_1916_, 1);
v___x_1922_ = 1;
v___x_1923_ = lean_box(v___x_1922_);
if (v_isShared_1914_ == 0)
{
lean_ctor_set(v___x_1913_, 0, v___x_1923_);
v___x_1925_ = v___x_1913_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v___x_1923_);
v___x_1925_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
return v___x_1925_;
}
}
}
}
}
else
{
lean_object* v_a_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1940_; 
v_a_1933_ = lean_ctor_get(v___x_1910_, 0);
v_isSharedCheck_1940_ = !lean_is_exclusive(v___x_1910_);
if (v_isSharedCheck_1940_ == 0)
{
v___x_1935_ = v___x_1910_;
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_a_1933_);
lean_dec(v___x_1910_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v___x_1938_; 
if (v_isShared_1936_ == 0)
{
v___x_1938_ = v___x_1935_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_a_1933_);
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
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_eliminated_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1896_ = stack[0].m_obj;
lean_object* v_a_1897_ = stack[1].m_obj;
lean_object* v_a_1898_ = stack[2].m_obj;
lean_object* v_a_1899_ = stack[3].m_obj;
lean_object* v_a_1900_ = stack[4].m_obj;
lean_object* v_a_1901_ = stack[5].m_obj;
lean_object* v_a_1902_ = stack[6].m_obj;
lean_object* v_a_1903_ = stack[7].m_obj;
lean_object* v_a_1904_ = stack[8].m_obj;
lean_object* v_a_1905_ = stack[9].m_obj;
lean_object* v_a_1906_ = stack[10].m_obj;
lean_object* v_a_1907_ = stack[11].m_obj;
lean_object* v_res_1941_;
v_res_1941_ = l_Lean_Meta_Grind_Arith_Linear_eliminated(v_x_1896_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_);
stack->m_obj
 = v_res_1941_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_eliminated___boxed(lean_object* v_x_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_){
_start:
{
lean_object* v_res_1955_; 
v_res_1955_ = l_Lean_Meta_Grind_Arith_Linear_eliminated(v_x_1942_, v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_, v_a_1947_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_);
lean_dec(v_a_1953_);
lean_dec_ref(v_a_1952_);
lean_dec(v_a_1951_);
lean_dec_ref(v_a_1950_);
lean_dec(v_a_1949_);
lean_dec_ref(v_a_1948_);
lean_dec(v_a_1947_);
lean_dec_ref(v_a_1946_);
lean_dec(v_a_1945_);
lean_dec(v_a_1944_);
lean_dec(v_a_1943_);
lean_dec(v_x_1942_);
return v_res_1955_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_getOccursOf(lean_object* v_x_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_){
_start:
{
lean_object* v___x_1969_; 
v___x_1969_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1957_, v_a_1958_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_, v_a_1966_, v_a_1967_);
if (lean_obj_tag(v___x_1969_) == 0)
{
lean_object* v_a_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1986_; 
v_a_1970_ = lean_ctor_get(v___x_1969_, 0);
v_isSharedCheck_1986_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_1986_ == 0)
{
v___x_1972_ = v___x_1969_;
v_isShared_1973_ = v_isSharedCheck_1986_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_a_1970_);
lean_dec(v___x_1969_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1986_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v_occurs_1974_; lean_object* v_size_1975_; lean_object* v___x_1976_; uint8_t v___x_1977_; 
v_occurs_1974_ = lean_ctor_get(v_a_1970_, 40);
lean_inc_ref(v_occurs_1974_);
lean_dec(v_a_1970_);
v_size_1975_ = lean_ctor_get(v_occurs_1974_, 2);
v___x_1976_ = lean_box(1);
v___x_1977_ = lean_nat_dec_lt(v_x_1956_, v_size_1975_);
if (v___x_1977_ == 0)
{
lean_object* v___x_1978_; lean_object* v___x_1980_; 
lean_dec_ref(v_occurs_1974_);
v___x_1978_ = l_outOfBounds___redArg(v___x_1976_);
if (v_isShared_1973_ == 0)
{
lean_ctor_set(v___x_1972_, 0, v___x_1978_);
v___x_1980_ = v___x_1972_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v___x_1978_);
v___x_1980_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
return v___x_1980_;
}
}
else
{
lean_object* v___x_1982_; lean_object* v___x_1984_; 
v___x_1982_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1976_, v_occurs_1974_, v_x_1956_);
lean_dec_ref(v_occurs_1974_);
if (v_isShared_1973_ == 0)
{
lean_ctor_set(v___x_1972_, 0, v___x_1982_);
v___x_1984_ = v___x_1972_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v___x_1982_);
v___x_1984_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
return v___x_1984_;
}
}
}
}
else
{
lean_object* v_a_1987_; lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_1994_; 
v_a_1987_ = lean_ctor_get(v___x_1969_, 0);
v_isSharedCheck_1994_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_1994_ == 0)
{
v___x_1989_ = v___x_1969_;
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
else
{
lean_inc(v_a_1987_);
lean_dec(v___x_1969_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
lean_object* v___x_1992_; 
if (v_isShared_1990_ == 0)
{
v___x_1992_ = v___x_1989_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v_a_1987_);
v___x_1992_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
return v___x_1992_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_getOccursOf_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1956_ = stack[0].m_obj;
lean_object* v_a_1957_ = stack[1].m_obj;
lean_object* v_a_1958_ = stack[2].m_obj;
lean_object* v_a_1959_ = stack[3].m_obj;
lean_object* v_a_1960_ = stack[4].m_obj;
lean_object* v_a_1961_ = stack[5].m_obj;
lean_object* v_a_1962_ = stack[6].m_obj;
lean_object* v_a_1963_ = stack[7].m_obj;
lean_object* v_a_1964_ = stack[8].m_obj;
lean_object* v_a_1965_ = stack[9].m_obj;
lean_object* v_a_1966_ = stack[10].m_obj;
lean_object* v_a_1967_ = stack[11].m_obj;
lean_object* v_res_1995_;
v_res_1995_ = l_Lean_Meta_Grind_Arith_Linear_getOccursOf(v_x_1956_, v_a_1957_, v_a_1958_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_, v_a_1966_, v_a_1967_);
stack->m_obj
 = v_res_1995_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOccursOf___boxed(lean_object* v_x_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_){
_start:
{
lean_object* v_res_2009_; 
v_res_2009_ = l_Lean_Meta_Grind_Arith_Linear_getOccursOf(v_x_1996_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_);
lean_dec(v_a_2007_);
lean_dec_ref(v_a_2006_);
lean_dec(v_a_2005_);
lean_dec_ref(v_a_2004_);
lean_dec(v_a_2003_);
lean_dec_ref(v_a_2002_);
lean_dec(v_a_2001_);
lean_dec_ref(v_a_2000_);
lean_dec(v_a_1999_);
lean_dec(v_a_1998_);
lean_dec(v_a_1997_);
lean_dec(v_x_1996_);
return v_res_2009_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg(lean_object* v_k_2010_, lean_object* v_t_2011_){
_start:
{
if (lean_obj_tag(v_t_2011_) == 0)
{
lean_object* v_k_2012_; lean_object* v_l_2013_; lean_object* v_r_2014_; uint8_t v___x_2015_; 
v_k_2012_ = lean_ctor_get(v_t_2011_, 1);
v_l_2013_ = lean_ctor_get(v_t_2011_, 3);
v_r_2014_ = lean_ctor_get(v_t_2011_, 4);
v___x_2015_ = lean_nat_dec_lt(v_k_2010_, v_k_2012_);
if (v___x_2015_ == 0)
{
uint8_t v___x_2016_; 
v___x_2016_ = lean_nat_dec_eq(v_k_2010_, v_k_2012_);
if (v___x_2016_ == 0)
{
v_t_2011_ = v_r_2014_;
goto _start;
}
else
{
return v___x_2016_;
}
}
else
{
v_t_2011_ = v_l_2013_;
goto _start;
}
}
else
{
uint8_t v___x_2019_; 
v___x_2019_ = 0;
return v___x_2019_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_2010_ = stack[0].m_obj;
lean_object* v_t_2011_ = stack[1].m_obj;
uint8_t v_res_2020_;
v_res_2020_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg(v_k_2010_, v_t_2011_);
stack->m_num = v_res_2020_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg___boxed(lean_object* v_k_2021_, lean_object* v_t_2022_){
_start:
{
uint8_t v_res_2023_; lean_object* v_r_2024_; 
v_res_2023_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg(v_k_2021_, v_t_2022_);
lean_dec(v_t_2022_);
lean_dec(v_k_2021_);
v_r_2024_ = lean_box(v_res_2023_);
return v_r_2024_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1___redArg(lean_object* v_k_2025_, lean_object* v_v_2026_, lean_object* v_t_2027_){
_start:
{
if (lean_obj_tag(v_t_2027_) == 0)
{
lean_object* v_size_2028_; lean_object* v_k_2029_; lean_object* v_v_2030_; lean_object* v_l_2031_; lean_object* v_r_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2313_; 
v_size_2028_ = lean_ctor_get(v_t_2027_, 0);
v_k_2029_ = lean_ctor_get(v_t_2027_, 1);
v_v_2030_ = lean_ctor_get(v_t_2027_, 2);
v_l_2031_ = lean_ctor_get(v_t_2027_, 3);
v_r_2032_ = lean_ctor_get(v_t_2027_, 4);
v_isSharedCheck_2313_ = !lean_is_exclusive(v_t_2027_);
if (v_isSharedCheck_2313_ == 0)
{
v___x_2034_ = v_t_2027_;
v_isShared_2035_ = v_isSharedCheck_2313_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_r_2032_);
lean_inc(v_l_2031_);
lean_inc(v_v_2030_);
lean_inc(v_k_2029_);
lean_inc(v_size_2028_);
lean_dec(v_t_2027_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2313_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
uint8_t v___x_2036_; 
v___x_2036_ = lean_nat_dec_lt(v_k_2025_, v_k_2029_);
if (v___x_2036_ == 0)
{
uint8_t v___x_2037_; 
v___x_2037_ = lean_nat_dec_eq(v_k_2025_, v_k_2029_);
if (v___x_2037_ == 0)
{
lean_object* v_impl_2038_; lean_object* v___x_2039_; 
lean_dec(v_size_2028_);
v_impl_2038_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1___redArg(v_k_2025_, v_v_2026_, v_r_2032_);
v___x_2039_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_2031_) == 0)
{
lean_object* v_size_2040_; lean_object* v_size_2041_; lean_object* v_k_2042_; lean_object* v_v_2043_; lean_object* v_l_2044_; lean_object* v_r_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; uint8_t v___x_2048_; 
v_size_2040_ = lean_ctor_get(v_l_2031_, 0);
v_size_2041_ = lean_ctor_get(v_impl_2038_, 0);
v_k_2042_ = lean_ctor_get(v_impl_2038_, 1);
v_v_2043_ = lean_ctor_get(v_impl_2038_, 2);
v_l_2044_ = lean_ctor_get(v_impl_2038_, 3);
lean_inc(v_l_2044_);
v_r_2045_ = lean_ctor_get(v_impl_2038_, 4);
v___x_2046_ = lean_unsigned_to_nat(3u);
v___x_2047_ = lean_nat_mul(v___x_2046_, v_size_2040_);
v___x_2048_ = lean_nat_dec_lt(v___x_2047_, v_size_2041_);
lean_dec(v___x_2047_);
if (v___x_2048_ == 0)
{
lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2052_; 
lean_dec(v_l_2044_);
v___x_2049_ = lean_nat_add(v___x_2039_, v_size_2040_);
v___x_2050_ = lean_nat_add(v___x_2049_, v_size_2041_);
lean_dec(v___x_2049_);
if (v_isShared_2035_ == 0)
{
lean_ctor_set(v___x_2034_, 4, v_impl_2038_);
lean_ctor_set(v___x_2034_, 0, v___x_2050_);
v___x_2052_ = v___x_2034_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v___x_2050_);
lean_ctor_set(v_reuseFailAlloc_2053_, 1, v_k_2029_);
lean_ctor_set(v_reuseFailAlloc_2053_, 2, v_v_2030_);
lean_ctor_set(v_reuseFailAlloc_2053_, 3, v_l_2031_);
lean_ctor_set(v_reuseFailAlloc_2053_, 4, v_impl_2038_);
v___x_2052_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
return v___x_2052_;
}
}
else
{
lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2117_; 
lean_inc(v_r_2045_);
lean_inc(v_v_2043_);
lean_inc(v_k_2042_);
lean_inc(v_size_2041_);
v_isSharedCheck_2117_ = !lean_is_exclusive(v_impl_2038_);
if (v_isSharedCheck_2117_ == 0)
{
lean_object* v_unused_2118_; lean_object* v_unused_2119_; lean_object* v_unused_2120_; lean_object* v_unused_2121_; lean_object* v_unused_2122_; 
v_unused_2118_ = lean_ctor_get(v_impl_2038_, 4);
lean_dec(v_unused_2118_);
v_unused_2119_ = lean_ctor_get(v_impl_2038_, 3);
lean_dec(v_unused_2119_);
v_unused_2120_ = lean_ctor_get(v_impl_2038_, 2);
lean_dec(v_unused_2120_);
v_unused_2121_ = lean_ctor_get(v_impl_2038_, 1);
lean_dec(v_unused_2121_);
v_unused_2122_ = lean_ctor_get(v_impl_2038_, 0);
lean_dec(v_unused_2122_);
v___x_2055_ = v_impl_2038_;
v_isShared_2056_ = v_isSharedCheck_2117_;
goto v_resetjp_2054_;
}
else
{
lean_dec(v_impl_2038_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2117_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
lean_object* v_size_2057_; lean_object* v_k_2058_; lean_object* v_v_2059_; lean_object* v_l_2060_; lean_object* v_r_2061_; lean_object* v_size_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; uint8_t v___x_2065_; 
v_size_2057_ = lean_ctor_get(v_l_2044_, 0);
v_k_2058_ = lean_ctor_get(v_l_2044_, 1);
v_v_2059_ = lean_ctor_get(v_l_2044_, 2);
v_l_2060_ = lean_ctor_get(v_l_2044_, 3);
v_r_2061_ = lean_ctor_get(v_l_2044_, 4);
v_size_2062_ = lean_ctor_get(v_r_2045_, 0);
v___x_2063_ = lean_unsigned_to_nat(2u);
v___x_2064_ = lean_nat_mul(v___x_2063_, v_size_2062_);
v___x_2065_ = lean_nat_dec_lt(v_size_2057_, v___x_2064_);
lean_dec(v___x_2064_);
if (v___x_2065_ == 0)
{
lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2093_; 
lean_inc(v_r_2061_);
lean_inc(v_l_2060_);
lean_inc(v_v_2059_);
lean_inc(v_k_2058_);
v_isSharedCheck_2093_ = !lean_is_exclusive(v_l_2044_);
if (v_isSharedCheck_2093_ == 0)
{
lean_object* v_unused_2094_; lean_object* v_unused_2095_; lean_object* v_unused_2096_; lean_object* v_unused_2097_; lean_object* v_unused_2098_; 
v_unused_2094_ = lean_ctor_get(v_l_2044_, 4);
lean_dec(v_unused_2094_);
v_unused_2095_ = lean_ctor_get(v_l_2044_, 3);
lean_dec(v_unused_2095_);
v_unused_2096_ = lean_ctor_get(v_l_2044_, 2);
lean_dec(v_unused_2096_);
v_unused_2097_ = lean_ctor_get(v_l_2044_, 1);
lean_dec(v_unused_2097_);
v_unused_2098_ = lean_ctor_get(v_l_2044_, 0);
lean_dec(v_unused_2098_);
v___x_2067_ = v_l_2044_;
v_isShared_2068_ = v_isSharedCheck_2093_;
goto v_resetjp_2066_;
}
else
{
lean_dec(v_l_2044_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2093_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___y_2072_; lean_object* v___y_2073_; lean_object* v___y_2074_; lean_object* v___y_2083_; 
v___x_2069_ = lean_nat_add(v___x_2039_, v_size_2040_);
v___x_2070_ = lean_nat_add(v___x_2069_, v_size_2041_);
lean_dec(v_size_2041_);
if (lean_obj_tag(v_l_2060_) == 0)
{
lean_object* v_size_2091_; 
v_size_2091_ = lean_ctor_get(v_l_2060_, 0);
lean_inc(v_size_2091_);
v___y_2083_ = v_size_2091_;
goto v___jp_2082_;
}
else
{
lean_object* v___x_2092_; 
v___x_2092_ = lean_unsigned_to_nat(0u);
v___y_2083_ = v___x_2092_;
goto v___jp_2082_;
}
v___jp_2071_:
{
lean_object* v___x_2075_; lean_object* v___x_2077_; 
v___x_2075_ = lean_nat_add(v___y_2073_, v___y_2074_);
lean_dec(v___y_2074_);
lean_dec(v___y_2073_);
if (v_isShared_2068_ == 0)
{
lean_ctor_set(v___x_2067_, 4, v_r_2045_);
lean_ctor_set(v___x_2067_, 3, v_r_2061_);
lean_ctor_set(v___x_2067_, 2, v_v_2043_);
lean_ctor_set(v___x_2067_, 1, v_k_2042_);
lean_ctor_set(v___x_2067_, 0, v___x_2075_);
v___x_2077_ = v___x_2067_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v___x_2075_);
lean_ctor_set(v_reuseFailAlloc_2081_, 1, v_k_2042_);
lean_ctor_set(v_reuseFailAlloc_2081_, 2, v_v_2043_);
lean_ctor_set(v_reuseFailAlloc_2081_, 3, v_r_2061_);
lean_ctor_set(v_reuseFailAlloc_2081_, 4, v_r_2045_);
v___x_2077_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
lean_object* v___x_2079_; 
if (v_isShared_2056_ == 0)
{
lean_ctor_set(v___x_2055_, 4, v___x_2077_);
lean_ctor_set(v___x_2055_, 3, v___y_2072_);
lean_ctor_set(v___x_2055_, 2, v_v_2059_);
lean_ctor_set(v___x_2055_, 1, v_k_2058_);
lean_ctor_set(v___x_2055_, 0, v___x_2070_);
v___x_2079_ = v___x_2055_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v___x_2070_);
lean_ctor_set(v_reuseFailAlloc_2080_, 1, v_k_2058_);
lean_ctor_set(v_reuseFailAlloc_2080_, 2, v_v_2059_);
lean_ctor_set(v_reuseFailAlloc_2080_, 3, v___y_2072_);
lean_ctor_set(v_reuseFailAlloc_2080_, 4, v___x_2077_);
v___x_2079_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
return v___x_2079_;
}
}
}
v___jp_2082_:
{
lean_object* v___x_2084_; lean_object* v___x_2086_; 
v___x_2084_ = lean_nat_add(v___x_2069_, v___y_2083_);
lean_dec(v___y_2083_);
lean_dec(v___x_2069_);
if (v_isShared_2035_ == 0)
{
lean_ctor_set(v___x_2034_, 4, v_l_2060_);
lean_ctor_set(v___x_2034_, 0, v___x_2084_);
v___x_2086_ = v___x_2034_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v___x_2084_);
lean_ctor_set(v_reuseFailAlloc_2090_, 1, v_k_2029_);
lean_ctor_set(v_reuseFailAlloc_2090_, 2, v_v_2030_);
lean_ctor_set(v_reuseFailAlloc_2090_, 3, v_l_2031_);
lean_ctor_set(v_reuseFailAlloc_2090_, 4, v_l_2060_);
v___x_2086_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
lean_object* v___x_2087_; 
v___x_2087_ = lean_nat_add(v___x_2039_, v_size_2062_);
if (lean_obj_tag(v_r_2061_) == 0)
{
lean_object* v_size_2088_; 
v_size_2088_ = lean_ctor_get(v_r_2061_, 0);
lean_inc(v_size_2088_);
v___y_2072_ = v___x_2086_;
v___y_2073_ = v___x_2087_;
v___y_2074_ = v_size_2088_;
goto v___jp_2071_;
}
else
{
lean_object* v___x_2089_; 
v___x_2089_ = lean_unsigned_to_nat(0u);
v___y_2072_ = v___x_2086_;
v___y_2073_ = v___x_2087_;
v___y_2074_ = v___x_2089_;
goto v___jp_2071_;
}
}
}
}
}
else
{
lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2103_; 
lean_del_object(v___x_2034_);
v___x_2099_ = lean_nat_add(v___x_2039_, v_size_2040_);
v___x_2100_ = lean_nat_add(v___x_2099_, v_size_2041_);
lean_dec(v_size_2041_);
v___x_2101_ = lean_nat_add(v___x_2099_, v_size_2057_);
lean_dec(v___x_2099_);
lean_inc_ref(v_l_2031_);
if (v_isShared_2056_ == 0)
{
lean_ctor_set(v___x_2055_, 4, v_l_2044_);
lean_ctor_set(v___x_2055_, 3, v_l_2031_);
lean_ctor_set(v___x_2055_, 2, v_v_2030_);
lean_ctor_set(v___x_2055_, 1, v_k_2029_);
lean_ctor_set(v___x_2055_, 0, v___x_2101_);
v___x_2103_ = v___x_2055_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v___x_2101_);
lean_ctor_set(v_reuseFailAlloc_2116_, 1, v_k_2029_);
lean_ctor_set(v_reuseFailAlloc_2116_, 2, v_v_2030_);
lean_ctor_set(v_reuseFailAlloc_2116_, 3, v_l_2031_);
lean_ctor_set(v_reuseFailAlloc_2116_, 4, v_l_2044_);
v___x_2103_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2110_; 
v_isSharedCheck_2110_ = !lean_is_exclusive(v_l_2031_);
if (v_isSharedCheck_2110_ == 0)
{
lean_object* v_unused_2111_; lean_object* v_unused_2112_; lean_object* v_unused_2113_; lean_object* v_unused_2114_; lean_object* v_unused_2115_; 
v_unused_2111_ = lean_ctor_get(v_l_2031_, 4);
lean_dec(v_unused_2111_);
v_unused_2112_ = lean_ctor_get(v_l_2031_, 3);
lean_dec(v_unused_2112_);
v_unused_2113_ = lean_ctor_get(v_l_2031_, 2);
lean_dec(v_unused_2113_);
v_unused_2114_ = lean_ctor_get(v_l_2031_, 1);
lean_dec(v_unused_2114_);
v_unused_2115_ = lean_ctor_get(v_l_2031_, 0);
lean_dec(v_unused_2115_);
v___x_2105_ = v_l_2031_;
v_isShared_2106_ = v_isSharedCheck_2110_;
goto v_resetjp_2104_;
}
else
{
lean_dec(v_l_2031_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2110_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
lean_object* v___x_2108_; 
if (v_isShared_2106_ == 0)
{
lean_ctor_set(v___x_2105_, 4, v_r_2045_);
lean_ctor_set(v___x_2105_, 3, v___x_2103_);
lean_ctor_set(v___x_2105_, 2, v_v_2043_);
lean_ctor_set(v___x_2105_, 1, v_k_2042_);
lean_ctor_set(v___x_2105_, 0, v___x_2100_);
v___x_2108_ = v___x_2105_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v___x_2100_);
lean_ctor_set(v_reuseFailAlloc_2109_, 1, v_k_2042_);
lean_ctor_set(v_reuseFailAlloc_2109_, 2, v_v_2043_);
lean_ctor_set(v_reuseFailAlloc_2109_, 3, v___x_2103_);
lean_ctor_set(v_reuseFailAlloc_2109_, 4, v_r_2045_);
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
}
}
}
else
{
lean_object* v_l_2123_; 
v_l_2123_ = lean_ctor_get(v_impl_2038_, 3);
lean_inc(v_l_2123_);
if (lean_obj_tag(v_l_2123_) == 0)
{
lean_object* v_r_2124_; lean_object* v_k_2125_; lean_object* v_v_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2149_; 
v_r_2124_ = lean_ctor_get(v_impl_2038_, 4);
v_k_2125_ = lean_ctor_get(v_impl_2038_, 1);
v_v_2126_ = lean_ctor_get(v_impl_2038_, 2);
v_isSharedCheck_2149_ = !lean_is_exclusive(v_impl_2038_);
if (v_isSharedCheck_2149_ == 0)
{
lean_object* v_unused_2150_; lean_object* v_unused_2151_; 
v_unused_2150_ = lean_ctor_get(v_impl_2038_, 3);
lean_dec(v_unused_2150_);
v_unused_2151_ = lean_ctor_get(v_impl_2038_, 0);
lean_dec(v_unused_2151_);
v___x_2128_ = v_impl_2038_;
v_isShared_2129_ = v_isSharedCheck_2149_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_r_2124_);
lean_inc(v_v_2126_);
lean_inc(v_k_2125_);
lean_dec(v_impl_2038_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2149_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v_k_2130_; lean_object* v_v_2131_; lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2145_; 
v_k_2130_ = lean_ctor_get(v_l_2123_, 1);
v_v_2131_ = lean_ctor_get(v_l_2123_, 2);
v_isSharedCheck_2145_ = !lean_is_exclusive(v_l_2123_);
if (v_isSharedCheck_2145_ == 0)
{
lean_object* v_unused_2146_; lean_object* v_unused_2147_; lean_object* v_unused_2148_; 
v_unused_2146_ = lean_ctor_get(v_l_2123_, 4);
lean_dec(v_unused_2146_);
v_unused_2147_ = lean_ctor_get(v_l_2123_, 3);
lean_dec(v_unused_2147_);
v_unused_2148_ = lean_ctor_get(v_l_2123_, 0);
lean_dec(v_unused_2148_);
v___x_2133_ = v_l_2123_;
v_isShared_2134_ = v_isSharedCheck_2145_;
goto v_resetjp_2132_;
}
else
{
lean_inc(v_v_2131_);
lean_inc(v_k_2130_);
lean_dec(v_l_2123_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2145_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
lean_object* v___x_2135_; lean_object* v___x_2137_; 
v___x_2135_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2124_, 2);
if (v_isShared_2134_ == 0)
{
lean_ctor_set(v___x_2133_, 4, v_r_2124_);
lean_ctor_set(v___x_2133_, 3, v_r_2124_);
lean_ctor_set(v___x_2133_, 2, v_v_2030_);
lean_ctor_set(v___x_2133_, 1, v_k_2029_);
lean_ctor_set(v___x_2133_, 0, v___x_2039_);
v___x_2137_ = v___x_2133_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v___x_2039_);
lean_ctor_set(v_reuseFailAlloc_2144_, 1, v_k_2029_);
lean_ctor_set(v_reuseFailAlloc_2144_, 2, v_v_2030_);
lean_ctor_set(v_reuseFailAlloc_2144_, 3, v_r_2124_);
lean_ctor_set(v_reuseFailAlloc_2144_, 4, v_r_2124_);
v___x_2137_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
lean_object* v___x_2139_; 
lean_inc(v_r_2124_);
if (v_isShared_2129_ == 0)
{
lean_ctor_set(v___x_2128_, 3, v_r_2124_);
lean_ctor_set(v___x_2128_, 0, v___x_2039_);
v___x_2139_ = v___x_2128_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v___x_2039_);
lean_ctor_set(v_reuseFailAlloc_2143_, 1, v_k_2125_);
lean_ctor_set(v_reuseFailAlloc_2143_, 2, v_v_2126_);
lean_ctor_set(v_reuseFailAlloc_2143_, 3, v_r_2124_);
lean_ctor_set(v_reuseFailAlloc_2143_, 4, v_r_2124_);
v___x_2139_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
lean_object* v___x_2141_; 
if (v_isShared_2035_ == 0)
{
lean_ctor_set(v___x_2034_, 4, v___x_2139_);
lean_ctor_set(v___x_2034_, 3, v___x_2137_);
lean_ctor_set(v___x_2034_, 2, v_v_2131_);
lean_ctor_set(v___x_2034_, 1, v_k_2130_);
lean_ctor_set(v___x_2034_, 0, v___x_2135_);
v___x_2141_ = v___x_2034_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v___x_2135_);
lean_ctor_set(v_reuseFailAlloc_2142_, 1, v_k_2130_);
lean_ctor_set(v_reuseFailAlloc_2142_, 2, v_v_2131_);
lean_ctor_set(v_reuseFailAlloc_2142_, 3, v___x_2137_);
lean_ctor_set(v_reuseFailAlloc_2142_, 4, v___x_2139_);
v___x_2141_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
return v___x_2141_;
}
}
}
}
}
}
else
{
lean_object* v_r_2152_; 
v_r_2152_ = lean_ctor_get(v_impl_2038_, 4);
lean_inc(v_r_2152_);
if (lean_obj_tag(v_r_2152_) == 0)
{
lean_object* v_k_2153_; lean_object* v_v_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2165_; 
v_k_2153_ = lean_ctor_get(v_impl_2038_, 1);
v_v_2154_ = lean_ctor_get(v_impl_2038_, 2);
v_isSharedCheck_2165_ = !lean_is_exclusive(v_impl_2038_);
if (v_isSharedCheck_2165_ == 0)
{
lean_object* v_unused_2166_; lean_object* v_unused_2167_; lean_object* v_unused_2168_; 
v_unused_2166_ = lean_ctor_get(v_impl_2038_, 4);
lean_dec(v_unused_2166_);
v_unused_2167_ = lean_ctor_get(v_impl_2038_, 3);
lean_dec(v_unused_2167_);
v_unused_2168_ = lean_ctor_get(v_impl_2038_, 0);
lean_dec(v_unused_2168_);
v___x_2156_ = v_impl_2038_;
v_isShared_2157_ = v_isSharedCheck_2165_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_v_2154_);
lean_inc(v_k_2153_);
lean_dec(v_impl_2038_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2165_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___x_2158_; lean_object* v___x_2160_; 
v___x_2158_ = lean_unsigned_to_nat(3u);
if (v_isShared_2157_ == 0)
{
lean_ctor_set(v___x_2156_, 4, v_l_2123_);
lean_ctor_set(v___x_2156_, 2, v_v_2030_);
lean_ctor_set(v___x_2156_, 1, v_k_2029_);
lean_ctor_set(v___x_2156_, 0, v___x_2039_);
v___x_2160_ = v___x_2156_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v___x_2039_);
lean_ctor_set(v_reuseFailAlloc_2164_, 1, v_k_2029_);
lean_ctor_set(v_reuseFailAlloc_2164_, 2, v_v_2030_);
lean_ctor_set(v_reuseFailAlloc_2164_, 3, v_l_2123_);
lean_ctor_set(v_reuseFailAlloc_2164_, 4, v_l_2123_);
v___x_2160_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
lean_object* v___x_2162_; 
if (v_isShared_2035_ == 0)
{
lean_ctor_set(v___x_2034_, 4, v_r_2152_);
lean_ctor_set(v___x_2034_, 3, v___x_2160_);
lean_ctor_set(v___x_2034_, 2, v_v_2154_);
lean_ctor_set(v___x_2034_, 1, v_k_2153_);
lean_ctor_set(v___x_2034_, 0, v___x_2158_);
v___x_2162_ = v___x_2034_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v___x_2158_);
lean_ctor_set(v_reuseFailAlloc_2163_, 1, v_k_2153_);
lean_ctor_set(v_reuseFailAlloc_2163_, 2, v_v_2154_);
lean_ctor_set(v_reuseFailAlloc_2163_, 3, v___x_2160_);
lean_ctor_set(v_reuseFailAlloc_2163_, 4, v_r_2152_);
v___x_2162_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
return v___x_2162_;
}
}
}
}
else
{
lean_object* v___x_2169_; lean_object* v___x_2171_; 
v___x_2169_ = lean_unsigned_to_nat(2u);
if (v_isShared_2035_ == 0)
{
lean_ctor_set(v___x_2034_, 4, v_impl_2038_);
lean_ctor_set(v___x_2034_, 3, v_r_2152_);
lean_ctor_set(v___x_2034_, 0, v___x_2169_);
v___x_2171_ = v___x_2034_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v___x_2169_);
lean_ctor_set(v_reuseFailAlloc_2172_, 1, v_k_2029_);
lean_ctor_set(v_reuseFailAlloc_2172_, 2, v_v_2030_);
lean_ctor_set(v_reuseFailAlloc_2172_, 3, v_r_2152_);
lean_ctor_set(v_reuseFailAlloc_2172_, 4, v_impl_2038_);
v___x_2171_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
return v___x_2171_;
}
}
}
}
}
else
{
lean_object* v___x_2174_; 
lean_dec(v_v_2030_);
lean_dec(v_k_2029_);
if (v_isShared_2035_ == 0)
{
lean_ctor_set(v___x_2034_, 2, v_v_2026_);
lean_ctor_set(v___x_2034_, 1, v_k_2025_);
v___x_2174_ = v___x_2034_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v_size_2028_);
lean_ctor_set(v_reuseFailAlloc_2175_, 1, v_k_2025_);
lean_ctor_set(v_reuseFailAlloc_2175_, 2, v_v_2026_);
lean_ctor_set(v_reuseFailAlloc_2175_, 3, v_l_2031_);
lean_ctor_set(v_reuseFailAlloc_2175_, 4, v_r_2032_);
v___x_2174_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
return v___x_2174_;
}
}
}
else
{
lean_object* v_impl_2176_; lean_object* v___x_2177_; 
lean_dec(v_size_2028_);
v_impl_2176_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1___redArg(v_k_2025_, v_v_2026_, v_l_2031_);
v___x_2177_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_2032_) == 0)
{
lean_object* v_size_2178_; lean_object* v_size_2179_; lean_object* v_k_2180_; lean_object* v_v_2181_; lean_object* v_l_2182_; lean_object* v_r_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; uint8_t v___x_2186_; 
v_size_2178_ = lean_ctor_get(v_r_2032_, 0);
v_size_2179_ = lean_ctor_get(v_impl_2176_, 0);
v_k_2180_ = lean_ctor_get(v_impl_2176_, 1);
v_v_2181_ = lean_ctor_get(v_impl_2176_, 2);
v_l_2182_ = lean_ctor_get(v_impl_2176_, 3);
v_r_2183_ = lean_ctor_get(v_impl_2176_, 4);
lean_inc(v_r_2183_);
v___x_2184_ = lean_unsigned_to_nat(3u);
v___x_2185_ = lean_nat_mul(v___x_2184_, v_size_2178_);
v___x_2186_ = lean_nat_dec_lt(v___x_2185_, v_size_2179_);
lean_dec(v___x_2185_);
if (v___x_2186_ == 0)
{
lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2190_; 
lean_dec(v_r_2183_);
v___x_2187_ = lean_nat_add(v___x_2177_, v_size_2179_);
v___x_2188_ = lean_nat_add(v___x_2187_, v_size_2178_);
lean_dec(v___x_2187_);
if (v_isShared_2035_ == 0)
{
lean_ctor_set(v___x_2034_, 3, v_impl_2176_);
lean_ctor_set(v___x_2034_, 0, v___x_2188_);
v___x_2190_ = v___x_2034_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v___x_2188_);
lean_ctor_set(v_reuseFailAlloc_2191_, 1, v_k_2029_);
lean_ctor_set(v_reuseFailAlloc_2191_, 2, v_v_2030_);
lean_ctor_set(v_reuseFailAlloc_2191_, 3, v_impl_2176_);
lean_ctor_set(v_reuseFailAlloc_2191_, 4, v_r_2032_);
v___x_2190_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
return v___x_2190_;
}
}
else
{
lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2257_; 
lean_inc(v_l_2182_);
lean_inc(v_v_2181_);
lean_inc(v_k_2180_);
lean_inc(v_size_2179_);
v_isSharedCheck_2257_ = !lean_is_exclusive(v_impl_2176_);
if (v_isSharedCheck_2257_ == 0)
{
lean_object* v_unused_2258_; lean_object* v_unused_2259_; lean_object* v_unused_2260_; lean_object* v_unused_2261_; lean_object* v_unused_2262_; 
v_unused_2258_ = lean_ctor_get(v_impl_2176_, 4);
lean_dec(v_unused_2258_);
v_unused_2259_ = lean_ctor_get(v_impl_2176_, 3);
lean_dec(v_unused_2259_);
v_unused_2260_ = lean_ctor_get(v_impl_2176_, 2);
lean_dec(v_unused_2260_);
v_unused_2261_ = lean_ctor_get(v_impl_2176_, 1);
lean_dec(v_unused_2261_);
v_unused_2262_ = lean_ctor_get(v_impl_2176_, 0);
lean_dec(v_unused_2262_);
v___x_2193_ = v_impl_2176_;
v_isShared_2194_ = v_isSharedCheck_2257_;
goto v_resetjp_2192_;
}
else
{
lean_dec(v_impl_2176_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2257_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
lean_object* v_size_2195_; lean_object* v_size_2196_; lean_object* v_k_2197_; lean_object* v_v_2198_; lean_object* v_l_2199_; lean_object* v_r_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; uint8_t v___x_2203_; 
v_size_2195_ = lean_ctor_get(v_l_2182_, 0);
v_size_2196_ = lean_ctor_get(v_r_2183_, 0);
v_k_2197_ = lean_ctor_get(v_r_2183_, 1);
v_v_2198_ = lean_ctor_get(v_r_2183_, 2);
v_l_2199_ = lean_ctor_get(v_r_2183_, 3);
v_r_2200_ = lean_ctor_get(v_r_2183_, 4);
v___x_2201_ = lean_unsigned_to_nat(2u);
v___x_2202_ = lean_nat_mul(v___x_2201_, v_size_2195_);
v___x_2203_ = lean_nat_dec_lt(v_size_2196_, v___x_2202_);
lean_dec(v___x_2202_);
if (v___x_2203_ == 0)
{
lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2232_; 
lean_inc(v_r_2200_);
lean_inc(v_l_2199_);
lean_inc(v_v_2198_);
lean_inc(v_k_2197_);
v_isSharedCheck_2232_ = !lean_is_exclusive(v_r_2183_);
if (v_isSharedCheck_2232_ == 0)
{
lean_object* v_unused_2233_; lean_object* v_unused_2234_; lean_object* v_unused_2235_; lean_object* v_unused_2236_; lean_object* v_unused_2237_; 
v_unused_2233_ = lean_ctor_get(v_r_2183_, 4);
lean_dec(v_unused_2233_);
v_unused_2234_ = lean_ctor_get(v_r_2183_, 3);
lean_dec(v_unused_2234_);
v_unused_2235_ = lean_ctor_get(v_r_2183_, 2);
lean_dec(v_unused_2235_);
v_unused_2236_ = lean_ctor_get(v_r_2183_, 1);
lean_dec(v_unused_2236_);
v_unused_2237_ = lean_ctor_get(v_r_2183_, 0);
lean_dec(v_unused_2237_);
v___x_2205_ = v_r_2183_;
v_isShared_2206_ = v_isSharedCheck_2232_;
goto v_resetjp_2204_;
}
else
{
lean_dec(v_r_2183_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2232_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___y_2210_; lean_object* v___y_2211_; lean_object* v___y_2212_; lean_object* v___x_2220_; lean_object* v___y_2222_; 
v___x_2207_ = lean_nat_add(v___x_2177_, v_size_2179_);
lean_dec(v_size_2179_);
v___x_2208_ = lean_nat_add(v___x_2207_, v_size_2178_);
lean_dec(v___x_2207_);
v___x_2220_ = lean_nat_add(v___x_2177_, v_size_2195_);
if (lean_obj_tag(v_l_2199_) == 0)
{
lean_object* v_size_2230_; 
v_size_2230_ = lean_ctor_get(v_l_2199_, 0);
lean_inc(v_size_2230_);
v___y_2222_ = v_size_2230_;
goto v___jp_2221_;
}
else
{
lean_object* v___x_2231_; 
v___x_2231_ = lean_unsigned_to_nat(0u);
v___y_2222_ = v___x_2231_;
goto v___jp_2221_;
}
v___jp_2209_:
{
lean_object* v___x_2213_; lean_object* v___x_2215_; 
v___x_2213_ = lean_nat_add(v___y_2211_, v___y_2212_);
lean_dec(v___y_2212_);
lean_dec(v___y_2211_);
if (v_isShared_2206_ == 0)
{
lean_ctor_set(v___x_2205_, 4, v_r_2032_);
lean_ctor_set(v___x_2205_, 3, v_r_2200_);
lean_ctor_set(v___x_2205_, 2, v_v_2030_);
lean_ctor_set(v___x_2205_, 1, v_k_2029_);
lean_ctor_set(v___x_2205_, 0, v___x_2213_);
v___x_2215_ = v___x_2205_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v___x_2213_);
lean_ctor_set(v_reuseFailAlloc_2219_, 1, v_k_2029_);
lean_ctor_set(v_reuseFailAlloc_2219_, 2, v_v_2030_);
lean_ctor_set(v_reuseFailAlloc_2219_, 3, v_r_2200_);
lean_ctor_set(v_reuseFailAlloc_2219_, 4, v_r_2032_);
v___x_2215_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
lean_object* v___x_2217_; 
if (v_isShared_2194_ == 0)
{
lean_ctor_set(v___x_2193_, 4, v___x_2215_);
lean_ctor_set(v___x_2193_, 3, v___y_2210_);
lean_ctor_set(v___x_2193_, 2, v_v_2198_);
lean_ctor_set(v___x_2193_, 1, v_k_2197_);
lean_ctor_set(v___x_2193_, 0, v___x_2208_);
v___x_2217_ = v___x_2193_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v___x_2208_);
lean_ctor_set(v_reuseFailAlloc_2218_, 1, v_k_2197_);
lean_ctor_set(v_reuseFailAlloc_2218_, 2, v_v_2198_);
lean_ctor_set(v_reuseFailAlloc_2218_, 3, v___y_2210_);
lean_ctor_set(v_reuseFailAlloc_2218_, 4, v___x_2215_);
v___x_2217_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
return v___x_2217_;
}
}
}
v___jp_2221_:
{
lean_object* v___x_2223_; lean_object* v___x_2225_; 
v___x_2223_ = lean_nat_add(v___x_2220_, v___y_2222_);
lean_dec(v___y_2222_);
lean_dec(v___x_2220_);
if (v_isShared_2035_ == 0)
{
lean_ctor_set(v___x_2034_, 4, v_l_2199_);
lean_ctor_set(v___x_2034_, 3, v_l_2182_);
lean_ctor_set(v___x_2034_, 2, v_v_2181_);
lean_ctor_set(v___x_2034_, 1, v_k_2180_);
lean_ctor_set(v___x_2034_, 0, v___x_2223_);
v___x_2225_ = v___x_2034_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v___x_2223_);
lean_ctor_set(v_reuseFailAlloc_2229_, 1, v_k_2180_);
lean_ctor_set(v_reuseFailAlloc_2229_, 2, v_v_2181_);
lean_ctor_set(v_reuseFailAlloc_2229_, 3, v_l_2182_);
lean_ctor_set(v_reuseFailAlloc_2229_, 4, v_l_2199_);
v___x_2225_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
lean_object* v___x_2226_; 
v___x_2226_ = lean_nat_add(v___x_2177_, v_size_2178_);
if (lean_obj_tag(v_r_2200_) == 0)
{
lean_object* v_size_2227_; 
v_size_2227_ = lean_ctor_get(v_r_2200_, 0);
lean_inc(v_size_2227_);
v___y_2210_ = v___x_2225_;
v___y_2211_ = v___x_2226_;
v___y_2212_ = v_size_2227_;
goto v___jp_2209_;
}
else
{
lean_object* v___x_2228_; 
v___x_2228_ = lean_unsigned_to_nat(0u);
v___y_2210_ = v___x_2225_;
v___y_2211_ = v___x_2226_;
v___y_2212_ = v___x_2228_;
goto v___jp_2209_;
}
}
}
}
}
else
{
lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2243_; 
lean_del_object(v___x_2034_);
v___x_2238_ = lean_nat_add(v___x_2177_, v_size_2179_);
lean_dec(v_size_2179_);
v___x_2239_ = lean_nat_add(v___x_2238_, v_size_2178_);
lean_dec(v___x_2238_);
v___x_2240_ = lean_nat_add(v___x_2177_, v_size_2178_);
v___x_2241_ = lean_nat_add(v___x_2240_, v_size_2196_);
lean_dec(v___x_2240_);
lean_inc_ref(v_r_2032_);
if (v_isShared_2194_ == 0)
{
lean_ctor_set(v___x_2193_, 4, v_r_2032_);
lean_ctor_set(v___x_2193_, 3, v_r_2183_);
lean_ctor_set(v___x_2193_, 2, v_v_2030_);
lean_ctor_set(v___x_2193_, 1, v_k_2029_);
lean_ctor_set(v___x_2193_, 0, v___x_2241_);
v___x_2243_ = v___x_2193_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v___x_2241_);
lean_ctor_set(v_reuseFailAlloc_2256_, 1, v_k_2029_);
lean_ctor_set(v_reuseFailAlloc_2256_, 2, v_v_2030_);
lean_ctor_set(v_reuseFailAlloc_2256_, 3, v_r_2183_);
lean_ctor_set(v_reuseFailAlloc_2256_, 4, v_r_2032_);
v___x_2243_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2250_; 
v_isSharedCheck_2250_ = !lean_is_exclusive(v_r_2032_);
if (v_isSharedCheck_2250_ == 0)
{
lean_object* v_unused_2251_; lean_object* v_unused_2252_; lean_object* v_unused_2253_; lean_object* v_unused_2254_; lean_object* v_unused_2255_; 
v_unused_2251_ = lean_ctor_get(v_r_2032_, 4);
lean_dec(v_unused_2251_);
v_unused_2252_ = lean_ctor_get(v_r_2032_, 3);
lean_dec(v_unused_2252_);
v_unused_2253_ = lean_ctor_get(v_r_2032_, 2);
lean_dec(v_unused_2253_);
v_unused_2254_ = lean_ctor_get(v_r_2032_, 1);
lean_dec(v_unused_2254_);
v_unused_2255_ = lean_ctor_get(v_r_2032_, 0);
lean_dec(v_unused_2255_);
v___x_2245_ = v_r_2032_;
v_isShared_2246_ = v_isSharedCheck_2250_;
goto v_resetjp_2244_;
}
else
{
lean_dec(v_r_2032_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2250_;
goto v_resetjp_2244_;
}
v_resetjp_2244_:
{
lean_object* v___x_2248_; 
if (v_isShared_2246_ == 0)
{
lean_ctor_set(v___x_2245_, 4, v___x_2243_);
lean_ctor_set(v___x_2245_, 3, v_l_2182_);
lean_ctor_set(v___x_2245_, 2, v_v_2181_);
lean_ctor_set(v___x_2245_, 1, v_k_2180_);
lean_ctor_set(v___x_2245_, 0, v___x_2239_);
v___x_2248_ = v___x_2245_;
goto v_reusejp_2247_;
}
else
{
lean_object* v_reuseFailAlloc_2249_; 
v_reuseFailAlloc_2249_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2249_, 0, v___x_2239_);
lean_ctor_set(v_reuseFailAlloc_2249_, 1, v_k_2180_);
lean_ctor_set(v_reuseFailAlloc_2249_, 2, v_v_2181_);
lean_ctor_set(v_reuseFailAlloc_2249_, 3, v_l_2182_);
lean_ctor_set(v_reuseFailAlloc_2249_, 4, v___x_2243_);
v___x_2248_ = v_reuseFailAlloc_2249_;
goto v_reusejp_2247_;
}
v_reusejp_2247_:
{
return v___x_2248_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2263_; 
v_l_2263_ = lean_ctor_get(v_impl_2176_, 3);
if (lean_obj_tag(v_l_2263_) == 0)
{
lean_object* v_r_2264_; lean_object* v_k_2265_; lean_object* v_v_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2277_; 
lean_inc_ref(v_l_2263_);
v_r_2264_ = lean_ctor_get(v_impl_2176_, 4);
v_k_2265_ = lean_ctor_get(v_impl_2176_, 1);
v_v_2266_ = lean_ctor_get(v_impl_2176_, 2);
v_isSharedCheck_2277_ = !lean_is_exclusive(v_impl_2176_);
if (v_isSharedCheck_2277_ == 0)
{
lean_object* v_unused_2278_; lean_object* v_unused_2279_; 
v_unused_2278_ = lean_ctor_get(v_impl_2176_, 3);
lean_dec(v_unused_2278_);
v_unused_2279_ = lean_ctor_get(v_impl_2176_, 0);
lean_dec(v_unused_2279_);
v___x_2268_ = v_impl_2176_;
v_isShared_2269_ = v_isSharedCheck_2277_;
goto v_resetjp_2267_;
}
else
{
lean_inc(v_r_2264_);
lean_inc(v_v_2266_);
lean_inc(v_k_2265_);
lean_dec(v_impl_2176_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2277_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
lean_object* v___x_2270_; lean_object* v___x_2272_; 
v___x_2270_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2264_);
if (v_isShared_2269_ == 0)
{
lean_ctor_set(v___x_2268_, 3, v_r_2264_);
lean_ctor_set(v___x_2268_, 2, v_v_2030_);
lean_ctor_set(v___x_2268_, 1, v_k_2029_);
lean_ctor_set(v___x_2268_, 0, v___x_2177_);
v___x_2272_ = v___x_2268_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v___x_2177_);
lean_ctor_set(v_reuseFailAlloc_2276_, 1, v_k_2029_);
lean_ctor_set(v_reuseFailAlloc_2276_, 2, v_v_2030_);
lean_ctor_set(v_reuseFailAlloc_2276_, 3, v_r_2264_);
lean_ctor_set(v_reuseFailAlloc_2276_, 4, v_r_2264_);
v___x_2272_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
lean_object* v___x_2274_; 
if (v_isShared_2035_ == 0)
{
lean_ctor_set(v___x_2034_, 4, v___x_2272_);
lean_ctor_set(v___x_2034_, 3, v_l_2263_);
lean_ctor_set(v___x_2034_, 2, v_v_2266_);
lean_ctor_set(v___x_2034_, 1, v_k_2265_);
lean_ctor_set(v___x_2034_, 0, v___x_2270_);
v___x_2274_ = v___x_2034_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v___x_2270_);
lean_ctor_set(v_reuseFailAlloc_2275_, 1, v_k_2265_);
lean_ctor_set(v_reuseFailAlloc_2275_, 2, v_v_2266_);
lean_ctor_set(v_reuseFailAlloc_2275_, 3, v_l_2263_);
lean_ctor_set(v_reuseFailAlloc_2275_, 4, v___x_2272_);
v___x_2274_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
return v___x_2274_;
}
}
}
}
else
{
lean_object* v_r_2280_; 
v_r_2280_ = lean_ctor_get(v_impl_2176_, 4);
lean_inc(v_r_2280_);
if (lean_obj_tag(v_r_2280_) == 0)
{
lean_object* v_k_2281_; lean_object* v_v_2282_; lean_object* v___x_2284_; uint8_t v_isShared_2285_; uint8_t v_isSharedCheck_2305_; 
lean_inc(v_l_2263_);
v_k_2281_ = lean_ctor_get(v_impl_2176_, 1);
v_v_2282_ = lean_ctor_get(v_impl_2176_, 2);
v_isSharedCheck_2305_ = !lean_is_exclusive(v_impl_2176_);
if (v_isSharedCheck_2305_ == 0)
{
lean_object* v_unused_2306_; lean_object* v_unused_2307_; lean_object* v_unused_2308_; 
v_unused_2306_ = lean_ctor_get(v_impl_2176_, 4);
lean_dec(v_unused_2306_);
v_unused_2307_ = lean_ctor_get(v_impl_2176_, 3);
lean_dec(v_unused_2307_);
v_unused_2308_ = lean_ctor_get(v_impl_2176_, 0);
lean_dec(v_unused_2308_);
v___x_2284_ = v_impl_2176_;
v_isShared_2285_ = v_isSharedCheck_2305_;
goto v_resetjp_2283_;
}
else
{
lean_inc(v_v_2282_);
lean_inc(v_k_2281_);
lean_dec(v_impl_2176_);
v___x_2284_ = lean_box(0);
v_isShared_2285_ = v_isSharedCheck_2305_;
goto v_resetjp_2283_;
}
v_resetjp_2283_:
{
lean_object* v_k_2286_; lean_object* v_v_2287_; lean_object* v___x_2289_; uint8_t v_isShared_2290_; uint8_t v_isSharedCheck_2301_; 
v_k_2286_ = lean_ctor_get(v_r_2280_, 1);
v_v_2287_ = lean_ctor_get(v_r_2280_, 2);
v_isSharedCheck_2301_ = !lean_is_exclusive(v_r_2280_);
if (v_isSharedCheck_2301_ == 0)
{
lean_object* v_unused_2302_; lean_object* v_unused_2303_; lean_object* v_unused_2304_; 
v_unused_2302_ = lean_ctor_get(v_r_2280_, 4);
lean_dec(v_unused_2302_);
v_unused_2303_ = lean_ctor_get(v_r_2280_, 3);
lean_dec(v_unused_2303_);
v_unused_2304_ = lean_ctor_get(v_r_2280_, 0);
lean_dec(v_unused_2304_);
v___x_2289_ = v_r_2280_;
v_isShared_2290_ = v_isSharedCheck_2301_;
goto v_resetjp_2288_;
}
else
{
lean_inc(v_v_2287_);
lean_inc(v_k_2286_);
lean_dec(v_r_2280_);
v___x_2289_ = lean_box(0);
v_isShared_2290_ = v_isSharedCheck_2301_;
goto v_resetjp_2288_;
}
v_resetjp_2288_:
{
lean_object* v___x_2291_; lean_object* v___x_2293_; 
v___x_2291_ = lean_unsigned_to_nat(3u);
if (v_isShared_2290_ == 0)
{
lean_ctor_set(v___x_2289_, 4, v_l_2263_);
lean_ctor_set(v___x_2289_, 3, v_l_2263_);
lean_ctor_set(v___x_2289_, 2, v_v_2282_);
lean_ctor_set(v___x_2289_, 1, v_k_2281_);
lean_ctor_set(v___x_2289_, 0, v___x_2177_);
v___x_2293_ = v___x_2289_;
goto v_reusejp_2292_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v___x_2177_);
lean_ctor_set(v_reuseFailAlloc_2300_, 1, v_k_2281_);
lean_ctor_set(v_reuseFailAlloc_2300_, 2, v_v_2282_);
lean_ctor_set(v_reuseFailAlloc_2300_, 3, v_l_2263_);
lean_ctor_set(v_reuseFailAlloc_2300_, 4, v_l_2263_);
v___x_2293_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2292_;
}
v_reusejp_2292_:
{
lean_object* v___x_2295_; 
if (v_isShared_2285_ == 0)
{
lean_ctor_set(v___x_2284_, 4, v_l_2263_);
lean_ctor_set(v___x_2284_, 2, v_v_2030_);
lean_ctor_set(v___x_2284_, 1, v_k_2029_);
lean_ctor_set(v___x_2284_, 0, v___x_2177_);
v___x_2295_ = v___x_2284_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v___x_2177_);
lean_ctor_set(v_reuseFailAlloc_2299_, 1, v_k_2029_);
lean_ctor_set(v_reuseFailAlloc_2299_, 2, v_v_2030_);
lean_ctor_set(v_reuseFailAlloc_2299_, 3, v_l_2263_);
lean_ctor_set(v_reuseFailAlloc_2299_, 4, v_l_2263_);
v___x_2295_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
lean_object* v___x_2297_; 
if (v_isShared_2035_ == 0)
{
lean_ctor_set(v___x_2034_, 4, v___x_2295_);
lean_ctor_set(v___x_2034_, 3, v___x_2293_);
lean_ctor_set(v___x_2034_, 2, v_v_2287_);
lean_ctor_set(v___x_2034_, 1, v_k_2286_);
lean_ctor_set(v___x_2034_, 0, v___x_2291_);
v___x_2297_ = v___x_2034_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2298_; 
v_reuseFailAlloc_2298_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2298_, 0, v___x_2291_);
lean_ctor_set(v_reuseFailAlloc_2298_, 1, v_k_2286_);
lean_ctor_set(v_reuseFailAlloc_2298_, 2, v_v_2287_);
lean_ctor_set(v_reuseFailAlloc_2298_, 3, v___x_2293_);
lean_ctor_set(v_reuseFailAlloc_2298_, 4, v___x_2295_);
v___x_2297_ = v_reuseFailAlloc_2298_;
goto v_reusejp_2296_;
}
v_reusejp_2296_:
{
return v___x_2297_;
}
}
}
}
}
}
else
{
lean_object* v___x_2309_; lean_object* v___x_2311_; 
v___x_2309_ = lean_unsigned_to_nat(2u);
if (v_isShared_2035_ == 0)
{
lean_ctor_set(v___x_2034_, 4, v_r_2280_);
lean_ctor_set(v___x_2034_, 3, v_impl_2176_);
lean_ctor_set(v___x_2034_, 0, v___x_2309_);
v___x_2311_ = v___x_2034_;
goto v_reusejp_2310_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v___x_2309_);
lean_ctor_set(v_reuseFailAlloc_2312_, 1, v_k_2029_);
lean_ctor_set(v_reuseFailAlloc_2312_, 2, v_v_2030_);
lean_ctor_set(v_reuseFailAlloc_2312_, 3, v_impl_2176_);
lean_ctor_set(v_reuseFailAlloc_2312_, 4, v_r_2280_);
v___x_2311_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2310_;
}
v_reusejp_2310_:
{
return v___x_2311_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2314_; lean_object* v___x_2315_; 
v___x_2314_ = lean_unsigned_to_nat(1u);
v___x_2315_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2315_, 0, v___x_2314_);
lean_ctor_set(v___x_2315_, 1, v_k_2025_);
lean_ctor_set(v___x_2315_, 2, v_v_2026_);
lean_ctor_set(v___x_2315_, 3, v_t_2027_);
lean_ctor_set(v___x_2315_, 4, v_t_2027_);
return v___x_2315_;
}
}
}
lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2(lean_object* v_y_2316_, lean_object* v_x_2317_, size_t v_x_2318_, size_t v_x_2319_){
_start:
{
if (lean_obj_tag(v_x_2317_) == 0)
{
lean_object* v_cs_2320_; size_t v_j_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; uint8_t v___x_2324_; 
v_cs_2320_ = lean_ctor_get(v_x_2317_, 0);
v_j_2321_ = lean_usize_shift_right(v_x_2318_, v_x_2319_);
v___x_2322_ = lean_usize_to_nat(v_j_2321_);
v___x_2323_ = lean_array_get_size(v_cs_2320_);
v___x_2324_ = lean_nat_dec_lt(v___x_2322_, v___x_2323_);
if (v___x_2324_ == 0)
{
lean_dec(v___x_2322_);
lean_dec(v_y_2316_);
return v_x_2317_;
}
else
{
lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2342_; 
lean_inc_ref(v_cs_2320_);
v_isSharedCheck_2342_ = !lean_is_exclusive(v_x_2317_);
if (v_isSharedCheck_2342_ == 0)
{
lean_object* v_unused_2343_; 
v_unused_2343_ = lean_ctor_get(v_x_2317_, 0);
lean_dec(v_unused_2343_);
v___x_2326_ = v_x_2317_;
v_isShared_2327_ = v_isSharedCheck_2342_;
goto v_resetjp_2325_;
}
else
{
lean_dec(v_x_2317_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2342_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
size_t v___x_2328_; size_t v___x_2329_; size_t v___x_2330_; size_t v_i_2331_; size_t v___x_2332_; size_t v_shift_2333_; lean_object* v_v_2334_; lean_object* v___x_2335_; lean_object* v_xs_x27_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2340_; 
v___x_2328_ = ((size_t)1ULL);
v___x_2329_ = lean_usize_shift_left(v___x_2328_, v_x_2319_);
v___x_2330_ = lean_usize_sub(v___x_2329_, v___x_2328_);
v_i_2331_ = lean_usize_land(v_x_2318_, v___x_2330_);
v___x_2332_ = ((size_t)5ULL);
v_shift_2333_ = lean_usize_sub(v_x_2319_, v___x_2332_);
v_v_2334_ = lean_array_fget(v_cs_2320_, v___x_2322_);
v___x_2335_ = lean_box(0);
v_xs_x27_2336_ = lean_array_fset(v_cs_2320_, v___x_2322_, v___x_2335_);
v___x_2337_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2(v_y_2316_, v_v_2334_, v_i_2331_, v_shift_2333_);
v___x_2338_ = lean_array_fset(v_xs_x27_2336_, v___x_2322_, v___x_2337_);
lean_dec(v___x_2322_);
if (v_isShared_2327_ == 0)
{
lean_ctor_set(v___x_2326_, 0, v___x_2338_);
v___x_2340_ = v___x_2326_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v___x_2338_);
v___x_2340_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
return v___x_2340_;
}
}
}
}
else
{
lean_object* v_vs_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; uint8_t v___x_2347_; 
v_vs_2344_ = lean_ctor_get(v_x_2317_, 0);
v___x_2345_ = lean_usize_to_nat(v_x_2318_);
v___x_2346_ = lean_array_get_size(v_vs_2344_);
v___x_2347_ = lean_nat_dec_lt(v___x_2345_, v___x_2346_);
if (v___x_2347_ == 0)
{
lean_dec(v___x_2345_);
lean_dec(v_y_2316_);
return v_x_2317_;
}
else
{
lean_object* v___x_2349_; uint8_t v_isShared_2350_; uint8_t v_isSharedCheck_2362_; 
lean_inc_ref(v_vs_2344_);
v_isSharedCheck_2362_ = !lean_is_exclusive(v_x_2317_);
if (v_isSharedCheck_2362_ == 0)
{
lean_object* v_unused_2363_; 
v_unused_2363_ = lean_ctor_get(v_x_2317_, 0);
lean_dec(v_unused_2363_);
v___x_2349_ = v_x_2317_;
v_isShared_2350_ = v_isSharedCheck_2362_;
goto v_resetjp_2348_;
}
else
{
lean_dec(v_x_2317_);
v___x_2349_ = lean_box(0);
v_isShared_2350_ = v_isSharedCheck_2362_;
goto v_resetjp_2348_;
}
v_resetjp_2348_:
{
lean_object* v_v_2351_; lean_object* v___x_2352_; lean_object* v_xs_x27_2353_; lean_object* v___y_2355_; uint8_t v___x_2360_; 
v_v_2351_ = lean_array_fget(v_vs_2344_, v___x_2345_);
v___x_2352_ = lean_box(0);
v_xs_x27_2353_ = lean_array_fset(v_vs_2344_, v___x_2345_, v___x_2352_);
v___x_2360_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg(v_y_2316_, v_v_2351_);
if (v___x_2360_ == 0)
{
lean_object* v___x_2361_; 
v___x_2361_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1___redArg(v_y_2316_, v___x_2352_, v_v_2351_);
v___y_2355_ = v___x_2361_;
goto v___jp_2354_;
}
else
{
lean_dec(v_y_2316_);
v___y_2355_ = v_v_2351_;
goto v___jp_2354_;
}
v___jp_2354_:
{
lean_object* v___x_2356_; lean_object* v___x_2358_; 
v___x_2356_ = lean_array_fset(v_xs_x27_2353_, v___x_2345_, v___y_2355_);
lean_dec(v___x_2345_);
if (v_isShared_2350_ == 0)
{
lean_ctor_set(v___x_2349_, 0, v___x_2356_);
v___x_2358_ = v___x_2349_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v___x_2356_);
v___x_2358_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
return v___x_2358_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_y_2316_ = stack[0].m_obj;
lean_object* v_x_2317_ = stack[1].m_obj;
size_t v_x_2318_ = stack[2].m_num;
size_t v_x_2319_ = stack[3].m_num;
lean_object* v_res_2364_;
v_res_2364_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2(v_y_2316_, v_x_2317_, v_x_2318_, v_x_2319_);
stack->m_obj
 = v_res_2364_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2___boxed(lean_object* v_y_2365_, lean_object* v_x_2366_, lean_object* v_x_2367_, lean_object* v_x_2368_){
_start:
{
size_t v_x_5440__boxed_2369_; size_t v_x_5441__boxed_2370_; lean_object* v_res_2371_; 
v_x_5440__boxed_2369_ = lean_unbox_usize(v_x_2367_);
lean_dec(v_x_2367_);
v_x_5441__boxed_2370_ = lean_unbox_usize(v_x_2368_);
lean_dec(v_x_2368_);
v_res_2371_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2(v_y_2365_, v_x_2366_, v_x_5440__boxed_2369_, v_x_5441__boxed_2370_);
return v_res_2371_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2(lean_object* v_y_2372_, lean_object* v_t_2373_, lean_object* v_i_2374_){
_start:
{
lean_object* v_root_2375_; lean_object* v_tail_2376_; lean_object* v_size_2377_; size_t v_shift_2378_; lean_object* v_tailOff_2379_; lean_object* v___x_2381_; uint8_t v_isShared_2382_; uint8_t v_isSharedCheck_2406_; 
v_root_2375_ = lean_ctor_get(v_t_2373_, 0);
v_tail_2376_ = lean_ctor_get(v_t_2373_, 1);
v_size_2377_ = lean_ctor_get(v_t_2373_, 2);
v_shift_2378_ = lean_ctor_get_usize(v_t_2373_, 4);
v_tailOff_2379_ = lean_ctor_get(v_t_2373_, 3);
v_isSharedCheck_2406_ = !lean_is_exclusive(v_t_2373_);
if (v_isSharedCheck_2406_ == 0)
{
v___x_2381_ = v_t_2373_;
v_isShared_2382_ = v_isSharedCheck_2406_;
goto v_resetjp_2380_;
}
else
{
lean_inc(v_tailOff_2379_);
lean_inc(v_size_2377_);
lean_inc(v_tail_2376_);
lean_inc(v_root_2375_);
lean_dec(v_t_2373_);
v___x_2381_ = lean_box(0);
v_isShared_2382_ = v_isSharedCheck_2406_;
goto v_resetjp_2380_;
}
v_resetjp_2380_:
{
uint8_t v___x_2383_; 
v___x_2383_ = lean_nat_dec_le(v_tailOff_2379_, v_i_2374_);
if (v___x_2383_ == 0)
{
size_t v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2387_; 
v___x_2384_ = lean_usize_of_nat(v_i_2374_);
v___x_2385_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2(v_y_2372_, v_root_2375_, v___x_2384_, v_shift_2378_);
if (v_isShared_2382_ == 0)
{
lean_ctor_set(v___x_2381_, 0, v___x_2385_);
v___x_2387_ = v___x_2381_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v___x_2385_);
lean_ctor_set(v_reuseFailAlloc_2388_, 1, v_tail_2376_);
lean_ctor_set(v_reuseFailAlloc_2388_, 2, v_size_2377_);
lean_ctor_set(v_reuseFailAlloc_2388_, 3, v_tailOff_2379_);
lean_ctor_set_usize(v_reuseFailAlloc_2388_, 4, v_shift_2378_);
v___x_2387_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
return v___x_2387_;
}
}
else
{
lean_object* v___x_2389_; lean_object* v___x_2390_; uint8_t v___x_2391_; 
v___x_2389_ = lean_nat_sub(v_i_2374_, v_tailOff_2379_);
v___x_2390_ = lean_array_get_size(v_tail_2376_);
v___x_2391_ = lean_nat_dec_lt(v___x_2389_, v___x_2390_);
if (v___x_2391_ == 0)
{
lean_object* v___x_2393_; 
lean_dec(v___x_2389_);
lean_dec(v_y_2372_);
if (v_isShared_2382_ == 0)
{
v___x_2393_ = v___x_2381_;
goto v_reusejp_2392_;
}
else
{
lean_object* v_reuseFailAlloc_2394_; 
v_reuseFailAlloc_2394_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2394_, 0, v_root_2375_);
lean_ctor_set(v_reuseFailAlloc_2394_, 1, v_tail_2376_);
lean_ctor_set(v_reuseFailAlloc_2394_, 2, v_size_2377_);
lean_ctor_set(v_reuseFailAlloc_2394_, 3, v_tailOff_2379_);
lean_ctor_set_usize(v_reuseFailAlloc_2394_, 4, v_shift_2378_);
v___x_2393_ = v_reuseFailAlloc_2394_;
goto v_reusejp_2392_;
}
v_reusejp_2392_:
{
return v___x_2393_;
}
}
else
{
lean_object* v_v_2395_; lean_object* v___x_2396_; lean_object* v_xs_x27_2397_; lean_object* v___y_2399_; uint8_t v___x_2404_; 
v_v_2395_ = lean_array_fget(v_tail_2376_, v___x_2389_);
v___x_2396_ = lean_box(0);
v_xs_x27_2397_ = lean_array_fset(v_tail_2376_, v___x_2389_, v___x_2396_);
v___x_2404_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg(v_y_2372_, v_v_2395_);
if (v___x_2404_ == 0)
{
lean_object* v___x_2405_; 
v___x_2405_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1___redArg(v_y_2372_, v___x_2396_, v_v_2395_);
v___y_2399_ = v___x_2405_;
goto v___jp_2398_;
}
else
{
lean_dec(v_y_2372_);
v___y_2399_ = v_v_2395_;
goto v___jp_2398_;
}
v___jp_2398_:
{
lean_object* v___x_2400_; lean_object* v___x_2402_; 
v___x_2400_ = lean_array_fset(v_xs_x27_2397_, v___x_2389_, v___y_2399_);
lean_dec(v___x_2389_);
if (v_isShared_2382_ == 0)
{
lean_ctor_set(v___x_2381_, 1, v___x_2400_);
v___x_2402_ = v___x_2381_;
goto v_reusejp_2401_;
}
else
{
lean_object* v_reuseFailAlloc_2403_; 
v_reuseFailAlloc_2403_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2403_, 0, v_root_2375_);
lean_ctor_set(v_reuseFailAlloc_2403_, 1, v___x_2400_);
lean_ctor_set(v_reuseFailAlloc_2403_, 2, v_size_2377_);
lean_ctor_set(v_reuseFailAlloc_2403_, 3, v_tailOff_2379_);
lean_ctor_set_usize(v_reuseFailAlloc_2403_, 4, v_shift_2378_);
v___x_2402_ = v_reuseFailAlloc_2403_;
goto v_reusejp_2401_;
}
v_reusejp_2401_:
{
return v___x_2402_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2___boxed(lean_object* v_y_2407_, lean_object* v_t_2408_, lean_object* v_i_2409_){
_start:
{
lean_object* v_res_2410_; 
v_res_2410_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2(v_y_2407_, v_t_2408_, v_i_2409_);
lean_dec(v_i_2409_);
return v_res_2410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_addOcc___lam__0(lean_object* v_a_2411_, lean_object* v_y_2412_, lean_object* v_x_2413_, lean_object* v_s_2414_){
_start:
{
lean_object* v_structs_2415_; lean_object* v_typeIdOf_2416_; lean_object* v_exprToStructId_2417_; lean_object* v_exprToStructIdEntries_2418_; lean_object* v_forbiddenNatModules_2419_; lean_object* v_natStructs_2420_; lean_object* v_natTypeIdOf_2421_; lean_object* v_exprToNatStructId_2422_; lean_object* v___x_2423_; uint8_t v___x_2424_; 
v_structs_2415_ = lean_ctor_get(v_s_2414_, 0);
v_typeIdOf_2416_ = lean_ctor_get(v_s_2414_, 1);
v_exprToStructId_2417_ = lean_ctor_get(v_s_2414_, 2);
v_exprToStructIdEntries_2418_ = lean_ctor_get(v_s_2414_, 3);
v_forbiddenNatModules_2419_ = lean_ctor_get(v_s_2414_, 4);
v_natStructs_2420_ = lean_ctor_get(v_s_2414_, 5);
v_natTypeIdOf_2421_ = lean_ctor_get(v_s_2414_, 6);
v_exprToNatStructId_2422_ = lean_ctor_get(v_s_2414_, 7);
v___x_2423_ = lean_array_get_size(v_structs_2415_);
v___x_2424_ = lean_nat_dec_lt(v_a_2411_, v___x_2423_);
if (v___x_2424_ == 0)
{
lean_dec(v_y_2412_);
return v_s_2414_;
}
else
{
lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2486_; 
lean_inc_ref(v_exprToNatStructId_2422_);
lean_inc_ref(v_natTypeIdOf_2421_);
lean_inc_ref(v_natStructs_2420_);
lean_inc_ref(v_forbiddenNatModules_2419_);
lean_inc_ref(v_exprToStructIdEntries_2418_);
lean_inc_ref(v_exprToStructId_2417_);
lean_inc_ref(v_typeIdOf_2416_);
lean_inc_ref(v_structs_2415_);
v_isSharedCheck_2486_ = !lean_is_exclusive(v_s_2414_);
if (v_isSharedCheck_2486_ == 0)
{
lean_object* v_unused_2487_; lean_object* v_unused_2488_; lean_object* v_unused_2489_; lean_object* v_unused_2490_; lean_object* v_unused_2491_; lean_object* v_unused_2492_; lean_object* v_unused_2493_; lean_object* v_unused_2494_; 
v_unused_2487_ = lean_ctor_get(v_s_2414_, 7);
lean_dec(v_unused_2487_);
v_unused_2488_ = lean_ctor_get(v_s_2414_, 6);
lean_dec(v_unused_2488_);
v_unused_2489_ = lean_ctor_get(v_s_2414_, 5);
lean_dec(v_unused_2489_);
v_unused_2490_ = lean_ctor_get(v_s_2414_, 4);
lean_dec(v_unused_2490_);
v_unused_2491_ = lean_ctor_get(v_s_2414_, 3);
lean_dec(v_unused_2491_);
v_unused_2492_ = lean_ctor_get(v_s_2414_, 2);
lean_dec(v_unused_2492_);
v_unused_2493_ = lean_ctor_get(v_s_2414_, 1);
lean_dec(v_unused_2493_);
v_unused_2494_ = lean_ctor_get(v_s_2414_, 0);
lean_dec(v_unused_2494_);
v___x_2426_ = v_s_2414_;
v_isShared_2427_ = v_isSharedCheck_2486_;
goto v_resetjp_2425_;
}
else
{
lean_dec(v_s_2414_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2486_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
lean_object* v_v_2428_; lean_object* v_id_2429_; lean_object* v_ringId_x3f_2430_; lean_object* v_type_2431_; lean_object* v_u_2432_; lean_object* v_intModuleInst_2433_; lean_object* v_leInst_x3f_2434_; lean_object* v_ltInst_x3f_2435_; lean_object* v_lawfulOrderLTInst_x3f_2436_; lean_object* v_isPreorderInst_x3f_2437_; lean_object* v_orderedAddInst_x3f_2438_; lean_object* v_isLinearInst_x3f_2439_; lean_object* v_noNatDivInst_x3f_2440_; lean_object* v_ringInst_x3f_2441_; lean_object* v_commRingInst_x3f_2442_; lean_object* v_orderedRingInst_x3f_2443_; lean_object* v_fieldInst_x3f_2444_; lean_object* v_charInst_x3f_2445_; lean_object* v_zero_2446_; lean_object* v_ofNatZero_2447_; lean_object* v_one_x3f_2448_; lean_object* v_leFn_x3f_2449_; lean_object* v_ltFn_x3f_2450_; lean_object* v_addFn_2451_; lean_object* v_zsmulFn_2452_; lean_object* v_nsmulFn_2453_; lean_object* v_zsmulFn_x3f_2454_; lean_object* v_nsmulFn_x3f_2455_; lean_object* v_homomulFn_x3f_2456_; lean_object* v_subFn_2457_; lean_object* v_negFn_2458_; lean_object* v_vars_2459_; lean_object* v_varMap_2460_; lean_object* v_lowers_2461_; lean_object* v_uppers_2462_; lean_object* v_diseqs_2463_; lean_object* v_assignment_2464_; uint8_t v_caseSplits_2465_; lean_object* v_conflict_x3f_2466_; lean_object* v_diseqSplits_2467_; lean_object* v_elimEqs_2468_; lean_object* v_elimStack_2469_; lean_object* v_occurs_2470_; lean_object* v_ignored_2471_; lean_object* v___x_2473_; uint8_t v_isShared_2474_; uint8_t v_isSharedCheck_2485_; 
v_v_2428_ = lean_array_fget(v_structs_2415_, v_a_2411_);
v_id_2429_ = lean_ctor_get(v_v_2428_, 0);
v_ringId_x3f_2430_ = lean_ctor_get(v_v_2428_, 1);
v_type_2431_ = lean_ctor_get(v_v_2428_, 2);
v_u_2432_ = lean_ctor_get(v_v_2428_, 3);
v_intModuleInst_2433_ = lean_ctor_get(v_v_2428_, 4);
v_leInst_x3f_2434_ = lean_ctor_get(v_v_2428_, 5);
v_ltInst_x3f_2435_ = lean_ctor_get(v_v_2428_, 6);
v_lawfulOrderLTInst_x3f_2436_ = lean_ctor_get(v_v_2428_, 7);
v_isPreorderInst_x3f_2437_ = lean_ctor_get(v_v_2428_, 8);
v_orderedAddInst_x3f_2438_ = lean_ctor_get(v_v_2428_, 9);
v_isLinearInst_x3f_2439_ = lean_ctor_get(v_v_2428_, 10);
v_noNatDivInst_x3f_2440_ = lean_ctor_get(v_v_2428_, 11);
v_ringInst_x3f_2441_ = lean_ctor_get(v_v_2428_, 12);
v_commRingInst_x3f_2442_ = lean_ctor_get(v_v_2428_, 13);
v_orderedRingInst_x3f_2443_ = lean_ctor_get(v_v_2428_, 14);
v_fieldInst_x3f_2444_ = lean_ctor_get(v_v_2428_, 15);
v_charInst_x3f_2445_ = lean_ctor_get(v_v_2428_, 16);
v_zero_2446_ = lean_ctor_get(v_v_2428_, 17);
v_ofNatZero_2447_ = lean_ctor_get(v_v_2428_, 18);
v_one_x3f_2448_ = lean_ctor_get(v_v_2428_, 19);
v_leFn_x3f_2449_ = lean_ctor_get(v_v_2428_, 20);
v_ltFn_x3f_2450_ = lean_ctor_get(v_v_2428_, 21);
v_addFn_2451_ = lean_ctor_get(v_v_2428_, 22);
v_zsmulFn_2452_ = lean_ctor_get(v_v_2428_, 23);
v_nsmulFn_2453_ = lean_ctor_get(v_v_2428_, 24);
v_zsmulFn_x3f_2454_ = lean_ctor_get(v_v_2428_, 25);
v_nsmulFn_x3f_2455_ = lean_ctor_get(v_v_2428_, 26);
v_homomulFn_x3f_2456_ = lean_ctor_get(v_v_2428_, 27);
v_subFn_2457_ = lean_ctor_get(v_v_2428_, 28);
v_negFn_2458_ = lean_ctor_get(v_v_2428_, 29);
v_vars_2459_ = lean_ctor_get(v_v_2428_, 30);
v_varMap_2460_ = lean_ctor_get(v_v_2428_, 31);
v_lowers_2461_ = lean_ctor_get(v_v_2428_, 32);
v_uppers_2462_ = lean_ctor_get(v_v_2428_, 33);
v_diseqs_2463_ = lean_ctor_get(v_v_2428_, 34);
v_assignment_2464_ = lean_ctor_get(v_v_2428_, 35);
v_caseSplits_2465_ = lean_ctor_get_uint8(v_v_2428_, sizeof(void*)*42);
v_conflict_x3f_2466_ = lean_ctor_get(v_v_2428_, 36);
v_diseqSplits_2467_ = lean_ctor_get(v_v_2428_, 37);
v_elimEqs_2468_ = lean_ctor_get(v_v_2428_, 38);
v_elimStack_2469_ = lean_ctor_get(v_v_2428_, 39);
v_occurs_2470_ = lean_ctor_get(v_v_2428_, 40);
v_ignored_2471_ = lean_ctor_get(v_v_2428_, 41);
v_isSharedCheck_2485_ = !lean_is_exclusive(v_v_2428_);
if (v_isSharedCheck_2485_ == 0)
{
v___x_2473_ = v_v_2428_;
v_isShared_2474_ = v_isSharedCheck_2485_;
goto v_resetjp_2472_;
}
else
{
lean_inc(v_ignored_2471_);
lean_inc(v_occurs_2470_);
lean_inc(v_elimStack_2469_);
lean_inc(v_elimEqs_2468_);
lean_inc(v_diseqSplits_2467_);
lean_inc(v_conflict_x3f_2466_);
lean_inc(v_assignment_2464_);
lean_inc(v_diseqs_2463_);
lean_inc(v_uppers_2462_);
lean_inc(v_lowers_2461_);
lean_inc(v_varMap_2460_);
lean_inc(v_vars_2459_);
lean_inc(v_negFn_2458_);
lean_inc(v_subFn_2457_);
lean_inc(v_homomulFn_x3f_2456_);
lean_inc(v_nsmulFn_x3f_2455_);
lean_inc(v_zsmulFn_x3f_2454_);
lean_inc(v_nsmulFn_2453_);
lean_inc(v_zsmulFn_2452_);
lean_inc(v_addFn_2451_);
lean_inc(v_ltFn_x3f_2450_);
lean_inc(v_leFn_x3f_2449_);
lean_inc(v_one_x3f_2448_);
lean_inc(v_ofNatZero_2447_);
lean_inc(v_zero_2446_);
lean_inc(v_charInst_x3f_2445_);
lean_inc(v_fieldInst_x3f_2444_);
lean_inc(v_orderedRingInst_x3f_2443_);
lean_inc(v_commRingInst_x3f_2442_);
lean_inc(v_ringInst_x3f_2441_);
lean_inc(v_noNatDivInst_x3f_2440_);
lean_inc(v_isLinearInst_x3f_2439_);
lean_inc(v_orderedAddInst_x3f_2438_);
lean_inc(v_isPreorderInst_x3f_2437_);
lean_inc(v_lawfulOrderLTInst_x3f_2436_);
lean_inc(v_ltInst_x3f_2435_);
lean_inc(v_leInst_x3f_2434_);
lean_inc(v_intModuleInst_2433_);
lean_inc(v_u_2432_);
lean_inc(v_type_2431_);
lean_inc(v_ringId_x3f_2430_);
lean_inc(v_id_2429_);
lean_dec(v_v_2428_);
v___x_2473_ = lean_box(0);
v_isShared_2474_ = v_isSharedCheck_2485_;
goto v_resetjp_2472_;
}
v_resetjp_2472_:
{
lean_object* v___x_2475_; lean_object* v_xs_x27_2476_; lean_object* v___x_2477_; lean_object* v___x_2479_; 
v___x_2475_ = lean_box(0);
v_xs_x27_2476_ = lean_array_fset(v_structs_2415_, v_a_2411_, v___x_2475_);
v___x_2477_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2(v_y_2412_, v_occurs_2470_, v_x_2413_);
if (v_isShared_2474_ == 0)
{
lean_ctor_set(v___x_2473_, 40, v___x_2477_);
v___x_2479_ = v___x_2473_;
goto v_reusejp_2478_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v_id_2429_);
lean_ctor_set(v_reuseFailAlloc_2484_, 1, v_ringId_x3f_2430_);
lean_ctor_set(v_reuseFailAlloc_2484_, 2, v_type_2431_);
lean_ctor_set(v_reuseFailAlloc_2484_, 3, v_u_2432_);
lean_ctor_set(v_reuseFailAlloc_2484_, 4, v_intModuleInst_2433_);
lean_ctor_set(v_reuseFailAlloc_2484_, 5, v_leInst_x3f_2434_);
lean_ctor_set(v_reuseFailAlloc_2484_, 6, v_ltInst_x3f_2435_);
lean_ctor_set(v_reuseFailAlloc_2484_, 7, v_lawfulOrderLTInst_x3f_2436_);
lean_ctor_set(v_reuseFailAlloc_2484_, 8, v_isPreorderInst_x3f_2437_);
lean_ctor_set(v_reuseFailAlloc_2484_, 9, v_orderedAddInst_x3f_2438_);
lean_ctor_set(v_reuseFailAlloc_2484_, 10, v_isLinearInst_x3f_2439_);
lean_ctor_set(v_reuseFailAlloc_2484_, 11, v_noNatDivInst_x3f_2440_);
lean_ctor_set(v_reuseFailAlloc_2484_, 12, v_ringInst_x3f_2441_);
lean_ctor_set(v_reuseFailAlloc_2484_, 13, v_commRingInst_x3f_2442_);
lean_ctor_set(v_reuseFailAlloc_2484_, 14, v_orderedRingInst_x3f_2443_);
lean_ctor_set(v_reuseFailAlloc_2484_, 15, v_fieldInst_x3f_2444_);
lean_ctor_set(v_reuseFailAlloc_2484_, 16, v_charInst_x3f_2445_);
lean_ctor_set(v_reuseFailAlloc_2484_, 17, v_zero_2446_);
lean_ctor_set(v_reuseFailAlloc_2484_, 18, v_ofNatZero_2447_);
lean_ctor_set(v_reuseFailAlloc_2484_, 19, v_one_x3f_2448_);
lean_ctor_set(v_reuseFailAlloc_2484_, 20, v_leFn_x3f_2449_);
lean_ctor_set(v_reuseFailAlloc_2484_, 21, v_ltFn_x3f_2450_);
lean_ctor_set(v_reuseFailAlloc_2484_, 22, v_addFn_2451_);
lean_ctor_set(v_reuseFailAlloc_2484_, 23, v_zsmulFn_2452_);
lean_ctor_set(v_reuseFailAlloc_2484_, 24, v_nsmulFn_2453_);
lean_ctor_set(v_reuseFailAlloc_2484_, 25, v_zsmulFn_x3f_2454_);
lean_ctor_set(v_reuseFailAlloc_2484_, 26, v_nsmulFn_x3f_2455_);
lean_ctor_set(v_reuseFailAlloc_2484_, 27, v_homomulFn_x3f_2456_);
lean_ctor_set(v_reuseFailAlloc_2484_, 28, v_subFn_2457_);
lean_ctor_set(v_reuseFailAlloc_2484_, 29, v_negFn_2458_);
lean_ctor_set(v_reuseFailAlloc_2484_, 30, v_vars_2459_);
lean_ctor_set(v_reuseFailAlloc_2484_, 31, v_varMap_2460_);
lean_ctor_set(v_reuseFailAlloc_2484_, 32, v_lowers_2461_);
lean_ctor_set(v_reuseFailAlloc_2484_, 33, v_uppers_2462_);
lean_ctor_set(v_reuseFailAlloc_2484_, 34, v_diseqs_2463_);
lean_ctor_set(v_reuseFailAlloc_2484_, 35, v_assignment_2464_);
lean_ctor_set(v_reuseFailAlloc_2484_, 36, v_conflict_x3f_2466_);
lean_ctor_set(v_reuseFailAlloc_2484_, 37, v_diseqSplits_2467_);
lean_ctor_set(v_reuseFailAlloc_2484_, 38, v_elimEqs_2468_);
lean_ctor_set(v_reuseFailAlloc_2484_, 39, v_elimStack_2469_);
lean_ctor_set(v_reuseFailAlloc_2484_, 40, v___x_2477_);
lean_ctor_set(v_reuseFailAlloc_2484_, 41, v_ignored_2471_);
lean_ctor_set_uint8(v_reuseFailAlloc_2484_, sizeof(void*)*42, v_caseSplits_2465_);
v___x_2479_ = v_reuseFailAlloc_2484_;
goto v_reusejp_2478_;
}
v_reusejp_2478_:
{
lean_object* v___x_2480_; lean_object* v___x_2482_; 
v___x_2480_ = lean_array_fset(v_xs_x27_2476_, v_a_2411_, v___x_2479_);
if (v_isShared_2427_ == 0)
{
lean_ctor_set(v___x_2426_, 0, v___x_2480_);
v___x_2482_ = v___x_2426_;
goto v_reusejp_2481_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v___x_2480_);
lean_ctor_set(v_reuseFailAlloc_2483_, 1, v_typeIdOf_2416_);
lean_ctor_set(v_reuseFailAlloc_2483_, 2, v_exprToStructId_2417_);
lean_ctor_set(v_reuseFailAlloc_2483_, 3, v_exprToStructIdEntries_2418_);
lean_ctor_set(v_reuseFailAlloc_2483_, 4, v_forbiddenNatModules_2419_);
lean_ctor_set(v_reuseFailAlloc_2483_, 5, v_natStructs_2420_);
lean_ctor_set(v_reuseFailAlloc_2483_, 6, v_natTypeIdOf_2421_);
lean_ctor_set(v_reuseFailAlloc_2483_, 7, v_exprToNatStructId_2422_);
v___x_2482_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2481_;
}
v_reusejp_2481_:
{
return v___x_2482_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_addOcc___lam__0___boxed(lean_object* v_a_2495_, lean_object* v_y_2496_, lean_object* v_x_2497_, lean_object* v_s_2498_){
_start:
{
lean_object* v_res_2499_; 
v_res_2499_ = l_Lean_Meta_Grind_Arith_Linear_addOcc___lam__0(v_a_2495_, v_y_2496_, v_x_2497_, v_s_2498_);
lean_dec(v_x_2497_);
lean_dec(v_a_2495_);
return v_res_2499_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Linear_addOcc(lean_object* v_x_2500_, lean_object* v_y_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_){
_start:
{
lean_object* v___f_2514_; lean_object* v___x_2515_; 
lean_inc(v_x_2500_);
lean_inc(v_y_2501_);
lean_inc(v_a_2502_);
v___f_2514_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_addOcc___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2514_, 0, v_a_2502_);
lean_closure_set(v___f_2514_, 1, v_y_2501_);
lean_closure_set(v___f_2514_, 2, v_x_2500_);
v___x_2515_ = l_Lean_Meta_Grind_Arith_Linear_getOccursOf(v_x_2500_, v_a_2502_, v_a_2503_, v_a_2504_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_, v_a_2510_, v_a_2511_, v_a_2512_);
lean_dec(v_x_2500_);
if (lean_obj_tag(v___x_2515_) == 0)
{
lean_object* v_a_2516_; lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2527_; 
v_a_2516_ = lean_ctor_get(v___x_2515_, 0);
v_isSharedCheck_2527_ = !lean_is_exclusive(v___x_2515_);
if (v_isSharedCheck_2527_ == 0)
{
v___x_2518_ = v___x_2515_;
v_isShared_2519_ = v_isSharedCheck_2527_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_a_2516_);
lean_dec(v___x_2515_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2527_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
uint8_t v___x_2520_; 
v___x_2520_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg(v_y_2501_, v_a_2516_);
lean_dec(v_a_2516_);
lean_dec(v_y_2501_);
if (v___x_2520_ == 0)
{
lean_object* v___x_2521_; lean_object* v___x_2522_; 
lean_del_object(v___x_2518_);
v___x_2521_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2522_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2521_, v___f_2514_, v_a_2503_);
return v___x_2522_;
}
else
{
lean_object* v___x_2523_; lean_object* v___x_2525_; 
lean_dec_ref(v___f_2514_);
v___x_2523_ = lean_box(0);
if (v_isShared_2519_ == 0)
{
lean_ctor_set(v___x_2518_, 0, v___x_2523_);
v___x_2525_ = v___x_2518_;
goto v_reusejp_2524_;
}
else
{
lean_object* v_reuseFailAlloc_2526_; 
v_reuseFailAlloc_2526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2526_, 0, v___x_2523_);
v___x_2525_ = v_reuseFailAlloc_2526_;
goto v_reusejp_2524_;
}
v_reusejp_2524_:
{
return v___x_2525_;
}
}
}
}
else
{
lean_object* v_a_2528_; lean_object* v___x_2530_; uint8_t v_isShared_2531_; uint8_t v_isSharedCheck_2535_; 
lean_dec_ref(v___f_2514_);
lean_dec(v_y_2501_);
v_a_2528_ = lean_ctor_get(v___x_2515_, 0);
v_isSharedCheck_2535_ = !lean_is_exclusive(v___x_2515_);
if (v_isSharedCheck_2535_ == 0)
{
v___x_2530_ = v___x_2515_;
v_isShared_2531_ = v_isSharedCheck_2535_;
goto v_resetjp_2529_;
}
else
{
lean_inc(v_a_2528_);
lean_dec(v___x_2515_);
v___x_2530_ = lean_box(0);
v_isShared_2531_ = v_isSharedCheck_2535_;
goto v_resetjp_2529_;
}
v_resetjp_2529_:
{
lean_object* v___x_2533_; 
if (v_isShared_2531_ == 0)
{
v___x_2533_ = v___x_2530_;
goto v_reusejp_2532_;
}
else
{
lean_object* v_reuseFailAlloc_2534_; 
v_reuseFailAlloc_2534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2534_, 0, v_a_2528_);
v___x_2533_ = v_reuseFailAlloc_2534_;
goto v_reusejp_2532_;
}
v_reusejp_2532_:
{
return v___x_2533_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Linear_addOcc_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2500_ = stack[0].m_obj;
lean_object* v_y_2501_ = stack[1].m_obj;
lean_object* v_a_2502_ = stack[2].m_obj;
lean_object* v_a_2503_ = stack[3].m_obj;
lean_object* v_a_2504_ = stack[4].m_obj;
lean_object* v_a_2505_ = stack[5].m_obj;
lean_object* v_a_2506_ = stack[6].m_obj;
lean_object* v_a_2507_ = stack[7].m_obj;
lean_object* v_a_2508_ = stack[8].m_obj;
lean_object* v_a_2509_ = stack[9].m_obj;
lean_object* v_a_2510_ = stack[10].m_obj;
lean_object* v_a_2511_ = stack[11].m_obj;
lean_object* v_a_2512_ = stack[12].m_obj;
lean_object* v_res_2536_;
v_res_2536_ = l_Lean_Meta_Grind_Arith_Linear_addOcc(v_x_2500_, v_y_2501_, v_a_2502_, v_a_2503_, v_a_2504_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_, v_a_2510_, v_a_2511_, v_a_2512_);
stack->m_obj
 = v_res_2536_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_addOcc___boxed(lean_object* v_x_2537_, lean_object* v_y_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_){
_start:
{
lean_object* v_res_2551_; 
v_res_2551_ = l_Lean_Meta_Grind_Arith_Linear_addOcc(v_x_2537_, v_y_2538_, v_a_2539_, v_a_2540_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_);
lean_dec(v_a_2549_);
lean_dec_ref(v_a_2548_);
lean_dec(v_a_2547_);
lean_dec_ref(v_a_2546_);
lean_dec(v_a_2545_);
lean_dec_ref(v_a_2544_);
lean_dec(v_a_2543_);
lean_dec_ref(v_a_2542_);
lean_dec(v_a_2541_);
lean_dec(v_a_2540_);
lean_dec(v_a_2539_);
return v_res_2551_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0(lean_object* v_00_u03b2_2552_, lean_object* v_k_2553_, lean_object* v_t_2554_){
_start:
{
uint8_t v___x_2555_; 
v___x_2555_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg(v_k_2553_, v_t_2554_);
return v___x_2555_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_2553_ = stack[1].m_obj;
lean_object* v_t_2554_ = stack[2].m_obj;
uint8_t v_res_2556_;
v_res_2556_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0(lean_box(0), v_k_2553_, v_t_2554_);
stack->m_num = v_res_2556_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___boxed(lean_object* v_00_u03b2_2557_, lean_object* v_k_2558_, lean_object* v_t_2559_){
_start:
{
uint8_t v_res_2560_; lean_object* v_r_2561_; 
v_res_2560_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0(v_00_u03b2_2557_, v_k_2558_, v_t_2559_);
lean_dec(v_t_2559_);
lean_dec(v_k_2558_);
v_r_2561_ = lean_box(v_res_2560_);
return v_r_2561_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1(lean_object* v_00_u03b2_2562_, lean_object* v_k_2563_, lean_object* v_v_2564_, lean_object* v_t_2565_, lean_object* v_hl_2566_){
_start:
{
lean_object* v___x_2567_; 
v___x_2567_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1___redArg(v_k_2563_, v_v_2564_, v_t_2565_);
return v___x_2567_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_updateOccs_go(lean_object* v_y_2568_, lean_object* v_p_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_){
_start:
{
if (lean_obj_tag(v_p_2569_) == 1)
{
lean_object* v_v_2582_; lean_object* v_p_2583_; lean_object* v___x_2584_; 
v_v_2582_ = lean_ctor_get(v_p_2569_, 1);
lean_inc(v_v_2582_);
v_p_2583_ = lean_ctor_get(v_p_2569_, 2);
lean_inc(v_p_2583_);
lean_dec_ref_known(v_p_2569_, 3);
lean_inc(v_y_2568_);
v___x_2584_ = l_Lean_Meta_Grind_Arith_Linear_addOcc(v_v_2582_, v_y_2568_, v_a_2570_, v_a_2571_, v_a_2572_, v_a_2573_, v_a_2574_, v_a_2575_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_);
if (lean_obj_tag(v___x_2584_) == 0)
{
lean_dec_ref_known(v___x_2584_, 1);
v_p_2569_ = v_p_2583_;
goto _start;
}
else
{
lean_dec(v_p_2583_);
lean_dec(v_y_2568_);
return v___x_2584_;
}
}
else
{
lean_object* v___x_2586_; lean_object* v___x_2587_; 
lean_dec(v_p_2569_);
lean_dec(v_y_2568_);
v___x_2586_ = lean_box(0);
v___x_2587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2587_, 0, v___x_2586_);
return v___x_2587_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_updateOccs_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_y_2568_ = stack[0].m_obj;
lean_object* v_p_2569_ = stack[1].m_obj;
lean_object* v_a_2570_ = stack[2].m_obj;
lean_object* v_a_2571_ = stack[3].m_obj;
lean_object* v_a_2572_ = stack[4].m_obj;
lean_object* v_a_2573_ = stack[5].m_obj;
lean_object* v_a_2574_ = stack[6].m_obj;
lean_object* v_a_2575_ = stack[7].m_obj;
lean_object* v_a_2576_ = stack[8].m_obj;
lean_object* v_a_2577_ = stack[9].m_obj;
lean_object* v_a_2578_ = stack[10].m_obj;
lean_object* v_a_2579_ = stack[11].m_obj;
lean_object* v_a_2580_ = stack[12].m_obj;
lean_object* v_res_2588_;
v_res_2588_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_updateOccs_go(v_y_2568_, v_p_2569_, v_a_2570_, v_a_2571_, v_a_2572_, v_a_2573_, v_a_2574_, v_a_2575_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_);
stack->m_obj
 = v_res_2588_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_updateOccs_go___boxed(lean_object* v_y_2589_, lean_object* v_p_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_, lean_object* v_a_2594_, lean_object* v_a_2595_, lean_object* v_a_2596_, lean_object* v_a_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_){
_start:
{
lean_object* v_res_2603_; 
v_res_2603_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_updateOccs_go(v_y_2589_, v_p_2590_, v_a_2591_, v_a_2592_, v_a_2593_, v_a_2594_, v_a_2595_, v_a_2596_, v_a_2597_, v_a_2598_, v_a_2599_, v_a_2600_, v_a_2601_);
lean_dec(v_a_2601_);
lean_dec_ref(v_a_2600_);
lean_dec(v_a_2599_);
lean_dec_ref(v_a_2598_);
lean_dec(v_a_2597_);
lean_dec_ref(v_a_2596_);
lean_dec(v_a_2595_);
lean_dec_ref(v_a_2594_);
lean_dec(v_a_2593_);
lean_dec(v_a_2592_);
lean_dec(v_a_2591_);
return v_res_2603_;
}
}
static lean_object* _init_l_Lean_Grind_Linarith_Poly_updateOccs___closed__1(void){
_start:
{
lean_object* v___x_2605_; lean_object* v___x_2606_; 
v___x_2605_ = ((lean_object*)(l_Lean_Grind_Linarith_Poly_updateOccs___closed__0));
v___x_2606_ = l_Lean_stringToMessageData(v___x_2605_);
return v___x_2606_;
}
}
lean_object* l_Lean_Grind_Linarith_Poly_updateOccs(lean_object* v_p_2607_, lean_object* v_a_2608_, lean_object* v_a_2609_, lean_object* v_a_2610_, lean_object* v_a_2611_, lean_object* v_a_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_){
_start:
{
if (lean_obj_tag(v_p_2607_) == 1)
{
lean_object* v_v_2620_; lean_object* v_p_2621_; lean_object* v___x_2622_; 
v_v_2620_ = lean_ctor_get(v_p_2607_, 1);
lean_inc(v_v_2620_);
v_p_2621_ = lean_ctor_get(v_p_2607_, 2);
lean_inc(v_p_2621_);
lean_dec_ref_known(v_p_2607_, 3);
v___x_2622_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_updateOccs_go(v_v_2620_, v_p_2621_, v_a_2608_, v_a_2609_, v_a_2610_, v_a_2611_, v_a_2612_, v_a_2613_, v_a_2614_, v_a_2615_, v_a_2616_, v_a_2617_, v_a_2618_);
return v___x_2622_;
}
else
{
lean_object* v___x_2623_; lean_object* v___x_2624_; 
lean_dec(v_p_2607_);
v___x_2623_ = lean_obj_once(&l_Lean_Grind_Linarith_Poly_updateOccs___closed__1, &l_Lean_Grind_Linarith_Poly_updateOccs___closed__1_once, _init_l_Lean_Grind_Linarith_Poly_updateOccs___closed__1);
v___x_2624_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_2623_, v_a_2615_, v_a_2616_, v_a_2617_, v_a_2618_);
return v___x_2624_;
}
}
}
LEAN_EXPORT void l_Lean_Grind_Linarith_Poly_updateOccs_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_2607_ = stack[0].m_obj;
lean_object* v_a_2608_ = stack[1].m_obj;
lean_object* v_a_2609_ = stack[2].m_obj;
lean_object* v_a_2610_ = stack[3].m_obj;
lean_object* v_a_2611_ = stack[4].m_obj;
lean_object* v_a_2612_ = stack[5].m_obj;
lean_object* v_a_2613_ = stack[6].m_obj;
lean_object* v_a_2614_ = stack[7].m_obj;
lean_object* v_a_2615_ = stack[8].m_obj;
lean_object* v_a_2616_ = stack[9].m_obj;
lean_object* v_a_2617_ = stack[10].m_obj;
lean_object* v_a_2618_ = stack[11].m_obj;
lean_object* v_res_2625_;
v_res_2625_ = l_Lean_Grind_Linarith_Poly_updateOccs(v_p_2607_, v_a_2608_, v_a_2609_, v_a_2610_, v_a_2611_, v_a_2612_, v_a_2613_, v_a_2614_, v_a_2615_, v_a_2616_, v_a_2617_, v_a_2618_);
stack->m_obj
 = v_res_2625_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_updateOccs___boxed(lean_object* v_p_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_){
_start:
{
lean_object* v_res_2639_; 
v_res_2639_ = l_Lean_Grind_Linarith_Poly_updateOccs(v_p_2626_, v_a_2627_, v_a_2628_, v_a_2629_, v_a_2630_, v_a_2631_, v_a_2632_, v_a_2633_, v_a_2634_, v_a_2635_, v_a_2636_, v_a_2637_);
lean_dec(v_a_2637_);
lean_dec_ref(v_a_2636_);
lean_dec(v_a_2635_);
lean_dec_ref(v_a_2634_);
lean_dec(v_a_2633_);
lean_dec_ref(v_a_2632_);
lean_dec(v_a_2631_);
lean_dec_ref(v_a_2630_);
lean_dec(v_a_2629_);
lean_dec(v_a_2628_);
lean_dec(v_a_2627_);
return v_res_2639_;
}
}
lean_object* l_Lean_Grind_Linarith_Poly_findVarToSubst(lean_object* v_p_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_){
_start:
{
if (lean_obj_tag(v_p_2640_) == 0)
{
lean_object* v___x_2653_; lean_object* v___x_2654_; 
v___x_2653_ = lean_box(0);
v___x_2654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2654_, 0, v___x_2653_);
return v___x_2654_;
}
else
{
lean_object* v_k_2655_; lean_object* v_v_2656_; lean_object* v_p_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; 
v_k_2655_ = lean_ctor_get(v_p_2640_, 0);
v_v_2656_ = lean_ctor_get(v_p_2640_, 1);
v_p_2657_ = lean_ctor_get(v_p_2640_, 2);
v___x_2658_ = lean_box(0);
v___x_2659_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_2641_, v_a_2642_, v_a_2643_, v_a_2644_, v_a_2645_, v_a_2646_, v_a_2647_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_);
if (lean_obj_tag(v___x_2659_) == 0)
{
lean_object* v_a_2660_; lean_object* v___x_2662_; uint8_t v_isShared_2663_; uint8_t v_isSharedCheck_2685_; 
v_a_2660_ = lean_ctor_get(v___x_2659_, 0);
v_isSharedCheck_2685_ = !lean_is_exclusive(v___x_2659_);
if (v_isSharedCheck_2685_ == 0)
{
v___x_2662_ = v___x_2659_;
v_isShared_2663_ = v_isSharedCheck_2685_;
goto v_resetjp_2661_;
}
else
{
lean_inc(v_a_2660_);
lean_dec(v___x_2659_);
v___x_2662_ = lean_box(0);
v_isShared_2663_ = v_isSharedCheck_2685_;
goto v_resetjp_2661_;
}
v_resetjp_2661_:
{
lean_object* v___y_2665_; lean_object* v_elimEqs_2680_; lean_object* v_size_2681_; uint8_t v___x_2682_; 
v_elimEqs_2680_ = lean_ctor_get(v_a_2660_, 38);
lean_inc_ref(v_elimEqs_2680_);
lean_dec(v_a_2660_);
v_size_2681_ = lean_ctor_get(v_elimEqs_2680_, 2);
v___x_2682_ = lean_nat_dec_lt(v_v_2656_, v_size_2681_);
if (v___x_2682_ == 0)
{
lean_object* v___x_2683_; 
lean_dec_ref(v_elimEqs_2680_);
v___x_2683_ = l_outOfBounds___redArg(v___x_2658_);
v___y_2665_ = v___x_2683_;
goto v___jp_2664_;
}
else
{
lean_object* v___x_2684_; 
v___x_2684_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2658_, v_elimEqs_2680_, v_v_2656_);
lean_dec_ref(v_elimEqs_2680_);
v___y_2665_ = v___x_2684_;
goto v___jp_2664_;
}
v___jp_2664_:
{
if (lean_obj_tag(v___y_2665_) == 1)
{
lean_object* v_val_2666_; lean_object* v___x_2668_; uint8_t v_isShared_2669_; uint8_t v_isSharedCheck_2678_; 
v_val_2666_ = lean_ctor_get(v___y_2665_, 0);
v_isSharedCheck_2678_ = !lean_is_exclusive(v___y_2665_);
if (v_isSharedCheck_2678_ == 0)
{
v___x_2668_ = v___y_2665_;
v_isShared_2669_ = v_isSharedCheck_2678_;
goto v_resetjp_2667_;
}
else
{
lean_inc(v_val_2666_);
lean_dec(v___y_2665_);
v___x_2668_ = lean_box(0);
v_isShared_2669_ = v_isSharedCheck_2678_;
goto v_resetjp_2667_;
}
v_resetjp_2667_:
{
lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2673_; 
lean_inc(v_v_2656_);
v___x_2670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2670_, 0, v_v_2656_);
lean_ctor_set(v___x_2670_, 1, v_val_2666_);
lean_inc(v_k_2655_);
v___x_2671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2671_, 0, v_k_2655_);
lean_ctor_set(v___x_2671_, 1, v___x_2670_);
if (v_isShared_2669_ == 0)
{
lean_ctor_set(v___x_2668_, 0, v___x_2671_);
v___x_2673_ = v___x_2668_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v___x_2671_);
v___x_2673_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
lean_object* v___x_2675_; 
if (v_isShared_2663_ == 0)
{
lean_ctor_set(v___x_2662_, 0, v___x_2673_);
v___x_2675_ = v___x_2662_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v___x_2673_);
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
lean_dec(v___y_2665_);
lean_del_object(v___x_2662_);
v_p_2640_ = v_p_2657_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2686_; lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2693_; 
v_a_2686_ = lean_ctor_get(v___x_2659_, 0);
v_isSharedCheck_2693_ = !lean_is_exclusive(v___x_2659_);
if (v_isSharedCheck_2693_ == 0)
{
v___x_2688_ = v___x_2659_;
v_isShared_2689_ = v_isSharedCheck_2693_;
goto v_resetjp_2687_;
}
else
{
lean_inc(v_a_2686_);
lean_dec(v___x_2659_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2693_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v___x_2691_; 
if (v_isShared_2689_ == 0)
{
v___x_2691_ = v___x_2688_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_a_2686_);
v___x_2691_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
return v___x_2691_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Grind_Linarith_Poly_findVarToSubst_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_2640_ = stack[0].m_obj;
lean_object* v_a_2641_ = stack[1].m_obj;
lean_object* v_a_2642_ = stack[2].m_obj;
lean_object* v_a_2643_ = stack[3].m_obj;
lean_object* v_a_2644_ = stack[4].m_obj;
lean_object* v_a_2645_ = stack[5].m_obj;
lean_object* v_a_2646_ = stack[6].m_obj;
lean_object* v_a_2647_ = stack[7].m_obj;
lean_object* v_a_2648_ = stack[8].m_obj;
lean_object* v_a_2649_ = stack[9].m_obj;
lean_object* v_a_2650_ = stack[10].m_obj;
lean_object* v_a_2651_ = stack[11].m_obj;
lean_object* v_res_2694_;
v_res_2694_ = l_Lean_Grind_Linarith_Poly_findVarToSubst(v_p_2640_, v_a_2641_, v_a_2642_, v_a_2643_, v_a_2644_, v_a_2645_, v_a_2646_, v_a_2647_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_);
stack->m_obj
 = v_res_2694_;
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_findVarToSubst___boxed(lean_object* v_p_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_){
_start:
{
lean_object* v_res_2708_; 
v_res_2708_ = l_Lean_Grind_Linarith_Poly_findVarToSubst(v_p_2695_, v_a_2696_, v_a_2697_, v_a_2698_, v_a_2699_, v_a_2700_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_);
lean_dec(v_a_2706_);
lean_dec_ref(v_a_2705_);
lean_dec(v_a_2704_);
lean_dec_ref(v_a_2703_);
lean_dec(v_a_2702_);
lean_dec_ref(v_a_2701_);
lean_dec(v_a_2700_);
lean_dec_ref(v_a_2699_);
lean_dec(v_a_2698_);
lean_dec(v_a_2697_);
lean_dec(v_a_2696_);
lean_dec(v_p_2695_);
return v_res_2708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_gcdCoeffsAux(lean_object* v_x_2709_, lean_object* v_x_2710_){
_start:
{
if (lean_obj_tag(v_x_2709_) == 0)
{
return v_x_2710_;
}
else
{
lean_object* v_k_2711_; lean_object* v_p_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; 
v_k_2711_ = lean_ctor_get(v_x_2709_, 0);
v_p_2712_ = lean_ctor_get(v_x_2709_, 2);
v___x_2713_ = lean_nat_to_int(v_x_2710_);
v___x_2714_ = l_Int_gcd(v_k_2711_, v___x_2713_);
lean_dec(v___x_2713_);
v_x_2709_ = v_p_2712_;
v_x_2710_ = v___x_2714_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_gcdCoeffsAux___boxed(lean_object* v_x_2716_, lean_object* v_x_2717_){
_start:
{
lean_object* v_res_2718_; 
v_res_2718_ = l_Lean_Grind_Linarith_Poly_gcdCoeffsAux(v_x_2716_, v_x_2717_);
lean_dec(v_x_2716_);
return v_res_2718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_gcdCoeffs(lean_object* v_p_2719_){
_start:
{
if (lean_obj_tag(v_p_2719_) == 0)
{
lean_object* v___x_2720_; 
v___x_2720_ = lean_unsigned_to_nat(1u);
return v___x_2720_;
}
else
{
lean_object* v_k_2721_; lean_object* v_p_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; 
v_k_2721_ = lean_ctor_get(v_p_2719_, 0);
v_p_2722_ = lean_ctor_get(v_p_2719_, 2);
v___x_2723_ = lean_nat_abs(v_k_2721_);
v___x_2724_ = l_Lean_Grind_Linarith_Poly_gcdCoeffsAux(v_p_2722_, v___x_2723_);
return v___x_2724_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_gcdCoeffs___boxed(lean_object* v_p_2725_){
_start:
{
lean_object* v_res_2726_; 
v_res_2726_ = l_Lean_Grind_Linarith_Poly_gcdCoeffs(v_p_2725_);
lean_dec(v_p_2725_);
return v_res_2726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_div(lean_object* v_p_2727_, lean_object* v_k_2728_){
_start:
{
if (lean_obj_tag(v_p_2727_) == 0)
{
return v_p_2727_;
}
else
{
lean_object* v_k_2729_; lean_object* v_v_2730_; lean_object* v_p_2731_; lean_object* v___x_2733_; uint8_t v_isShared_2734_; uint8_t v_isSharedCheck_2740_; 
v_k_2729_ = lean_ctor_get(v_p_2727_, 0);
v_v_2730_ = lean_ctor_get(v_p_2727_, 1);
v_p_2731_ = lean_ctor_get(v_p_2727_, 2);
v_isSharedCheck_2740_ = !lean_is_exclusive(v_p_2727_);
if (v_isSharedCheck_2740_ == 0)
{
v___x_2733_ = v_p_2727_;
v_isShared_2734_ = v_isSharedCheck_2740_;
goto v_resetjp_2732_;
}
else
{
lean_inc(v_p_2731_);
lean_inc(v_v_2730_);
lean_inc(v_k_2729_);
lean_dec(v_p_2727_);
v___x_2733_ = lean_box(0);
v_isShared_2734_ = v_isSharedCheck_2740_;
goto v_resetjp_2732_;
}
v_resetjp_2732_:
{
lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2738_; 
v___x_2735_ = lean_int_ediv(v_k_2729_, v_k_2728_);
lean_dec(v_k_2729_);
v___x_2736_ = l_Lean_Grind_Linarith_Poly_div(v_p_2731_, v_k_2728_);
if (v_isShared_2734_ == 0)
{
lean_ctor_set(v___x_2733_, 2, v___x_2736_);
lean_ctor_set(v___x_2733_, 0, v___x_2735_);
v___x_2738_ = v___x_2733_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2739_; 
v_reuseFailAlloc_2739_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2739_, 0, v___x_2735_);
lean_ctor_set(v_reuseFailAlloc_2739_, 1, v_v_2730_);
lean_ctor_set(v_reuseFailAlloc_2739_, 2, v___x_2736_);
v___x_2738_ = v_reuseFailAlloc_2739_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
return v___x_2738_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_div___boxed(lean_object* v_p_2741_, lean_object* v_k_2742_){
_start:
{
lean_object* v_res_2743_; 
v_res_2743_ = l_Lean_Grind_Linarith_Poly_div(v_p_2741_, v_k_2742_);
lean_dec(v_k_2742_);
return v_res_2743_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__0(void){
_start:
{
lean_object* v___x_2744_; lean_object* v___x_2745_; 
v___x_2744_ = lean_unsigned_to_nat(1u);
v___x_2745_ = lean_nat_to_int(v___x_2744_);
return v___x_2745_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__1(void){
_start:
{
lean_object* v___x_2746_; lean_object* v___x_2747_; 
v___x_2746_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__0);
v___x_2747_ = lean_int_neg(v___x_2746_);
return v___x_2747_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go(lean_object* v_k_2748_, lean_object* v_x_2749_, lean_object* v_p_2750_){
_start:
{
lean_object* v___x_2751_; uint8_t v___x_2752_; 
v___x_2751_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__0);
v___x_2752_ = lean_int_dec_eq(v_k_2748_, v___x_2751_);
if (v___x_2752_ == 0)
{
lean_object* v___x_2753_; uint8_t v___x_2754_; 
v___x_2753_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__1);
v___x_2754_ = lean_int_dec_eq(v_k_2748_, v___x_2753_);
if (v___x_2754_ == 0)
{
if (lean_obj_tag(v_p_2750_) == 0)
{
lean_object* v___x_2755_; 
v___x_2755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2755_, 0, v_k_2748_);
lean_ctor_set(v___x_2755_, 1, v_x_2749_);
return v___x_2755_;
}
else
{
lean_object* v_k_2756_; lean_object* v_v_2757_; lean_object* v_p_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; uint8_t v___x_2761_; 
v_k_2756_ = lean_ctor_get(v_p_2750_, 0);
lean_inc(v_k_2756_);
v_v_2757_ = lean_ctor_get(v_p_2750_, 1);
lean_inc(v_v_2757_);
v_p_2758_ = lean_ctor_get(v_p_2750_, 2);
lean_inc(v_p_2758_);
lean_dec_ref_known(v_p_2750_, 3);
v___x_2759_ = lean_nat_abs(v_k_2756_);
v___x_2760_ = lean_nat_abs(v_k_2748_);
v___x_2761_ = lean_nat_dec_lt(v___x_2759_, v___x_2760_);
lean_dec(v___x_2760_);
lean_dec(v___x_2759_);
if (v___x_2761_ == 0)
{
lean_dec(v_v_2757_);
lean_dec(v_k_2756_);
v_p_2750_ = v_p_2758_;
goto _start;
}
else
{
lean_dec(v_x_2749_);
lean_dec(v_k_2748_);
v_k_2748_ = v_k_2756_;
v_x_2749_ = v_v_2757_;
v_p_2750_ = v_p_2758_;
goto _start;
}
}
}
else
{
lean_object* v___x_2764_; 
lean_dec(v_p_2750_);
v___x_2764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2764_, 0, v_k_2748_);
lean_ctor_set(v___x_2764_, 1, v_x_2749_);
return v___x_2764_;
}
}
else
{
lean_object* v___x_2765_; 
lean_dec(v_p_2750_);
v___x_2765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2765_, 0, v_k_2748_);
lean_ctor_set(v___x_2765_, 1, v_x_2749_);
return v___x_2765_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_pickVarToElim_x3f(lean_object* v_p_2766_){
_start:
{
if (lean_obj_tag(v_p_2766_) == 0)
{
lean_object* v___x_2767_; 
v___x_2767_ = lean_box(0);
return v___x_2767_;
}
else
{
lean_object* v_k_2768_; lean_object* v_v_2769_; lean_object* v_p_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; 
v_k_2768_ = lean_ctor_get(v_p_2766_, 0);
lean_inc(v_k_2768_);
v_v_2769_ = lean_ctor_get(v_p_2766_, 1);
lean_inc(v_v_2769_);
v_p_2770_ = lean_ctor_get(v_p_2766_, 2);
lean_inc(v_p_2770_);
lean_dec_ref_known(v_p_2766_, 3);
v___x_2771_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go(v_k_2768_, v_v_2769_, v_p_2770_);
v___x_2772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2772_, 0, v___x_2771_);
return v___x_2772_;
}
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Util(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Gcd(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Util(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Gcd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Util(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Util(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Gcd(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Util(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Gcd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Util(builtin);
}
#ifdef __cplusplus
}
#endif
