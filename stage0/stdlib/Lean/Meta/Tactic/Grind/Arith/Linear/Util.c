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
lean_object* l_outOfBounds___redArg(lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getZero(lean_object* v_a_1_, lean_object* v_a_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getZero___boxed(lean_object* v_a_31_, lean_object* v_a_32_, lean_object* v_a_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_, lean_object* v_a_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lean_Meta_Grind_Arith_Linear_getZero(v_a_31_, v_a_32_, v_a_33_, v_a_34_, v_a_35_, v_a_36_, v_a_37_, v_a_38_, v_a_39_, v_a_40_, v_a_41_);
lean_dec(v_a_41_);
lean_dec_ref(v_a_40_);
lean_dec(v_a_39_);
lean_dec_ref(v_a_38_);
lean_dec(v_a_37_);
lean_dec_ref(v_a_36_);
lean_dec(v_a_35_);
lean_dec_ref(v_a_34_);
lean_dec(v_a_33_);
lean_dec(v_a_32_);
lean_dec(v_a_31_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOne(lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_44_, v_a_45_, v_a_46_, v_a_47_, v_a_48_, v_a_49_, v_a_50_, v_a_51_, v_a_52_, v_a_53_, v_a_54_);
if (lean_obj_tag(v___x_56_) == 0)
{
lean_object* v_a_57_; lean_object* v___x_59_; uint8_t v_isShared_60_; uint8_t v_isSharedCheck_67_; 
v_a_57_ = lean_ctor_get(v___x_56_, 0);
v_isSharedCheck_67_ = !lean_is_exclusive(v___x_56_);
if (v_isSharedCheck_67_ == 0)
{
v___x_59_ = v___x_56_;
v_isShared_60_ = v_isSharedCheck_67_;
goto v_resetjp_58_;
}
else
{
lean_inc(v_a_57_);
lean_dec(v___x_56_);
v___x_59_ = lean_box(0);
v_isShared_60_ = v_isSharedCheck_67_;
goto v_resetjp_58_;
}
v_resetjp_58_:
{
lean_object* v_one_x3f_61_; 
v_one_x3f_61_ = lean_ctor_get(v_a_57_, 19);
lean_inc(v_one_x3f_61_);
lean_dec(v_a_57_);
if (lean_obj_tag(v_one_x3f_61_) == 1)
{
lean_object* v_val_62_; lean_object* v___x_64_; 
v_val_62_ = lean_ctor_get(v_one_x3f_61_, 0);
lean_inc(v_val_62_);
lean_dec_ref_known(v_one_x3f_61_, 1);
if (v_isShared_60_ == 0)
{
lean_ctor_set(v___x_59_, 0, v_val_62_);
v___x_64_ = v___x_59_;
goto v_reusejp_63_;
}
else
{
lean_object* v_reuseFailAlloc_65_; 
v_reuseFailAlloc_65_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_65_, 0, v_val_62_);
v___x_64_ = v_reuseFailAlloc_65_;
goto v_reusejp_63_;
}
v_reusejp_63_:
{
return v___x_64_;
}
}
else
{
lean_object* v___x_66_; 
lean_dec(v_one_x3f_61_);
lean_del_object(v___x_59_);
v___x_66_ = l_Lean_Meta_Grind_Arith_Linear_throwNotRing___redArg(v_a_51_, v_a_52_, v_a_53_, v_a_54_);
return v___x_66_;
}
}
}
else
{
lean_object* v_a_68_; lean_object* v___x_70_; uint8_t v_isShared_71_; uint8_t v_isSharedCheck_75_; 
v_a_68_ = lean_ctor_get(v___x_56_, 0);
v_isSharedCheck_75_ = !lean_is_exclusive(v___x_56_);
if (v_isSharedCheck_75_ == 0)
{
v___x_70_ = v___x_56_;
v_isShared_71_ = v_isSharedCheck_75_;
goto v_resetjp_69_;
}
else
{
lean_inc(v_a_68_);
lean_dec(v___x_56_);
v___x_70_ = lean_box(0);
v_isShared_71_ = v_isSharedCheck_75_;
goto v_resetjp_69_;
}
v_resetjp_69_:
{
lean_object* v___x_73_; 
if (v_isShared_71_ == 0)
{
v___x_73_ = v___x_70_;
goto v_reusejp_72_;
}
else
{
lean_object* v_reuseFailAlloc_74_; 
v_reuseFailAlloc_74_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_74_, 0, v_a_68_);
v___x_73_ = v_reuseFailAlloc_74_;
goto v_reusejp_72_;
}
v_reusejp_72_:
{
return v___x_73_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOne___boxed(lean_object* v_a_76_, lean_object* v_a_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Lean_Meta_Grind_Arith_Linear_getOne(v_a_76_, v_a_77_, v_a_78_, v_a_79_, v_a_80_, v_a_81_, v_a_82_, v_a_83_, v_a_84_, v_a_85_, v_a_86_);
lean_dec(v_a_86_);
lean_dec_ref(v_a_85_);
lean_dec(v_a_84_);
lean_dec_ref(v_a_83_);
lean_dec(v_a_82_);
lean_dec_ref(v_a_81_);
lean_dec(v_a_80_);
lean_dec_ref(v_a_79_);
lean_dec(v_a_78_);
lean_dec(v_a_77_);
lean_dec(v_a_76_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isCommRing(lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_89_, v_a_90_, v_a_91_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_);
if (lean_obj_tag(v___x_101_) == 0)
{
lean_object* v_a_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_117_; 
v_a_102_ = lean_ctor_get(v___x_101_, 0);
v_isSharedCheck_117_ = !lean_is_exclusive(v___x_101_);
if (v_isSharedCheck_117_ == 0)
{
v___x_104_ = v___x_101_;
v_isShared_105_ = v_isSharedCheck_117_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_a_102_);
lean_dec(v___x_101_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_117_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v_ringId_x3f_106_; 
v_ringId_x3f_106_ = lean_ctor_get(v_a_102_, 1);
lean_inc(v_ringId_x3f_106_);
lean_dec(v_a_102_);
if (lean_obj_tag(v_ringId_x3f_106_) == 0)
{
uint8_t v___x_107_; lean_object* v___x_108_; lean_object* v___x_110_; 
v___x_107_ = 0;
v___x_108_ = lean_box(v___x_107_);
if (v_isShared_105_ == 0)
{
lean_ctor_set(v___x_104_, 0, v___x_108_);
v___x_110_ = v___x_104_;
goto v_reusejp_109_;
}
else
{
lean_object* v_reuseFailAlloc_111_; 
v_reuseFailAlloc_111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_111_, 0, v___x_108_);
v___x_110_ = v_reuseFailAlloc_111_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
return v___x_110_;
}
}
else
{
uint8_t v___x_112_; lean_object* v___x_113_; lean_object* v___x_115_; 
lean_dec_ref_known(v_ringId_x3f_106_, 1);
v___x_112_ = 1;
v___x_113_ = lean_box(v___x_112_);
if (v_isShared_105_ == 0)
{
lean_ctor_set(v___x_104_, 0, v___x_113_);
v___x_115_ = v___x_104_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v___x_113_);
v___x_115_ = v_reuseFailAlloc_116_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
return v___x_115_;
}
}
}
}
else
{
lean_object* v_a_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_125_; 
v_a_118_ = lean_ctor_get(v___x_101_, 0);
v_isSharedCheck_125_ = !lean_is_exclusive(v___x_101_);
if (v_isSharedCheck_125_ == 0)
{
v___x_120_ = v___x_101_;
v_isShared_121_ = v_isSharedCheck_125_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_a_118_);
lean_dec(v___x_101_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_125_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v___x_123_; 
if (v_isShared_121_ == 0)
{
v___x_123_ = v___x_120_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v_a_118_);
v___x_123_ = v_reuseFailAlloc_124_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
return v___x_123_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isCommRing___boxed(lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Lean_Meta_Grind_Arith_Linear_isCommRing(v_a_126_, v_a_127_, v_a_128_, v_a_129_, v_a_130_, v_a_131_, v_a_132_, v_a_133_, v_a_134_, v_a_135_, v_a_136_);
lean_dec(v_a_136_);
lean_dec_ref(v_a_135_);
lean_dec(v_a_134_);
lean_dec_ref(v_a_133_);
lean_dec(v_a_132_);
lean_dec_ref(v_a_131_);
lean_dec(v_a_130_);
lean_dec_ref(v_a_129_);
lean_dec(v_a_128_);
lean_dec(v_a_127_);
lean_dec(v_a_126_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isOrderedCommRing(lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = l_Lean_Meta_Grind_Arith_Linear_isCommRing(v_a_139_, v_a_140_, v_a_141_, v_a_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_, v_a_149_);
if (lean_obj_tag(v___x_151_) == 0)
{
lean_object* v_a_152_; lean_object* v___x_153_; 
v_a_152_ = lean_ctor_get(v___x_151_, 0);
lean_inc(v_a_152_);
lean_dec_ref_known(v___x_151_, 1);
v___x_153_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_139_, v_a_140_, v_a_141_, v_a_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_, v_a_149_);
if (lean_obj_tag(v___x_153_) == 0)
{
uint8_t v___x_154_; 
v___x_154_ = lean_unbox(v_a_152_);
if (v___x_154_ == 0)
{
lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_161_; 
v_isSharedCheck_161_ = !lean_is_exclusive(v___x_153_);
if (v_isSharedCheck_161_ == 0)
{
lean_object* v_unused_162_; 
v_unused_162_ = lean_ctor_get(v___x_153_, 0);
lean_dec(v_unused_162_);
v___x_156_ = v___x_153_;
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
else
{
lean_dec(v___x_153_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_159_; 
if (v_isShared_157_ == 0)
{
lean_ctor_set(v___x_156_, 0, v_a_152_);
v___x_159_ = v___x_156_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v_a_152_);
v___x_159_ = v_reuseFailAlloc_160_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
return v___x_159_;
}
}
}
else
{
lean_object* v_a_163_; lean_object* v___x_165_; uint8_t v_isShared_166_; uint8_t v_isSharedCheck_176_; 
v_a_163_ = lean_ctor_get(v___x_153_, 0);
v_isSharedCheck_176_ = !lean_is_exclusive(v___x_153_);
if (v_isSharedCheck_176_ == 0)
{
v___x_165_ = v___x_153_;
v_isShared_166_ = v_isSharedCheck_176_;
goto v_resetjp_164_;
}
else
{
lean_inc(v_a_163_);
lean_dec(v___x_153_);
v___x_165_ = lean_box(0);
v_isShared_166_ = v_isSharedCheck_176_;
goto v_resetjp_164_;
}
v_resetjp_164_:
{
lean_object* v_orderedRingInst_x3f_167_; 
v_orderedRingInst_x3f_167_ = lean_ctor_get(v_a_163_, 14);
lean_inc(v_orderedRingInst_x3f_167_);
lean_dec(v_a_163_);
if (lean_obj_tag(v_orderedRingInst_x3f_167_) == 0)
{
uint8_t v___x_168_; lean_object* v___x_169_; lean_object* v___x_171_; 
lean_dec(v_a_152_);
v___x_168_ = 0;
v___x_169_ = lean_box(v___x_168_);
if (v_isShared_166_ == 0)
{
lean_ctor_set(v___x_165_, 0, v___x_169_);
v___x_171_ = v___x_165_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v___x_169_);
v___x_171_ = v_reuseFailAlloc_172_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
return v___x_171_;
}
}
else
{
lean_object* v___x_174_; 
lean_dec_ref_known(v_orderedRingInst_x3f_167_, 1);
if (v_isShared_166_ == 0)
{
lean_ctor_set(v___x_165_, 0, v_a_152_);
v___x_174_ = v___x_165_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v_a_152_);
v___x_174_ = v_reuseFailAlloc_175_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
return v___x_174_;
}
}
}
}
}
else
{
lean_object* v_a_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_184_; 
lean_dec(v_a_152_);
v_a_177_ = lean_ctor_get(v___x_153_, 0);
v_isSharedCheck_184_ = !lean_is_exclusive(v___x_153_);
if (v_isSharedCheck_184_ == 0)
{
v___x_179_ = v___x_153_;
v_isShared_180_ = v_isSharedCheck_184_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_a_177_);
lean_dec(v___x_153_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_184_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v___x_182_; 
if (v_isShared_180_ == 0)
{
v___x_182_ = v___x_179_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v_a_177_);
v___x_182_ = v_reuseFailAlloc_183_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
return v___x_182_;
}
}
}
}
else
{
return v___x_151_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isOrderedCommRing___boxed(lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_Lean_Meta_Grind_Arith_Linear_isOrderedCommRing(v_a_185_, v_a_186_, v_a_187_, v_a_188_, v_a_189_, v_a_190_, v_a_191_, v_a_192_, v_a_193_, v_a_194_, v_a_195_);
lean_dec(v_a_195_);
lean_dec_ref(v_a_194_);
lean_dec(v_a_193_);
lean_dec_ref(v_a_192_);
lean_dec(v_a_191_);
lean_dec_ref(v_a_190_);
lean_dec(v_a_189_);
lean_dec_ref(v_a_188_);
lean_dec(v_a_187_);
lean_dec(v_a_186_);
lean_dec(v_a_185_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isLinearOrder(lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_);
if (lean_obj_tag(v___x_210_) == 0)
{
lean_object* v_a_211_; lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_226_; 
v_a_211_ = lean_ctor_get(v___x_210_, 0);
v_isSharedCheck_226_ = !lean_is_exclusive(v___x_210_);
if (v_isSharedCheck_226_ == 0)
{
v___x_213_ = v___x_210_;
v_isShared_214_ = v_isSharedCheck_226_;
goto v_resetjp_212_;
}
else
{
lean_inc(v_a_211_);
lean_dec(v___x_210_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_226_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
lean_object* v_isLinearInst_x3f_215_; 
v_isLinearInst_x3f_215_ = lean_ctor_get(v_a_211_, 10);
lean_inc(v_isLinearInst_x3f_215_);
lean_dec(v_a_211_);
if (lean_obj_tag(v_isLinearInst_x3f_215_) == 0)
{
uint8_t v___x_216_; lean_object* v___x_217_; lean_object* v___x_219_; 
v___x_216_ = 0;
v___x_217_ = lean_box(v___x_216_);
if (v_isShared_214_ == 0)
{
lean_ctor_set(v___x_213_, 0, v___x_217_);
v___x_219_ = v___x_213_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v___x_217_);
v___x_219_ = v_reuseFailAlloc_220_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
return v___x_219_;
}
}
else
{
uint8_t v___x_221_; lean_object* v___x_222_; lean_object* v___x_224_; 
lean_dec_ref_known(v_isLinearInst_x3f_215_, 1);
v___x_221_ = 1;
v___x_222_ = lean_box(v___x_221_);
if (v_isShared_214_ == 0)
{
lean_ctor_set(v___x_213_, 0, v___x_222_);
v___x_224_ = v___x_213_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v___x_222_);
v___x_224_ = v_reuseFailAlloc_225_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
return v___x_224_;
}
}
}
}
else
{
lean_object* v_a_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_234_; 
v_a_227_ = lean_ctor_get(v___x_210_, 0);
v_isSharedCheck_234_ = !lean_is_exclusive(v___x_210_);
if (v_isSharedCheck_234_ == 0)
{
v___x_229_ = v___x_210_;
v_isShared_230_ = v_isSharedCheck_234_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_a_227_);
lean_dec(v___x_210_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_234_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
lean_object* v___x_232_; 
if (v_isShared_230_ == 0)
{
v___x_232_ = v___x_229_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v_a_227_);
v___x_232_ = v_reuseFailAlloc_233_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
return v___x_232_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isLinearOrder___boxed(lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Lean_Meta_Grind_Arith_Linear_isLinearOrder(v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_, v_a_245_);
lean_dec(v_a_245_);
lean_dec_ref(v_a_244_);
lean_dec(v_a_243_);
lean_dec_ref(v_a_242_);
lean_dec(v_a_241_);
lean_dec_ref(v_a_240_);
lean_dec(v_a_239_);
lean_dec_ref(v_a_238_);
lean_dec(v_a_237_);
lean_dec(v_a_236_);
lean_dec(v_a_235_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_hasNoNatZeroDivisors(lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_){
_start:
{
lean_object* v___x_260_; 
v___x_260_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_248_, v_a_249_, v_a_250_, v_a_251_, v_a_252_, v_a_253_, v_a_254_, v_a_255_, v_a_256_, v_a_257_, v_a_258_);
if (lean_obj_tag(v___x_260_) == 0)
{
lean_object* v_a_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_276_; 
v_a_261_ = lean_ctor_get(v___x_260_, 0);
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_260_);
if (v_isSharedCheck_276_ == 0)
{
v___x_263_ = v___x_260_;
v_isShared_264_ = v_isSharedCheck_276_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_a_261_);
lean_dec(v___x_260_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_276_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v_noNatDivInst_x3f_265_; 
v_noNatDivInst_x3f_265_ = lean_ctor_get(v_a_261_, 11);
lean_inc(v_noNatDivInst_x3f_265_);
lean_dec(v_a_261_);
if (lean_obj_tag(v_noNatDivInst_x3f_265_) == 0)
{
uint8_t v___x_266_; lean_object* v___x_267_; lean_object* v___x_269_; 
v___x_266_ = 0;
v___x_267_ = lean_box(v___x_266_);
if (v_isShared_264_ == 0)
{
lean_ctor_set(v___x_263_, 0, v___x_267_);
v___x_269_ = v___x_263_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v___x_267_);
v___x_269_ = v_reuseFailAlloc_270_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
return v___x_269_;
}
}
else
{
uint8_t v___x_271_; lean_object* v___x_272_; lean_object* v___x_274_; 
lean_dec_ref_known(v_noNatDivInst_x3f_265_, 1);
v___x_271_ = 1;
v___x_272_ = lean_box(v___x_271_);
if (v_isShared_264_ == 0)
{
lean_ctor_set(v___x_263_, 0, v___x_272_);
v___x_274_ = v___x_263_;
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
}
}
else
{
lean_object* v_a_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_284_; 
v_a_277_ = lean_ctor_get(v___x_260_, 0);
v_isSharedCheck_284_ = !lean_is_exclusive(v___x_260_);
if (v_isSharedCheck_284_ == 0)
{
v___x_279_ = v___x_260_;
v_isShared_280_ = v_isSharedCheck_284_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_a_277_);
lean_dec(v___x_260_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_284_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v___x_282_; 
if (v_isShared_280_ == 0)
{
v___x_282_ = v___x_279_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v_a_277_);
v___x_282_ = v_reuseFailAlloc_283_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
return v___x_282_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_hasNoNatZeroDivisors___boxed(lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Lean_Meta_Grind_Arith_Linear_hasNoNatZeroDivisors(v_a_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_, v_a_292_, v_a_293_, v_a_294_, v_a_295_);
lean_dec(v_a_295_);
lean_dec_ref(v_a_294_);
lean_dec(v_a_293_);
lean_dec_ref(v_a_292_);
lean_dec(v_a_291_);
lean_dec_ref(v_a_290_);
lean_dec(v_a_289_);
lean_dec_ref(v_a_288_);
lean_dec(v_a_287_);
lean_dec(v_a_286_);
lean_dec(v_a_285_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_298_, lean_object* v_vals_299_, lean_object* v_i_300_, lean_object* v_k_301_){
_start:
{
lean_object* v___x_302_; uint8_t v___x_303_; 
v___x_302_ = lean_array_get_size(v_keys_298_);
v___x_303_ = lean_nat_dec_lt(v_i_300_, v___x_302_);
if (v___x_303_ == 0)
{
lean_object* v___x_304_; 
lean_dec(v_i_300_);
v___x_304_ = lean_box(0);
return v___x_304_;
}
else
{
lean_object* v_k_x27_305_; size_t v___x_306_; size_t v___x_307_; uint8_t v___x_308_; 
v_k_x27_305_ = lean_array_fget_borrowed(v_keys_298_, v_i_300_);
v___x_306_ = lean_ptr_addr(v_k_301_);
v___x_307_ = lean_ptr_addr(v_k_x27_305_);
v___x_308_ = lean_usize_dec_eq(v___x_306_, v___x_307_);
if (v___x_308_ == 0)
{
lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_309_ = lean_unsigned_to_nat(1u);
v___x_310_ = lean_nat_add(v_i_300_, v___x_309_);
lean_dec(v_i_300_);
v_i_300_ = v___x_310_;
goto _start;
}
else
{
lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_312_ = lean_array_fget_borrowed(v_vals_299_, v_i_300_);
lean_dec(v_i_300_);
lean_inc(v___x_312_);
v___x_313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_313_, 0, v___x_312_);
return v___x_313_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_314_, lean_object* v_vals_315_, lean_object* v_i_316_, lean_object* v_k_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_314_, v_vals_315_, v_i_316_, v_k_317_);
lean_dec_ref(v_k_317_);
lean_dec_ref(v_vals_315_);
lean_dec_ref(v_keys_314_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg(lean_object* v_x_319_, size_t v_x_320_, lean_object* v_x_321_){
_start:
{
if (lean_obj_tag(v_x_319_) == 0)
{
lean_object* v_es_322_; lean_object* v___x_323_; size_t v___x_324_; size_t v___x_325_; lean_object* v_j_326_; lean_object* v___x_327_; 
v_es_322_ = lean_ctor_get(v_x_319_, 0);
v___x_323_ = lean_box(2);
v___x_324_ = ((size_t)31ULL);
v___x_325_ = lean_usize_land(v_x_320_, v___x_324_);
v_j_326_ = lean_usize_to_nat(v___x_325_);
v___x_327_ = lean_array_get_borrowed(v___x_323_, v_es_322_, v_j_326_);
lean_dec(v_j_326_);
switch(lean_obj_tag(v___x_327_))
{
case 0:
{
lean_object* v_key_328_; lean_object* v_val_329_; size_t v___x_330_; size_t v___x_331_; uint8_t v___x_332_; 
v_key_328_ = lean_ctor_get(v___x_327_, 0);
v_val_329_ = lean_ctor_get(v___x_327_, 1);
v___x_330_ = lean_ptr_addr(v_x_321_);
v___x_331_ = lean_ptr_addr(v_key_328_);
v___x_332_ = lean_usize_dec_eq(v___x_330_, v___x_331_);
if (v___x_332_ == 0)
{
lean_object* v___x_333_; 
v___x_333_ = lean_box(0);
return v___x_333_;
}
else
{
lean_object* v___x_334_; 
lean_inc(v_val_329_);
v___x_334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_334_, 0, v_val_329_);
return v___x_334_;
}
}
case 1:
{
lean_object* v_node_335_; size_t v___x_336_; size_t v___x_337_; 
v_node_335_ = lean_ctor_get(v___x_327_, 0);
v___x_336_ = ((size_t)5ULL);
v___x_337_ = lean_usize_shift_right(v_x_320_, v___x_336_);
v_x_319_ = v_node_335_;
v_x_320_ = v___x_337_;
goto _start;
}
default: 
{
lean_object* v___x_339_; 
v___x_339_ = lean_box(0);
return v___x_339_;
}
}
}
else
{
lean_object* v_ks_340_; lean_object* v_vs_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v_ks_340_ = lean_ctor_get(v_x_319_, 0);
v_vs_341_ = lean_ctor_get(v_x_319_, 1);
v___x_342_ = lean_unsigned_to_nat(0u);
v___x_343_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_340_, v_vs_341_, v___x_342_, v_x_321_);
return v___x_343_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_344_, lean_object* v_x_345_, lean_object* v_x_346_){
_start:
{
size_t v_x_904__boxed_347_; lean_object* v_res_348_; 
v_x_904__boxed_347_ = lean_unbox_usize(v_x_345_);
lean_dec(v_x_345_);
v_res_348_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg(v_x_344_, v_x_904__boxed_347_, v_x_346_);
lean_dec_ref(v_x_346_);
lean_dec_ref(v_x_344_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0___redArg(lean_object* v_x_349_, lean_object* v_x_350_){
_start:
{
size_t v___x_351_; size_t v___x_352_; size_t v___x_353_; uint64_t v___x_354_; size_t v___x_355_; lean_object* v___x_356_; 
v___x_351_ = lean_ptr_addr(v_x_350_);
v___x_352_ = ((size_t)3ULL);
v___x_353_ = lean_usize_shift_right(v___x_351_, v___x_352_);
v___x_354_ = lean_usize_to_uint64(v___x_353_);
v___x_355_ = lean_uint64_to_usize(v___x_354_);
v___x_356_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg(v_x_349_, v___x_355_, v_x_350_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0___redArg___boxed(lean_object* v_x_357_, lean_object* v_x_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0___redArg(v_x_357_, v_x_358_);
lean_dec_ref(v_x_358_);
lean_dec_ref(v_x_357_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg(lean_object* v_e_360_, lean_object* v_a_361_, lean_object* v_a_362_){
_start:
{
lean_object* v___x_364_; 
v___x_364_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_361_, v_a_362_);
if (lean_obj_tag(v___x_364_) == 0)
{
lean_object* v_a_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_374_; 
v_a_365_ = lean_ctor_get(v___x_364_, 0);
v_isSharedCheck_374_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_374_ == 0)
{
v___x_367_ = v___x_364_;
v_isShared_368_ = v_isSharedCheck_374_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_a_365_);
lean_dec(v___x_364_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_374_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v_exprToStructId_369_; lean_object* v___x_370_; lean_object* v___x_372_; 
v_exprToStructId_369_ = lean_ctor_get(v_a_365_, 2);
lean_inc_ref(v_exprToStructId_369_);
lean_dec(v_a_365_);
v___x_370_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0___redArg(v_exprToStructId_369_, v_e_360_);
lean_dec_ref(v_exprToStructId_369_);
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 0, v___x_370_);
v___x_372_ = v___x_367_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v___x_370_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
return v___x_372_;
}
}
}
else
{
lean_object* v_a_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_382_; 
v_a_375_ = lean_ctor_get(v___x_364_, 0);
v_isSharedCheck_382_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_382_ == 0)
{
v___x_377_ = v___x_364_;
v_isShared_378_ = v_isSharedCheck_382_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_a_375_);
lean_dec(v___x_364_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_382_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_380_; 
if (v_isShared_378_ == 0)
{
v___x_380_ = v___x_377_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v_a_375_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg___boxed(lean_object* v_e_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg(v_e_383_, v_a_384_, v_a_385_);
lean_dec_ref(v_a_385_);
lean_dec(v_a_384_);
lean_dec_ref(v_e_383_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f(lean_object* v_e_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_){
_start:
{
lean_object* v___x_400_; 
v___x_400_ = l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg(v_e_388_, v_a_389_, v_a_397_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___boxed(lean_object* v_e_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f(v_e_401_, v_a_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_);
lean_dec(v_a_411_);
lean_dec_ref(v_a_410_);
lean_dec(v_a_409_);
lean_dec_ref(v_a_408_);
lean_dec(v_a_407_);
lean_dec_ref(v_a_406_);
lean_dec(v_a_405_);
lean_dec_ref(v_a_404_);
lean_dec(v_a_403_);
lean_dec(v_a_402_);
lean_dec_ref(v_e_401_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0(lean_object* v_00_u03b2_414_, lean_object* v_x_415_, lean_object* v_x_416_){
_start:
{
lean_object* v___x_417_; 
v___x_417_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0___redArg(v_x_415_, v_x_416_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0___boxed(lean_object* v_00_u03b2_418_, lean_object* v_x_419_, lean_object* v_x_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0(v_00_u03b2_418_, v_x_419_, v_x_420_);
lean_dec_ref(v_x_420_);
lean_dec_ref(v_x_419_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_422_, lean_object* v_x_423_, size_t v_x_424_, lean_object* v_x_425_){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg(v_x_423_, v_x_424_, v_x_425_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_427_, lean_object* v_x_428_, lean_object* v_x_429_, lean_object* v_x_430_){
_start:
{
size_t v_x_1025__boxed_431_; lean_object* v_res_432_; 
v_x_1025__boxed_431_ = lean_unbox_usize(v_x_429_);
lean_dec(v_x_429_);
v_res_432_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0(v_00_u03b2_427_, v_x_428_, v_x_1025__boxed_431_, v_x_430_);
lean_dec_ref(v_x_430_);
lean_dec_ref(v_x_428_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_433_, lean_object* v_keys_434_, lean_object* v_vals_435_, lean_object* v_heq_436_, lean_object* v_i_437_, lean_object* v_k_438_){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_434_, v_vals_435_, v_i_437_, v_k_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_440_, lean_object* v_keys_441_, lean_object* v_vals_442_, lean_object* v_heq_443_, lean_object* v_i_444_, lean_object* v_k_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_440_, v_keys_441_, v_vals_442_, v_heq_443_, v_i_444_, v_k_445_);
lean_dec_ref(v_k_445_);
lean_dec_ref(v_vals_442_);
lean_dec_ref(v_keys_441_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_447_, lean_object* v_x_448_, lean_object* v_x_449_, lean_object* v_x_450_){
_start:
{
lean_object* v_ks_451_; lean_object* v_vs_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_478_; 
v_ks_451_ = lean_ctor_get(v_x_447_, 0);
v_vs_452_ = lean_ctor_get(v_x_447_, 1);
v_isSharedCheck_478_ = !lean_is_exclusive(v_x_447_);
if (v_isSharedCheck_478_ == 0)
{
v___x_454_ = v_x_447_;
v_isShared_455_ = v_isSharedCheck_478_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_vs_452_);
lean_inc(v_ks_451_);
lean_dec(v_x_447_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_478_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_456_; uint8_t v___x_457_; 
v___x_456_ = lean_array_get_size(v_ks_451_);
v___x_457_ = lean_nat_dec_lt(v_x_448_, v___x_456_);
if (v___x_457_ == 0)
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_461_; 
lean_dec(v_x_448_);
v___x_458_ = lean_array_push(v_ks_451_, v_x_449_);
v___x_459_ = lean_array_push(v_vs_452_, v_x_450_);
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 1, v___x_459_);
lean_ctor_set(v___x_454_, 0, v___x_458_);
v___x_461_ = v___x_454_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v___x_458_);
lean_ctor_set(v_reuseFailAlloc_462_, 1, v___x_459_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
return v___x_461_;
}
}
else
{
lean_object* v_k_x27_463_; size_t v___x_464_; size_t v___x_465_; uint8_t v___x_466_; 
v_k_x27_463_ = lean_array_fget_borrowed(v_ks_451_, v_x_448_);
v___x_464_ = lean_ptr_addr(v_x_449_);
v___x_465_ = lean_ptr_addr(v_k_x27_463_);
v___x_466_ = lean_usize_dec_eq(v___x_464_, v___x_465_);
if (v___x_466_ == 0)
{
lean_object* v___x_468_; 
if (v_isShared_455_ == 0)
{
v___x_468_ = v___x_454_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v_ks_451_);
lean_ctor_set(v_reuseFailAlloc_472_, 1, v_vs_452_);
v___x_468_ = v_reuseFailAlloc_472_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_469_ = lean_unsigned_to_nat(1u);
v___x_470_ = lean_nat_add(v_x_448_, v___x_469_);
lean_dec(v_x_448_);
v_x_447_ = v___x_468_;
v_x_448_ = v___x_470_;
goto _start;
}
}
else
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_476_; 
v___x_473_ = lean_array_fset(v_ks_451_, v_x_448_, v_x_449_);
v___x_474_ = lean_array_fset(v_vs_452_, v_x_448_, v_x_450_);
lean_dec(v_x_448_);
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 1, v___x_474_);
lean_ctor_set(v___x_454_, 0, v___x_473_);
v___x_476_ = v___x_454_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v___x_473_);
lean_ctor_set(v_reuseFailAlloc_477_, 1, v___x_474_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1___redArg(lean_object* v_n_479_, lean_object* v_k_480_, lean_object* v_v_481_){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_482_ = lean_unsigned_to_nat(0u);
v___x_483_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1_spec__2___redArg(v_n_479_, v___x_482_, v_k_480_, v_v_481_);
return v___x_483_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg(lean_object* v_x_485_, size_t v_x_486_, size_t v_x_487_, lean_object* v_x_488_, lean_object* v_x_489_){
_start:
{
if (lean_obj_tag(v_x_485_) == 0)
{
lean_object* v_es_490_; size_t v___x_491_; size_t v___x_492_; lean_object* v_j_493_; lean_object* v___x_494_; uint8_t v___x_495_; 
v_es_490_ = lean_ctor_get(v_x_485_, 0);
v___x_491_ = ((size_t)31ULL);
v___x_492_ = lean_usize_land(v_x_486_, v___x_491_);
v_j_493_ = lean_usize_to_nat(v___x_492_);
v___x_494_ = lean_array_get_size(v_es_490_);
v___x_495_ = lean_nat_dec_lt(v_j_493_, v___x_494_);
if (v___x_495_ == 0)
{
lean_dec(v_j_493_);
lean_dec(v_x_489_);
lean_dec_ref(v_x_488_);
return v_x_485_;
}
else
{
lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_536_; 
lean_inc_ref(v_es_490_);
v_isSharedCheck_536_ = !lean_is_exclusive(v_x_485_);
if (v_isSharedCheck_536_ == 0)
{
lean_object* v_unused_537_; 
v_unused_537_ = lean_ctor_get(v_x_485_, 0);
lean_dec(v_unused_537_);
v___x_497_ = v_x_485_;
v_isShared_498_ = v_isSharedCheck_536_;
goto v_resetjp_496_;
}
else
{
lean_dec(v_x_485_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_536_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v_v_499_; lean_object* v___x_500_; lean_object* v_xs_x27_501_; lean_object* v___y_503_; 
v_v_499_ = lean_array_fget(v_es_490_, v_j_493_);
v___x_500_ = lean_box(0);
v_xs_x27_501_ = lean_array_fset(v_es_490_, v_j_493_, v___x_500_);
switch(lean_obj_tag(v_v_499_))
{
case 0:
{
lean_object* v_key_508_; lean_object* v_val_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_521_; 
v_key_508_ = lean_ctor_get(v_v_499_, 0);
v_val_509_ = lean_ctor_get(v_v_499_, 1);
v_isSharedCheck_521_ = !lean_is_exclusive(v_v_499_);
if (v_isSharedCheck_521_ == 0)
{
v___x_511_ = v_v_499_;
v_isShared_512_ = v_isSharedCheck_521_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_val_509_);
lean_inc(v_key_508_);
lean_dec(v_v_499_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_521_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
size_t v___x_513_; size_t v___x_514_; uint8_t v___x_515_; 
v___x_513_ = lean_ptr_addr(v_x_488_);
v___x_514_ = lean_ptr_addr(v_key_508_);
v___x_515_ = lean_usize_dec_eq(v___x_513_, v___x_514_);
if (v___x_515_ == 0)
{
lean_object* v___x_516_; lean_object* v___x_517_; 
lean_del_object(v___x_511_);
v___x_516_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_508_, v_val_509_, v_x_488_, v_x_489_);
v___x_517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_517_, 0, v___x_516_);
v___y_503_ = v___x_517_;
goto v___jp_502_;
}
else
{
lean_object* v___x_519_; 
lean_dec(v_val_509_);
lean_dec(v_key_508_);
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 1, v_x_489_);
lean_ctor_set(v___x_511_, 0, v_x_488_);
v___x_519_ = v___x_511_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v_x_488_);
lean_ctor_set(v_reuseFailAlloc_520_, 1, v_x_489_);
v___x_519_ = v_reuseFailAlloc_520_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
v___y_503_ = v___x_519_;
goto v___jp_502_;
}
}
}
}
case 1:
{
lean_object* v_node_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_534_; 
v_node_522_ = lean_ctor_get(v_v_499_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v_v_499_);
if (v_isSharedCheck_534_ == 0)
{
v___x_524_ = v_v_499_;
v_isShared_525_ = v_isSharedCheck_534_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_node_522_);
lean_dec(v_v_499_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_534_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
size_t v___x_526_; size_t v___x_527_; size_t v___x_528_; size_t v___x_529_; lean_object* v___x_530_; lean_object* v___x_532_; 
v___x_526_ = ((size_t)5ULL);
v___x_527_ = lean_usize_shift_right(v_x_486_, v___x_526_);
v___x_528_ = ((size_t)1ULL);
v___x_529_ = lean_usize_add(v_x_487_, v___x_528_);
v___x_530_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg(v_node_522_, v___x_527_, v___x_529_, v_x_488_, v_x_489_);
if (v_isShared_525_ == 0)
{
lean_ctor_set(v___x_524_, 0, v___x_530_);
v___x_532_ = v___x_524_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v___x_530_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
v___y_503_ = v___x_532_;
goto v___jp_502_;
}
}
}
default: 
{
lean_object* v___x_535_; 
v___x_535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_535_, 0, v_x_488_);
lean_ctor_set(v___x_535_, 1, v_x_489_);
v___y_503_ = v___x_535_;
goto v___jp_502_;
}
}
v___jp_502_:
{
lean_object* v___x_504_; lean_object* v___x_506_; 
v___x_504_ = lean_array_fset(v_xs_x27_501_, v_j_493_, v___y_503_);
lean_dec(v_j_493_);
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 0, v___x_504_);
v___x_506_ = v___x_497_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v___x_504_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
}
}
}
else
{
lean_object* v_ks_538_; lean_object* v_vs_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_557_; 
v_ks_538_ = lean_ctor_get(v_x_485_, 0);
v_vs_539_ = lean_ctor_get(v_x_485_, 1);
v_isSharedCheck_557_ = !lean_is_exclusive(v_x_485_);
if (v_isSharedCheck_557_ == 0)
{
v___x_541_ = v_x_485_;
v_isShared_542_ = v_isSharedCheck_557_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_vs_539_);
lean_inc(v_ks_538_);
lean_dec(v_x_485_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_557_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_544_; 
if (v_isShared_542_ == 0)
{
v___x_544_ = v___x_541_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v_ks_538_);
lean_ctor_set(v_reuseFailAlloc_556_, 1, v_vs_539_);
v___x_544_ = v_reuseFailAlloc_556_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
lean_object* v_newNode_545_; size_t v___x_546_; uint8_t v___x_547_; 
v_newNode_545_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1___redArg(v___x_544_, v_x_488_, v_x_489_);
v___x_546_ = ((size_t)7ULL);
v___x_547_ = lean_usize_dec_le(v___x_546_, v_x_487_);
if (v___x_547_ == 0)
{
lean_object* v___x_548_; lean_object* v___x_549_; uint8_t v___x_550_; 
v___x_548_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_545_);
v___x_549_ = lean_unsigned_to_nat(4u);
v___x_550_ = lean_nat_dec_lt(v___x_548_, v___x_549_);
lean_dec(v___x_548_);
if (v___x_550_ == 0)
{
lean_object* v_ks_551_; lean_object* v_vs_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v_ks_551_ = lean_ctor_get(v_newNode_545_, 0);
lean_inc_ref(v_ks_551_);
v_vs_552_ = lean_ctor_get(v_newNode_545_, 1);
lean_inc_ref(v_vs_552_);
lean_dec_ref(v_newNode_545_);
v___x_553_ = lean_unsigned_to_nat(0u);
v___x_554_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg___closed__0);
v___x_555_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2___redArg(v_x_487_, v_ks_551_, v_vs_552_, v___x_553_, v___x_554_);
lean_dec_ref(v_vs_552_);
lean_dec_ref(v_ks_551_);
return v___x_555_;
}
else
{
return v_newNode_545_;
}
}
else
{
return v_newNode_545_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2___redArg(size_t v_depth_558_, lean_object* v_keys_559_, lean_object* v_vals_560_, lean_object* v_i_561_, lean_object* v_entries_562_){
_start:
{
lean_object* v___x_563_; uint8_t v___x_564_; 
v___x_563_ = lean_array_get_size(v_keys_559_);
v___x_564_ = lean_nat_dec_lt(v_i_561_, v___x_563_);
if (v___x_564_ == 0)
{
lean_dec(v_i_561_);
return v_entries_562_;
}
else
{
lean_object* v_k_565_; lean_object* v_v_566_; size_t v___x_567_; size_t v___x_568_; size_t v___x_569_; uint64_t v___x_570_; size_t v_h_571_; size_t v___x_572_; lean_object* v___x_573_; size_t v___x_574_; size_t v___x_575_; size_t v___x_576_; size_t v_h_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
v_k_565_ = lean_array_fget_borrowed(v_keys_559_, v_i_561_);
v_v_566_ = lean_array_fget_borrowed(v_vals_560_, v_i_561_);
v___x_567_ = lean_ptr_addr(v_k_565_);
v___x_568_ = ((size_t)3ULL);
v___x_569_ = lean_usize_shift_right(v___x_567_, v___x_568_);
v___x_570_ = lean_usize_to_uint64(v___x_569_);
v_h_571_ = lean_uint64_to_usize(v___x_570_);
v___x_572_ = ((size_t)5ULL);
v___x_573_ = lean_unsigned_to_nat(1u);
v___x_574_ = ((size_t)1ULL);
v___x_575_ = lean_usize_sub(v_depth_558_, v___x_574_);
v___x_576_ = lean_usize_mul(v___x_572_, v___x_575_);
v_h_577_ = lean_usize_shift_right(v_h_571_, v___x_576_);
v___x_578_ = lean_nat_add(v_i_561_, v___x_573_);
lean_dec(v_i_561_);
lean_inc(v_v_566_);
lean_inc(v_k_565_);
v___x_579_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg(v_entries_562_, v_h_577_, v_depth_558_, v_k_565_, v_v_566_);
v_i_561_ = v___x_578_;
v_entries_562_ = v___x_579_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_581_, lean_object* v_keys_582_, lean_object* v_vals_583_, lean_object* v_i_584_, lean_object* v_entries_585_){
_start:
{
size_t v_depth_boxed_586_; lean_object* v_res_587_; 
v_depth_boxed_586_ = lean_unbox_usize(v_depth_581_);
lean_dec(v_depth_581_);
v_res_587_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2___redArg(v_depth_boxed_586_, v_keys_582_, v_vals_583_, v_i_584_, v_entries_585_);
lean_dec_ref(v_vals_583_);
lean_dec_ref(v_keys_582_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg___boxed(lean_object* v_x_588_, lean_object* v_x_589_, lean_object* v_x_590_, lean_object* v_x_591_, lean_object* v_x_592_){
_start:
{
size_t v_x_6461__boxed_593_; size_t v_x_6462__boxed_594_; lean_object* v_res_595_; 
v_x_6461__boxed_593_ = lean_unbox_usize(v_x_589_);
lean_dec(v_x_589_);
v_x_6462__boxed_594_ = lean_unbox_usize(v_x_590_);
lean_dec(v_x_590_);
v_res_595_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg(v_x_588_, v_x_6461__boxed_593_, v_x_6462__boxed_594_, v_x_591_, v_x_592_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0___redArg(lean_object* v_x_596_, lean_object* v_x_597_, lean_object* v_x_598_){
_start:
{
size_t v___x_599_; size_t v___x_600_; size_t v___x_601_; uint64_t v___x_602_; size_t v___x_603_; size_t v___x_604_; lean_object* v___x_605_; 
v___x_599_ = lean_ptr_addr(v_x_597_);
v___x_600_ = ((size_t)3ULL);
v___x_601_ = lean_usize_shift_right(v___x_599_, v___x_600_);
v___x_602_ = lean_usize_to_uint64(v___x_601_);
v___x_603_ = lean_uint64_to_usize(v___x_602_);
v___x_604_ = ((size_t)1ULL);
v___x_605_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg(v_x_596_, v___x_603_, v___x_604_, v_x_597_, v_x_598_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___lam__0(lean_object* v_e_606_, lean_object* v_a_607_, lean_object* v_s_608_){
_start:
{
lean_object* v_structs_609_; lean_object* v_typeIdOf_610_; lean_object* v_exprToStructId_611_; lean_object* v_exprToStructIdEntries_612_; lean_object* v_forbiddenNatModules_613_; lean_object* v_natStructs_614_; lean_object* v_natTypeIdOf_615_; lean_object* v_exprToNatStructId_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_626_; 
v_structs_609_ = lean_ctor_get(v_s_608_, 0);
v_typeIdOf_610_ = lean_ctor_get(v_s_608_, 1);
v_exprToStructId_611_ = lean_ctor_get(v_s_608_, 2);
v_exprToStructIdEntries_612_ = lean_ctor_get(v_s_608_, 3);
v_forbiddenNatModules_613_ = lean_ctor_get(v_s_608_, 4);
v_natStructs_614_ = lean_ctor_get(v_s_608_, 5);
v_natTypeIdOf_615_ = lean_ctor_get(v_s_608_, 6);
v_exprToNatStructId_616_ = lean_ctor_get(v_s_608_, 7);
v_isSharedCheck_626_ = !lean_is_exclusive(v_s_608_);
if (v_isSharedCheck_626_ == 0)
{
v___x_618_ = v_s_608_;
v_isShared_619_ = v_isSharedCheck_626_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_exprToNatStructId_616_);
lean_inc(v_natTypeIdOf_615_);
lean_inc(v_natStructs_614_);
lean_inc(v_forbiddenNatModules_613_);
lean_inc(v_exprToStructIdEntries_612_);
lean_inc(v_exprToStructId_611_);
lean_inc(v_typeIdOf_610_);
lean_inc(v_structs_609_);
lean_dec(v_s_608_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_626_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_624_; 
lean_inc_n(v_a_607_, 2);
lean_inc_ref(v_e_606_);
v___x_620_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0___redArg(v_exprToStructId_611_, v_e_606_, v_a_607_);
v___x_621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_621_, 0, v_e_606_);
lean_ctor_set(v___x_621_, 1, v_a_607_);
v___x_622_ = l_Lean_PersistentArray_push___redArg(v_exprToStructIdEntries_612_, v___x_621_);
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 3, v___x_622_);
lean_ctor_set(v___x_618_, 2, v___x_620_);
v___x_624_ = v___x_618_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v_structs_609_);
lean_ctor_set(v_reuseFailAlloc_625_, 1, v_typeIdOf_610_);
lean_ctor_set(v_reuseFailAlloc_625_, 2, v___x_620_);
lean_ctor_set(v_reuseFailAlloc_625_, 3, v___x_622_);
lean_ctor_set(v_reuseFailAlloc_625_, 4, v_forbiddenNatModules_613_);
lean_ctor_set(v_reuseFailAlloc_625_, 5, v_natStructs_614_);
lean_ctor_set(v_reuseFailAlloc_625_, 6, v_natTypeIdOf_615_);
lean_ctor_set(v_reuseFailAlloc_625_, 7, v_exprToNatStructId_616_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
return v___x_624_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___lam__0___boxed(lean_object* v_e_627_, lean_object* v_a_628_, lean_object* v_s_629_){
_start:
{
lean_object* v_res_630_; 
v_res_630_ = l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___lam__0(v_e_627_, v_a_628_, v_s_629_);
lean_dec(v_a_628_);
return v_res_630_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___closed__1(void){
_start:
{
lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_632_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___closed__0));
v___x_633_ = l_Lean_stringToMessageData(v___x_632_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg(lean_object* v_e_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_){
_start:
{
lean_object* v___x_647_; 
v___x_647_ = l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg(v_e_634_, v_a_636_, v_a_641_);
if (lean_obj_tag(v___x_647_) == 0)
{
lean_object* v_a_648_; 
v_a_648_ = lean_ctor_get(v___x_647_, 0);
lean_inc(v_a_648_);
lean_dec_ref_known(v___x_647_, 1);
if (lean_obj_tag(v_a_648_) == 1)
{
lean_object* v_val_649_; uint8_t v___x_650_; 
v_val_649_ = lean_ctor_get(v_a_648_, 0);
lean_inc(v_val_649_);
lean_dec_ref_known(v_a_648_, 1);
v___x_650_ = lean_nat_dec_eq(v_val_649_, v_a_635_);
lean_dec(v_val_649_);
if (v___x_650_ == 0)
{
lean_object* v___x_651_; 
v___x_651_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_637_);
if (lean_obj_tag(v___x_651_) == 0)
{
lean_object* v_a_652_; uint8_t v_verbose_653_; 
v_a_652_ = lean_ctor_get(v___x_651_, 0);
lean_inc(v_a_652_);
lean_dec_ref_known(v___x_651_, 1);
v_verbose_653_ = lean_ctor_get_uint8(v_a_652_, 0);
lean_dec(v_a_652_);
if (v_verbose_653_ == 0)
{
lean_dec_ref(v_e_634_);
goto v___jp_644_;
}
else
{
lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_654_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___closed__1, &l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___closed__1);
v___x_655_ = l_Lean_indentExpr(v_e_634_);
v___x_656_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_656_, 0, v___x_654_);
lean_ctor_set(v___x_656_, 1, v___x_655_);
v___x_657_ = l_Lean_Meta_Sym_reportIssue(v___x_656_, v_a_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_, v_a_642_);
if (lean_obj_tag(v___x_657_) == 0)
{
lean_dec_ref_known(v___x_657_, 1);
goto v___jp_644_;
}
else
{
return v___x_657_;
}
}
}
else
{
lean_object* v_a_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_665_; 
lean_dec_ref(v_e_634_);
v_a_658_ = lean_ctor_get(v___x_651_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_665_ == 0)
{
v___x_660_ = v___x_651_;
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_a_658_);
lean_dec(v___x_651_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_663_; 
if (v_isShared_661_ == 0)
{
v___x_663_ = v___x_660_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v_a_658_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
}
else
{
lean_dec_ref(v_e_634_);
goto v___jp_644_;
}
}
else
{
lean_object* v___f_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
lean_dec(v_a_648_);
lean_inc(v_a_635_);
v___f_666_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_666_, 0, v_e_634_);
lean_closure_set(v___f_666_, 1, v_a_635_);
v___x_667_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_668_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_667_, v___f_666_, v_a_636_);
return v___x_668_;
}
}
else
{
lean_object* v_a_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_676_; 
lean_dec_ref(v_e_634_);
v_a_669_ = lean_ctor_get(v___x_647_, 0);
v_isSharedCheck_676_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_676_ == 0)
{
v___x_671_ = v___x_647_;
v_isShared_672_ = v_isSharedCheck_676_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_a_669_);
lean_dec(v___x_647_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_676_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_674_; 
if (v_isShared_672_ == 0)
{
v___x_674_ = v___x_671_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v_a_669_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
return v___x_674_;
}
}
}
v___jp_644_:
{
lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_645_ = lean_box(0);
v___x_646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_646_, 0, v___x_645_);
return v___x_646_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg___boxed(lean_object* v_e_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg(v_e_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_, v_a_682_, v_a_683_, v_a_684_, v_a_685_);
lean_dec(v_a_685_);
lean_dec_ref(v_a_684_);
lean_dec(v_a_683_);
lean_dec_ref(v_a_682_);
lean_dec(v_a_681_);
lean_dec_ref(v_a_680_);
lean_dec(v_a_679_);
lean_dec(v_a_678_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId(lean_object* v_e_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_){
_start:
{
lean_object* v___x_701_; 
v___x_701_ = l_Lean_Meta_Grind_Arith_Linear_setTermStructId___redArg(v_e_688_, v_a_689_, v_a_690_, v_a_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_, v_a_699_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId___boxed(lean_object* v_e_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_){
_start:
{
lean_object* v_res_715_; 
v_res_715_ = l_Lean_Meta_Grind_Arith_Linear_setTermStructId(v_e_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_);
lean_dec(v_a_713_);
lean_dec_ref(v_a_712_);
lean_dec(v_a_711_);
lean_dec_ref(v_a_710_);
lean_dec(v_a_709_);
lean_dec_ref(v_a_708_);
lean_dec(v_a_707_);
lean_dec_ref(v_a_706_);
lean_dec(v_a_705_);
lean_dec(v_a_704_);
lean_dec(v_a_703_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0(lean_object* v_00_u03b2_716_, lean_object* v_x_717_, lean_object* v_x_718_, lean_object* v_x_719_){
_start:
{
lean_object* v___x_720_; 
v___x_720_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0___redArg(v_x_717_, v_x_718_, v_x_719_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0(lean_object* v_00_u03b2_721_, lean_object* v_x_722_, size_t v_x_723_, size_t v_x_724_, lean_object* v_x_725_, lean_object* v_x_726_){
_start:
{
lean_object* v___x_727_; 
v___x_727_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg(v_x_722_, v_x_723_, v_x_724_, v_x_725_, v_x_726_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___boxed(lean_object* v_00_u03b2_728_, lean_object* v_x_729_, lean_object* v_x_730_, lean_object* v_x_731_, lean_object* v_x_732_, lean_object* v_x_733_){
_start:
{
size_t v_x_6751__boxed_734_; size_t v_x_6752__boxed_735_; lean_object* v_res_736_; 
v_x_6751__boxed_734_ = lean_unbox_usize(v_x_730_);
lean_dec(v_x_730_);
v_x_6752__boxed_735_ = lean_unbox_usize(v_x_731_);
lean_dec(v_x_731_);
v_res_736_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0(v_00_u03b2_728_, v_x_729_, v_x_6751__boxed_734_, v_x_6752__boxed_735_, v_x_732_, v_x_733_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_737_, lean_object* v_n_738_, lean_object* v_k_739_, lean_object* v_v_740_){
_start:
{
lean_object* v___x_741_; 
v___x_741_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1___redArg(v_n_738_, v_k_739_, v_v_740_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_742_, size_t v_depth_743_, lean_object* v_keys_744_, lean_object* v_vals_745_, lean_object* v_heq_746_, lean_object* v_i_747_, lean_object* v_entries_748_){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2___redArg(v_depth_743_, v_keys_744_, v_vals_745_, v_i_747_, v_entries_748_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_750_, lean_object* v_depth_751_, lean_object* v_keys_752_, lean_object* v_vals_753_, lean_object* v_heq_754_, lean_object* v_i_755_, lean_object* v_entries_756_){
_start:
{
size_t v_depth_boxed_757_; lean_object* v_res_758_; 
v_depth_boxed_757_ = lean_unbox_usize(v_depth_751_);
lean_dec(v_depth_751_);
v_res_758_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2(v_00_u03b2_750_, v_depth_boxed_757_, v_keys_752_, v_vals_753_, v_heq_754_, v_i_755_, v_entries_756_);
lean_dec_ref(v_vals_753_);
lean_dec_ref(v_keys_752_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_759_, lean_object* v_x_760_, lean_object* v_x_761_, lean_object* v_x_762_, lean_object* v_x_763_){
_start:
{
lean_object* v___x_764_; 
v___x_764_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1_spec__2___redArg(v_x_760_, v_x_761_, v_x_762_, v_x_763_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0_spec__0(lean_object* v_msgData_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_){
_start:
{
lean_object* v___x_771_; lean_object* v_env_772_; lean_object* v___x_773_; lean_object* v_toCold_774_; lean_object* v_mctx_775_; lean_object* v_lctx_776_; lean_object* v_options_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_771_ = lean_st_ref_get(v___y_769_);
v_env_772_ = lean_ctor_get(v___x_771_, 0);
lean_inc_ref(v_env_772_);
lean_dec(v___x_771_);
v___x_773_ = lean_st_ref_get(v___y_767_);
v_toCold_774_ = lean_ctor_get(v___y_768_, 0);
v_mctx_775_ = lean_ctor_get(v___x_773_, 0);
lean_inc_ref(v_mctx_775_);
lean_dec(v___x_773_);
v_lctx_776_ = lean_ctor_get(v___y_766_, 2);
v_options_777_ = lean_ctor_get(v_toCold_774_, 2);
lean_inc_ref(v_options_777_);
lean_inc_ref(v_lctx_776_);
v___x_778_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_778_, 0, v_env_772_);
lean_ctor_set(v___x_778_, 1, v_mctx_775_);
lean_ctor_set(v___x_778_, 2, v_lctx_776_);
lean_ctor_set(v___x_778_, 3, v_options_777_);
v___x_779_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_779_, 0, v___x_778_);
lean_ctor_set(v___x_779_, 1, v_msgData_765_);
v___x_780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_780_, 0, v___x_779_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0_spec__0___boxed(lean_object* v_msgData_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0_spec__0(v_msgData_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_);
lean_dec(v___y_785_);
lean_dec_ref(v___y_784_);
lean_dec(v___y_783_);
lean_dec_ref(v___y_782_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(lean_object* v_msg_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_){
_start:
{
lean_object* v_ref_794_; lean_object* v___x_795_; lean_object* v_a_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_804_; 
v_ref_794_ = lean_ctor_get(v___y_791_, 2);
v___x_795_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0_spec__0(v_msg_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_);
v_a_796_ = lean_ctor_get(v___x_795_, 0);
v_isSharedCheck_804_ = !lean_is_exclusive(v___x_795_);
if (v_isSharedCheck_804_ == 0)
{
v___x_798_ = v___x_795_;
v_isShared_799_ = v_isSharedCheck_804_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_a_796_);
lean_dec(v___x_795_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_804_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_800_; lean_object* v___x_802_; 
lean_inc(v_ref_794_);
v___x_800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_800_, 0, v_ref_794_);
lean_ctor_set(v___x_800_, 1, v_a_796_);
if (v_isShared_799_ == 0)
{
lean_ctor_set_tag(v___x_798_, 1);
lean_ctor_set(v___x_798_, 0, v___x_800_);
v___x_802_ = v___x_798_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v___x_800_);
v___x_802_ = v_reuseFailAlloc_803_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
return v___x_802_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg___boxed(lean_object* v_msg_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_){
_start:
{
lean_object* v_res_811_; 
v_res_811_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v_msg_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_);
lean_dec(v___y_809_);
lean_dec_ref(v___y_808_);
lean_dec(v___y_807_);
lean_dec_ref(v___y_806_);
return v_res_811_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___closed__1(void){
_start:
{
lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_813_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___closed__0));
v___x_814_ = l_Lean_stringToMessageData(v___x_813_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst(lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_){
_start:
{
lean_object* v___x_827_; 
v___x_827_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_, v_a_820_, v_a_821_, v_a_822_, v_a_823_, v_a_824_, v_a_825_);
if (lean_obj_tag(v___x_827_) == 0)
{
lean_object* v_a_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_839_; 
v_a_828_ = lean_ctor_get(v___x_827_, 0);
v_isSharedCheck_839_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_839_ == 0)
{
v___x_830_ = v___x_827_;
v_isShared_831_ = v_isSharedCheck_839_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_a_828_);
lean_dec(v___x_827_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_839_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v_noNatDivInst_x3f_832_; 
v_noNatDivInst_x3f_832_ = lean_ctor_get(v_a_828_, 11);
lean_inc(v_noNatDivInst_x3f_832_);
lean_dec(v_a_828_);
if (lean_obj_tag(v_noNatDivInst_x3f_832_) == 1)
{
lean_object* v_val_833_; lean_object* v___x_835_; 
v_val_833_ = lean_ctor_get(v_noNatDivInst_x3f_832_, 0);
lean_inc(v_val_833_);
lean_dec_ref_known(v_noNatDivInst_x3f_832_, 1);
if (v_isShared_831_ == 0)
{
lean_ctor_set(v___x_830_, 0, v_val_833_);
v___x_835_ = v___x_830_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_val_833_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
else
{
lean_object* v___x_837_; lean_object* v___x_838_; 
lean_dec(v_noNatDivInst_x3f_832_);
lean_del_object(v___x_830_);
v___x_837_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___closed__1);
v___x_838_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_837_, v_a_822_, v_a_823_, v_a_824_, v_a_825_);
return v___x_838_;
}
}
}
else
{
lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_847_; 
v_a_840_ = lean_ctor_get(v___x_827_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_847_ == 0)
{
v___x_842_ = v___x_827_;
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_dec(v___x_827_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_845_; 
if (v_isShared_843_ == 0)
{
v___x_845_ = v___x_842_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_a_840_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___boxed(lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_){
_start:
{
lean_object* v_res_860_; 
v_res_860_ = l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst(v_a_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_, v_a_858_);
lean_dec(v_a_858_);
lean_dec_ref(v_a_857_);
lean_dec(v_a_856_);
lean_dec_ref(v_a_855_);
lean_dec(v_a_854_);
lean_dec_ref(v_a_853_);
lean_dec(v_a_852_);
lean_dec_ref(v_a_851_);
lean_dec(v_a_850_);
lean_dec(v_a_849_);
lean_dec(v_a_848_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0(lean_object* v_00_u03b1_861_, lean_object* v_msg_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_){
_start:
{
lean_object* v___x_875_; 
v___x_875_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v_msg_862_, v___y_870_, v___y_871_, v___y_872_, v___y_873_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___boxed(lean_object* v_00_u03b1_876_, lean_object* v_msg_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0(v_00_u03b1_876_, v_msg_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_);
lean_dec(v___y_888_);
lean_dec_ref(v___y_887_);
lean_dec(v___y_886_);
lean_dec_ref(v___y_885_);
lean_dec(v___y_884_);
lean_dec_ref(v___y_883_);
lean_dec(v___y_882_);
lean_dec_ref(v___y_881_);
lean_dec(v___y_880_);
lean_dec(v___y_879_);
lean_dec(v___y_878_);
return v_res_890_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLEInst___closed__1(void){
_start:
{
lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_892_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLEInst___closed__0));
v___x_893_ = l_Lean_stringToMessageData(v___x_892_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLEInst(lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_){
_start:
{
lean_object* v___x_906_; 
v___x_906_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_);
if (lean_obj_tag(v___x_906_) == 0)
{
lean_object* v_a_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_918_; 
v_a_907_ = lean_ctor_get(v___x_906_, 0);
v_isSharedCheck_918_ = !lean_is_exclusive(v___x_906_);
if (v_isSharedCheck_918_ == 0)
{
v___x_909_ = v___x_906_;
v_isShared_910_ = v_isSharedCheck_918_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_a_907_);
lean_dec(v___x_906_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_918_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v_leInst_x3f_911_; 
v_leInst_x3f_911_ = lean_ctor_get(v_a_907_, 5);
lean_inc(v_leInst_x3f_911_);
lean_dec(v_a_907_);
if (lean_obj_tag(v_leInst_x3f_911_) == 1)
{
lean_object* v_val_912_; lean_object* v___x_914_; 
v_val_912_ = lean_ctor_get(v_leInst_x3f_911_, 0);
lean_inc(v_val_912_);
lean_dec_ref_known(v_leInst_x3f_911_, 1);
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 0, v_val_912_);
v___x_914_ = v___x_909_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v_val_912_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
else
{
lean_object* v___x_916_; lean_object* v___x_917_; 
lean_dec(v_leInst_x3f_911_);
lean_del_object(v___x_909_);
v___x_916_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLEInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLEInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLEInst___closed__1);
v___x_917_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_916_, v_a_901_, v_a_902_, v_a_903_, v_a_904_);
return v___x_917_;
}
}
}
else
{
lean_object* v_a_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_926_; 
v_a_919_ = lean_ctor_get(v___x_906_, 0);
v_isSharedCheck_926_ = !lean_is_exclusive(v___x_906_);
if (v_isSharedCheck_926_ == 0)
{
v___x_921_ = v___x_906_;
v_isShared_922_ = v_isSharedCheck_926_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_a_919_);
lean_dec(v___x_906_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_926_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___x_924_; 
if (v_isShared_922_ == 0)
{
v___x_924_ = v___x_921_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v_a_919_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
return v___x_924_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLEInst___boxed(lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l_Lean_Meta_Grind_Arith_Linear_getLEInst(v_a_927_, v_a_928_, v_a_929_, v_a_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_, v_a_937_);
lean_dec(v_a_937_);
lean_dec_ref(v_a_936_);
lean_dec(v_a_935_);
lean_dec_ref(v_a_934_);
lean_dec(v_a_933_);
lean_dec_ref(v_a_932_);
lean_dec(v_a_931_);
lean_dec_ref(v_a_930_);
lean_dec(v_a_929_);
lean_dec(v_a_928_);
lean_dec(v_a_927_);
return v_res_939_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLTInst___closed__1(void){
_start:
{
lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_941_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLTInst___closed__0));
v___x_942_ = l_Lean_stringToMessageData(v___x_941_);
return v___x_942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLTInst(lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_){
_start:
{
lean_object* v___x_955_; 
v___x_955_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_, v_a_948_, v_a_949_, v_a_950_, v_a_951_, v_a_952_, v_a_953_);
if (lean_obj_tag(v___x_955_) == 0)
{
lean_object* v_a_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_967_; 
v_a_956_ = lean_ctor_get(v___x_955_, 0);
v_isSharedCheck_967_ = !lean_is_exclusive(v___x_955_);
if (v_isSharedCheck_967_ == 0)
{
v___x_958_ = v___x_955_;
v_isShared_959_ = v_isSharedCheck_967_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_a_956_);
lean_dec(v___x_955_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_967_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v_ltInst_x3f_960_; 
v_ltInst_x3f_960_ = lean_ctor_get(v_a_956_, 6);
lean_inc(v_ltInst_x3f_960_);
lean_dec(v_a_956_);
if (lean_obj_tag(v_ltInst_x3f_960_) == 1)
{
lean_object* v_val_961_; lean_object* v___x_963_; 
v_val_961_ = lean_ctor_get(v_ltInst_x3f_960_, 0);
lean_inc(v_val_961_);
lean_dec_ref_known(v_ltInst_x3f_960_, 1);
if (v_isShared_959_ == 0)
{
lean_ctor_set(v___x_958_, 0, v_val_961_);
v___x_963_ = v___x_958_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v_val_961_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
else
{
lean_object* v___x_965_; lean_object* v___x_966_; 
lean_dec(v_ltInst_x3f_960_);
lean_del_object(v___x_958_);
v___x_965_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLTInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLTInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLTInst___closed__1);
v___x_966_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_965_, v_a_950_, v_a_951_, v_a_952_, v_a_953_);
return v___x_966_;
}
}
}
else
{
lean_object* v_a_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_975_; 
v_a_968_ = lean_ctor_get(v___x_955_, 0);
v_isSharedCheck_975_ = !lean_is_exclusive(v___x_955_);
if (v_isSharedCheck_975_ == 0)
{
v___x_970_ = v___x_955_;
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_a_968_);
lean_dec(v___x_955_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_975_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_973_; 
if (v_isShared_971_ == 0)
{
v___x_973_ = v___x_970_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v_a_968_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
return v___x_973_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLTInst___boxed(lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_){
_start:
{
lean_object* v_res_988_; 
v_res_988_ = l_Lean_Meta_Grind_Arith_Linear_getLTInst(v_a_976_, v_a_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_);
lean_dec(v_a_986_);
lean_dec_ref(v_a_985_);
lean_dec(v_a_984_);
lean_dec_ref(v_a_983_);
lean_dec(v_a_982_);
lean_dec_ref(v_a_981_);
lean_dec(v_a_980_);
lean_dec_ref(v_a_979_);
lean_dec(v_a_978_);
lean_dec(v_a_977_);
lean_dec(v_a_976_);
return v_res_988_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___closed__1(void){
_start:
{
lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_990_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___closed__0));
v___x_991_ = l_Lean_stringToMessageData(v___x_990_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst(lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_){
_start:
{
lean_object* v___x_1004_; 
v___x_1004_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_992_, v_a_993_, v_a_994_, v_a_995_, v_a_996_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_, v_a_1001_, v_a_1002_);
if (lean_obj_tag(v___x_1004_) == 0)
{
lean_object* v_a_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1016_; 
v_a_1005_ = lean_ctor_get(v___x_1004_, 0);
v_isSharedCheck_1016_ = !lean_is_exclusive(v___x_1004_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_1007_ = v___x_1004_;
v_isShared_1008_ = v_isSharedCheck_1016_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_a_1005_);
lean_dec(v___x_1004_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1016_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v_lawfulOrderLTInst_x3f_1009_; 
v_lawfulOrderLTInst_x3f_1009_ = lean_ctor_get(v_a_1005_, 7);
lean_inc(v_lawfulOrderLTInst_x3f_1009_);
lean_dec(v_a_1005_);
if (lean_obj_tag(v_lawfulOrderLTInst_x3f_1009_) == 1)
{
lean_object* v_val_1010_; lean_object* v___x_1012_; 
v_val_1010_ = lean_ctor_get(v_lawfulOrderLTInst_x3f_1009_, 0);
lean_inc(v_val_1010_);
lean_dec_ref_known(v_lawfulOrderLTInst_x3f_1009_, 1);
if (v_isShared_1008_ == 0)
{
lean_ctor_set(v___x_1007_, 0, v_val_1010_);
v___x_1012_ = v___x_1007_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_val_1010_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
else
{
lean_object* v___x_1014_; lean_object* v___x_1015_; 
lean_dec(v_lawfulOrderLTInst_x3f_1009_);
lean_del_object(v___x_1007_);
v___x_1014_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___closed__1);
v___x_1015_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_1014_, v_a_999_, v_a_1000_, v_a_1001_, v_a_1002_);
return v___x_1015_;
}
}
}
else
{
lean_object* v_a_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1024_; 
v_a_1017_ = lean_ctor_get(v___x_1004_, 0);
v_isSharedCheck_1024_ = !lean_is_exclusive(v___x_1004_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_1019_ = v___x_1004_;
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_a_1017_);
lean_dec(v___x_1004_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1022_; 
if (v_isShared_1020_ == 0)
{
v___x_1022_ = v___x_1019_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v_a_1017_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
return v___x_1022_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___boxed(lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst(v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_);
lean_dec(v_a_1035_);
lean_dec_ref(v_a_1034_);
lean_dec(v_a_1033_);
lean_dec_ref(v_a_1032_);
lean_dec(v_a_1031_);
lean_dec_ref(v_a_1030_);
lean_dec(v_a_1029_);
lean_dec_ref(v_a_1028_);
lean_dec(v_a_1027_);
lean_dec(v_a_1026_);
lean_dec(v_a_1025_);
return v_res_1037_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___closed__1(void){
_start:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1039_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___closed__0));
v___x_1040_ = l_Lean_stringToMessageData(v___x_1039_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst(lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_){
_start:
{
lean_object* v___x_1053_; 
v___x_1053_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_);
if (lean_obj_tag(v___x_1053_) == 0)
{
lean_object* v_a_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1065_; 
v_a_1054_ = lean_ctor_get(v___x_1053_, 0);
v_isSharedCheck_1065_ = !lean_is_exclusive(v___x_1053_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1056_ = v___x_1053_;
v_isShared_1057_ = v_isSharedCheck_1065_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_a_1054_);
lean_dec(v___x_1053_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1065_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v_isPreorderInst_x3f_1058_; 
v_isPreorderInst_x3f_1058_ = lean_ctor_get(v_a_1054_, 8);
lean_inc(v_isPreorderInst_x3f_1058_);
lean_dec(v_a_1054_);
if (lean_obj_tag(v_isPreorderInst_x3f_1058_) == 1)
{
lean_object* v_val_1059_; lean_object* v___x_1061_; 
v_val_1059_ = lean_ctor_get(v_isPreorderInst_x3f_1058_, 0);
lean_inc(v_val_1059_);
lean_dec_ref_known(v_isPreorderInst_x3f_1058_, 1);
if (v_isShared_1057_ == 0)
{
lean_ctor_set(v___x_1056_, 0, v_val_1059_);
v___x_1061_ = v___x_1056_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_val_1059_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
else
{
lean_object* v___x_1063_; lean_object* v___x_1064_; 
lean_dec(v_isPreorderInst_x3f_1058_);
lean_del_object(v___x_1056_);
v___x_1063_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___closed__1);
v___x_1064_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_1063_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_);
return v___x_1064_;
}
}
}
else
{
lean_object* v_a_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1073_; 
v_a_1066_ = lean_ctor_get(v___x_1053_, 0);
v_isSharedCheck_1073_ = !lean_is_exclusive(v___x_1053_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1068_ = v___x_1053_;
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_a_1066_);
lean_dec(v___x_1053_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1071_; 
if (v_isShared_1069_ == 0)
{
v___x_1071_ = v___x_1068_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v_a_1066_);
v___x_1071_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
return v___x_1071_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___boxed(lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_){
_start:
{
lean_object* v_res_1086_; 
v_res_1086_ = l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst(v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_);
lean_dec(v_a_1084_);
lean_dec_ref(v_a_1083_);
lean_dec(v_a_1082_);
lean_dec_ref(v_a_1081_);
lean_dec(v_a_1080_);
lean_dec_ref(v_a_1079_);
lean_dec(v_a_1078_);
lean_dec_ref(v_a_1077_);
lean_dec(v_a_1076_);
lean_dec(v_a_1075_);
lean_dec(v_a_1074_);
return v_res_1086_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1(void){
_start:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1088_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__0));
v___x_1089_ = l_Lean_stringToMessageData(v___x_1088_);
return v___x_1089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst(lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_){
_start:
{
lean_object* v___x_1102_; 
v___x_1102_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_);
if (lean_obj_tag(v___x_1102_) == 0)
{
lean_object* v_a_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1114_; 
v_a_1103_ = lean_ctor_get(v___x_1102_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1102_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1105_ = v___x_1102_;
v_isShared_1106_ = v_isSharedCheck_1114_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_a_1103_);
lean_dec(v___x_1102_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1114_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v_orderedAddInst_x3f_1107_; 
v_orderedAddInst_x3f_1107_ = lean_ctor_get(v_a_1103_, 9);
lean_inc(v_orderedAddInst_x3f_1107_);
lean_dec(v_a_1103_);
if (lean_obj_tag(v_orderedAddInst_x3f_1107_) == 1)
{
lean_object* v_val_1108_; lean_object* v___x_1110_; 
v_val_1108_ = lean_ctor_get(v_orderedAddInst_x3f_1107_, 0);
lean_inc(v_val_1108_);
lean_dec_ref_known(v_orderedAddInst_x3f_1107_, 1);
if (v_isShared_1106_ == 0)
{
lean_ctor_set(v___x_1105_, 0, v_val_1108_);
v___x_1110_ = v___x_1105_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_val_1108_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
return v___x_1110_;
}
}
else
{
lean_object* v___x_1112_; lean_object* v___x_1113_; 
lean_dec(v_orderedAddInst_x3f_1107_);
lean_del_object(v___x_1105_);
v___x_1112_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1);
v___x_1113_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_1112_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_);
return v___x_1113_;
}
}
}
else
{
lean_object* v_a_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1122_; 
v_a_1115_ = lean_ctor_get(v___x_1102_, 0);
v_isSharedCheck_1122_ = !lean_is_exclusive(v___x_1102_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1117_ = v___x_1102_;
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_a_1115_);
lean_dec(v___x_1102_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v___x_1120_; 
if (v_isShared_1118_ == 0)
{
v___x_1120_ = v___x_1117_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_a_1115_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
return v___x_1120_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___boxed(lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_){
_start:
{
lean_object* v_res_1135_; 
v_res_1135_ = l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst(v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v_a_1133_);
lean_dec(v_a_1133_);
lean_dec_ref(v_a_1132_);
lean_dec(v_a_1131_);
lean_dec_ref(v_a_1130_);
lean_dec(v_a_1129_);
lean_dec_ref(v_a_1128_);
lean_dec(v_a_1127_);
lean_dec_ref(v_a_1126_);
lean_dec(v_a_1125_);
lean_dec(v_a_1124_);
lean_dec(v_a_1123_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isOrderedAdd(lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_){
_start:
{
lean_object* v___x_1148_; 
v___x_1148_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_);
if (lean_obj_tag(v___x_1148_) == 0)
{
lean_object* v_a_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1164_; 
v_a_1149_ = lean_ctor_get(v___x_1148_, 0);
v_isSharedCheck_1164_ = !lean_is_exclusive(v___x_1148_);
if (v_isSharedCheck_1164_ == 0)
{
v___x_1151_ = v___x_1148_;
v_isShared_1152_ = v_isSharedCheck_1164_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_a_1149_);
lean_dec(v___x_1148_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1164_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v_orderedAddInst_x3f_1153_; 
v_orderedAddInst_x3f_1153_ = lean_ctor_get(v_a_1149_, 9);
lean_inc(v_orderedAddInst_x3f_1153_);
lean_dec(v_a_1149_);
if (lean_obj_tag(v_orderedAddInst_x3f_1153_) == 0)
{
uint8_t v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1157_; 
v___x_1154_ = 0;
v___x_1155_ = lean_box(v___x_1154_);
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 0, v___x_1155_);
v___x_1157_ = v___x_1151_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v___x_1155_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
else
{
uint8_t v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1162_; 
lean_dec_ref_known(v_orderedAddInst_x3f_1153_, 1);
v___x_1159_ = 1;
v___x_1160_ = lean_box(v___x_1159_);
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 0, v___x_1160_);
v___x_1162_ = v___x_1151_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v___x_1160_);
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
else
{
lean_object* v_a_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1172_; 
v_a_1165_ = lean_ctor_get(v___x_1148_, 0);
v_isSharedCheck_1172_ = !lean_is_exclusive(v___x_1148_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1167_ = v___x_1148_;
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_a_1165_);
lean_dec(v___x_1148_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v___x_1170_; 
if (v_isShared_1168_ == 0)
{
v___x_1170_ = v___x_1167_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v_a_1165_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isOrderedAdd___boxed(lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_){
_start:
{
lean_object* v_res_1185_; 
v_res_1185_ = l_Lean_Meta_Grind_Arith_Linear_isOrderedAdd(v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_, v_a_1183_);
lean_dec(v_a_1183_);
lean_dec_ref(v_a_1182_);
lean_dec(v_a_1181_);
lean_dec_ref(v_a_1180_);
lean_dec(v_a_1179_);
lean_dec_ref(v_a_1178_);
lean_dec(v_a_1177_);
lean_dec_ref(v_a_1176_);
lean_dec(v_a_1175_);
lean_dec(v_a_1174_);
lean_dec(v_a_1173_);
return v_res_1185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___redArg___lam__0(lean_object* v_toPure_1186_, lean_object* v_inst_1187_, lean_object* v_inst_1188_, lean_object* v_____do__lift_1189_){
_start:
{
lean_object* v_ltFn_x3f_1190_; 
v_ltFn_x3f_1190_ = lean_ctor_get(v_____do__lift_1189_, 21);
lean_inc(v_ltFn_x3f_1190_);
lean_dec_ref(v_____do__lift_1189_);
if (lean_obj_tag(v_ltFn_x3f_1190_) == 1)
{
lean_object* v_val_1191_; lean_object* v___x_1192_; 
lean_dec_ref(v_inst_1188_);
lean_dec_ref(v_inst_1187_);
v_val_1191_ = lean_ctor_get(v_ltFn_x3f_1190_, 0);
lean_inc(v_val_1191_);
lean_dec_ref_known(v_ltFn_x3f_1190_, 1);
v___x_1192_ = lean_apply_2(v_toPure_1186_, lean_box(0), v_val_1191_);
return v___x_1192_;
}
else
{
lean_object* v___x_1193_; lean_object* v___x_1194_; 
lean_dec(v_ltFn_x3f_1190_);
lean_dec(v_toPure_1186_);
v___x_1193_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1);
v___x_1194_ = l_Lean_throwError___redArg(v_inst_1187_, v_inst_1188_, v___x_1193_);
return v___x_1194_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___redArg(lean_object* v_inst_1195_, lean_object* v_inst_1196_, lean_object* v_inst_1197_){
_start:
{
lean_object* v_toApplicative_1198_; lean_object* v_toBind_1199_; lean_object* v_toPure_1200_; lean_object* v___f_1201_; lean_object* v___x_1202_; 
v_toApplicative_1198_ = lean_ctor_get(v_inst_1195_, 0);
v_toBind_1199_ = lean_ctor_get(v_inst_1195_, 1);
lean_inc(v_toBind_1199_);
v_toPure_1200_ = lean_ctor_get(v_toApplicative_1198_, 1);
lean_inc(v_toPure_1200_);
v___f_1201_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_getLtFn___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1201_, 0, v_toPure_1200_);
lean_closure_set(v___f_1201_, 1, v_inst_1195_);
lean_closure_set(v___f_1201_, 2, v_inst_1196_);
v___x_1202_ = lean_apply_4(v_toBind_1199_, lean_box(0), lean_box(0), v_inst_1197_, v___f_1201_);
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn(lean_object* v_m_1203_, lean_object* v_inst_1204_, lean_object* v_inst_1205_, lean_object* v_inst_1206_){
_start:
{
lean_object* v___x_1207_; 
v___x_1207_ = l_Lean_Meta_Grind_Arith_Linear_getLtFn___redArg(v_inst_1204_, v_inst_1205_, v_inst_1206_);
return v___x_1207_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___x_1209_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0___closed__0));
v___x_1210_ = l_Lean_stringToMessageData(v___x_1209_);
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0(lean_object* v_toPure_1211_, lean_object* v_inst_1212_, lean_object* v_inst_1213_, lean_object* v_____do__lift_1214_){
_start:
{
lean_object* v_leFn_x3f_1215_; 
v_leFn_x3f_1215_ = lean_ctor_get(v_____do__lift_1214_, 20);
lean_inc(v_leFn_x3f_1215_);
lean_dec_ref(v_____do__lift_1214_);
if (lean_obj_tag(v_leFn_x3f_1215_) == 1)
{
lean_object* v_val_1216_; lean_object* v___x_1217_; 
lean_dec_ref(v_inst_1213_);
lean_dec_ref(v_inst_1212_);
v_val_1216_ = lean_ctor_get(v_leFn_x3f_1215_, 0);
lean_inc(v_val_1216_);
lean_dec_ref_known(v_leFn_x3f_1215_, 1);
v___x_1217_ = lean_apply_2(v_toPure_1211_, lean_box(0), v_val_1216_);
return v___x_1217_;
}
else
{
lean_object* v___x_1218_; lean_object* v___x_1219_; 
lean_dec(v_leFn_x3f_1215_);
lean_dec(v_toPure_1211_);
v___x_1218_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0___closed__1);
v___x_1219_ = l_Lean_throwError___redArg(v_inst_1212_, v_inst_1213_, v___x_1218_);
return v___x_1219_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg(lean_object* v_inst_1220_, lean_object* v_inst_1221_, lean_object* v_inst_1222_){
_start:
{
lean_object* v_toApplicative_1223_; lean_object* v_toBind_1224_; lean_object* v_toPure_1225_; lean_object* v___f_1226_; lean_object* v___x_1227_; 
v_toApplicative_1223_ = lean_ctor_get(v_inst_1220_, 0);
v_toBind_1224_ = lean_ctor_get(v_inst_1220_, 1);
lean_inc(v_toBind_1224_);
v_toPure_1225_ = lean_ctor_get(v_toApplicative_1223_, 1);
lean_inc(v_toPure_1225_);
v___f_1226_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1226_, 0, v_toPure_1225_);
lean_closure_set(v___f_1226_, 1, v_inst_1220_);
lean_closure_set(v___f_1226_, 2, v_inst_1221_);
v___x_1227_ = lean_apply_4(v_toBind_1224_, lean_box(0), lean_box(0), v_inst_1222_, v___f_1226_);
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn(lean_object* v_m_1228_, lean_object* v_inst_1229_, lean_object* v_inst_1230_, lean_object* v_inst_1231_){
_start:
{
lean_object* v___x_1232_; 
v___x_1232_ = l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg(v_inst_1229_, v_inst_1230_, v_inst_1231_);
return v___x_1232_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___closed__1(void){
_start:
{
lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___x_1234_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___closed__0));
v___x_1235_ = l_Lean_stringToMessageData(v___x_1234_);
return v___x_1235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst(lean_object* v_a_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_){
_start:
{
lean_object* v___x_1248_; 
v___x_1248_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1236_, v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_, v_a_1244_, v_a_1245_, v_a_1246_);
if (lean_obj_tag(v___x_1248_) == 0)
{
lean_object* v_a_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1260_; 
v_a_1249_ = lean_ctor_get(v___x_1248_, 0);
v_isSharedCheck_1260_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1260_ == 0)
{
v___x_1251_ = v___x_1248_;
v_isShared_1252_ = v_isSharedCheck_1260_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_a_1249_);
lean_dec(v___x_1248_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1260_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v_isLinearInst_x3f_1253_; 
v_isLinearInst_x3f_1253_ = lean_ctor_get(v_a_1249_, 10);
lean_inc(v_isLinearInst_x3f_1253_);
lean_dec(v_a_1249_);
if (lean_obj_tag(v_isLinearInst_x3f_1253_) == 1)
{
lean_object* v_val_1254_; lean_object* v___x_1256_; 
v_val_1254_ = lean_ctor_get(v_isLinearInst_x3f_1253_, 0);
lean_inc(v_val_1254_);
lean_dec_ref_known(v_isLinearInst_x3f_1253_, 1);
if (v_isShared_1252_ == 0)
{
lean_ctor_set(v___x_1251_, 0, v_val_1254_);
v___x_1256_ = v___x_1251_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v_val_1254_);
v___x_1256_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
return v___x_1256_;
}
}
else
{
lean_object* v___x_1258_; lean_object* v___x_1259_; 
lean_dec(v_isLinearInst_x3f_1253_);
lean_del_object(v___x_1251_);
v___x_1258_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___closed__1);
v___x_1259_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_1258_, v_a_1243_, v_a_1244_, v_a_1245_, v_a_1246_);
return v___x_1259_;
}
}
}
else
{
lean_object* v_a_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1268_; 
v_a_1261_ = lean_ctor_get(v___x_1248_, 0);
v_isSharedCheck_1268_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1263_ = v___x_1248_;
v_isShared_1264_ = v_isSharedCheck_1268_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_a_1261_);
lean_dec(v___x_1248_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1268_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1266_; 
if (v_isShared_1264_ == 0)
{
v___x_1266_ = v___x_1263_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v_a_1261_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
return v___x_1266_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___boxed(lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_){
_start:
{
lean_object* v_res_1281_; 
v_res_1281_ = l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst(v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_, v_a_1279_);
lean_dec(v_a_1279_);
lean_dec_ref(v_a_1278_);
lean_dec(v_a_1277_);
lean_dec_ref(v_a_1276_);
lean_dec(v_a_1275_);
lean_dec_ref(v_a_1274_);
lean_dec(v_a_1273_);
lean_dec_ref(v_a_1272_);
lean_dec(v_a_1271_);
lean_dec(v_a_1270_);
lean_dec(v_a_1269_);
return v_res_1281_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getRingInst___closed__1(void){
_start:
{
lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1283_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getRingInst___closed__0));
v___x_1284_ = l_Lean_stringToMessageData(v___x_1283_);
return v___x_1284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getRingInst(lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_){
_start:
{
lean_object* v___x_1297_; 
v___x_1297_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_);
if (lean_obj_tag(v___x_1297_) == 0)
{
lean_object* v_a_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1309_; 
v_a_1298_ = lean_ctor_get(v___x_1297_, 0);
v_isSharedCheck_1309_ = !lean_is_exclusive(v___x_1297_);
if (v_isSharedCheck_1309_ == 0)
{
v___x_1300_ = v___x_1297_;
v_isShared_1301_ = v_isSharedCheck_1309_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_a_1298_);
lean_dec(v___x_1297_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1309_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v_ringInst_x3f_1302_; 
v_ringInst_x3f_1302_ = lean_ctor_get(v_a_1298_, 12);
lean_inc(v_ringInst_x3f_1302_);
lean_dec(v_a_1298_);
if (lean_obj_tag(v_ringInst_x3f_1302_) == 1)
{
lean_object* v_val_1303_; lean_object* v___x_1305_; 
v_val_1303_ = lean_ctor_get(v_ringInst_x3f_1302_, 0);
lean_inc(v_val_1303_);
lean_dec_ref_known(v_ringInst_x3f_1302_, 1);
if (v_isShared_1301_ == 0)
{
lean_ctor_set(v___x_1300_, 0, v_val_1303_);
v___x_1305_ = v___x_1300_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v_val_1303_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
return v___x_1305_;
}
}
else
{
lean_object* v___x_1307_; lean_object* v___x_1308_; 
lean_dec(v_ringInst_x3f_1302_);
lean_del_object(v___x_1300_);
v___x_1307_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getRingInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getRingInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getRingInst___closed__1);
v___x_1308_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_1307_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_);
return v___x_1308_;
}
}
}
else
{
lean_object* v_a_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1317_; 
v_a_1310_ = lean_ctor_get(v___x_1297_, 0);
v_isSharedCheck_1317_ = !lean_is_exclusive(v___x_1297_);
if (v_isSharedCheck_1317_ == 0)
{
v___x_1312_ = v___x_1297_;
v_isShared_1313_ = v_isSharedCheck_1317_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_a_1310_);
lean_dec(v___x_1297_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1317_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v___x_1315_; 
if (v_isShared_1313_ == 0)
{
v___x_1315_ = v___x_1312_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v_a_1310_);
v___x_1315_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
return v___x_1315_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getRingInst___boxed(lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_){
_start:
{
lean_object* v_res_1330_; 
v_res_1330_ = l_Lean_Meta_Grind_Arith_Linear_getRingInst(v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_);
lean_dec(v_a_1328_);
lean_dec_ref(v_a_1327_);
lean_dec(v_a_1326_);
lean_dec_ref(v_a_1325_);
lean_dec(v_a_1324_);
lean_dec_ref(v_a_1323_);
lean_dec(v_a_1322_);
lean_dec_ref(v_a_1321_);
lean_dec(v_a_1320_);
lean_dec(v_a_1319_);
lean_dec(v_a_1318_);
return v_res_1330_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___closed__1(void){
_start:
{
lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1332_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___closed__0));
v___x_1333_ = l_Lean_stringToMessageData(v___x_1332_);
return v___x_1333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getCommRingInst(lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_){
_start:
{
lean_object* v___x_1346_; 
v___x_1346_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_);
if (lean_obj_tag(v___x_1346_) == 0)
{
lean_object* v_a_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1358_; 
v_a_1347_ = lean_ctor_get(v___x_1346_, 0);
v_isSharedCheck_1358_ = !lean_is_exclusive(v___x_1346_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1349_ = v___x_1346_;
v_isShared_1350_ = v_isSharedCheck_1358_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_a_1347_);
lean_dec(v___x_1346_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1358_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v_commRingInst_x3f_1351_; 
v_commRingInst_x3f_1351_ = lean_ctor_get(v_a_1347_, 13);
lean_inc(v_commRingInst_x3f_1351_);
lean_dec(v_a_1347_);
if (lean_obj_tag(v_commRingInst_x3f_1351_) == 1)
{
lean_object* v_val_1352_; lean_object* v___x_1354_; 
v_val_1352_ = lean_ctor_get(v_commRingInst_x3f_1351_, 0);
lean_inc(v_val_1352_);
lean_dec_ref_known(v_commRingInst_x3f_1351_, 1);
if (v_isShared_1350_ == 0)
{
lean_ctor_set(v___x_1349_, 0, v_val_1352_);
v___x_1354_ = v___x_1349_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v_val_1352_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
else
{
lean_object* v___x_1356_; lean_object* v___x_1357_; 
lean_dec(v_commRingInst_x3f_1351_);
lean_del_object(v___x_1349_);
v___x_1356_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___closed__1);
v___x_1357_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_1356_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_);
return v___x_1357_;
}
}
}
else
{
lean_object* v_a_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1366_; 
v_a_1359_ = lean_ctor_get(v___x_1346_, 0);
v_isSharedCheck_1366_ = !lean_is_exclusive(v___x_1346_);
if (v_isSharedCheck_1366_ == 0)
{
v___x_1361_ = v___x_1346_;
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_a_1359_);
lean_dec(v___x_1346_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v___x_1364_; 
if (v_isShared_1362_ == 0)
{
v___x_1364_ = v___x_1361_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_a_1359_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___boxed(lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_){
_start:
{
lean_object* v_res_1379_; 
v_res_1379_ = l_Lean_Meta_Grind_Arith_Linear_getCommRingInst(v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_);
lean_dec(v_a_1377_);
lean_dec_ref(v_a_1376_);
lean_dec(v_a_1375_);
lean_dec_ref(v_a_1374_);
lean_dec(v_a_1373_);
lean_dec_ref(v_a_1372_);
lean_dec(v_a_1371_);
lean_dec_ref(v_a_1370_);
lean_dec(v_a_1369_);
lean_dec(v_a_1368_);
lean_dec(v_a_1367_);
return v_res_1379_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___closed__1(void){
_start:
{
lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1381_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___closed__0));
v___x_1382_ = l_Lean_stringToMessageData(v___x_1381_);
return v___x_1382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst(lean_object* v_a_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_){
_start:
{
lean_object* v___x_1395_; 
v___x_1395_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1383_, v_a_1384_, v_a_1385_, v_a_1386_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_);
if (lean_obj_tag(v___x_1395_) == 0)
{
lean_object* v_a_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1407_; 
v_a_1396_ = lean_ctor_get(v___x_1395_, 0);
v_isSharedCheck_1407_ = !lean_is_exclusive(v___x_1395_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1398_ = v___x_1395_;
v_isShared_1399_ = v_isSharedCheck_1407_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_a_1396_);
lean_dec(v___x_1395_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1407_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v_orderedRingInst_x3f_1400_; 
v_orderedRingInst_x3f_1400_ = lean_ctor_get(v_a_1396_, 14);
lean_inc(v_orderedRingInst_x3f_1400_);
lean_dec(v_a_1396_);
if (lean_obj_tag(v_orderedRingInst_x3f_1400_) == 1)
{
lean_object* v_val_1401_; lean_object* v___x_1403_; 
v_val_1401_ = lean_ctor_get(v_orderedRingInst_x3f_1400_, 0);
lean_inc(v_val_1401_);
lean_dec_ref_known(v_orderedRingInst_x3f_1400_, 1);
if (v_isShared_1399_ == 0)
{
lean_ctor_set(v___x_1398_, 0, v_val_1401_);
v___x_1403_ = v___x_1398_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v_val_1401_);
v___x_1403_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
return v___x_1403_;
}
}
else
{
lean_object* v___x_1405_; lean_object* v___x_1406_; 
lean_dec(v_orderedRingInst_x3f_1400_);
lean_del_object(v___x_1398_);
v___x_1405_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___closed__1);
v___x_1406_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_1405_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_);
return v___x_1406_;
}
}
}
else
{
lean_object* v_a_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1415_; 
v_a_1408_ = lean_ctor_get(v___x_1395_, 0);
v_isSharedCheck_1415_ = !lean_is_exclusive(v___x_1395_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1410_ = v___x_1395_;
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_a_1408_);
lean_dec(v___x_1395_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1413_; 
if (v_isShared_1411_ == 0)
{
v___x_1413_ = v___x_1410_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_a_1408_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
return v___x_1413_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___boxed(lean_object* v_a_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_){
_start:
{
lean_object* v_res_1428_; 
v_res_1428_ = l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst(v_a_1416_, v_a_1417_, v_a_1418_, v_a_1419_, v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_, v_a_1424_, v_a_1425_, v_a_1426_);
lean_dec(v_a_1426_);
lean_dec_ref(v_a_1425_);
lean_dec(v_a_1424_);
lean_dec_ref(v_a_1423_);
lean_dec(v_a_1422_);
lean_dec_ref(v_a_1421_);
lean_dec(v_a_1420_);
lean_dec_ref(v_a_1419_);
lean_dec(v_a_1418_);
lean_dec(v_a_1417_);
lean_dec(v_a_1416_);
return v_res_1428_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_eval_x3f_go_spec__0(lean_object* v_a_1429_){
_start:
{
lean_object* v___x_1430_; 
v___x_1430_ = l_Rat_ofInt(v_a_1429_);
return v___x_1430_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_eval_x3f_go(lean_object* v_a_1431_, lean_object* v_v_1432_, lean_object* v_a_1433_){
_start:
{
if (lean_obj_tag(v_a_1433_) == 0)
{
lean_object* v___x_1434_; 
v___x_1434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1434_, 0, v_v_1432_);
return v___x_1434_;
}
else
{
lean_object* v_k_1435_; lean_object* v_v_1436_; lean_object* v_p_1437_; lean_object* v_size_1438_; uint8_t v___x_1439_; 
v_k_1435_ = lean_ctor_get(v_a_1433_, 0);
lean_inc(v_k_1435_);
v_v_1436_ = lean_ctor_get(v_a_1433_, 1);
lean_inc(v_v_1436_);
v_p_1437_ = lean_ctor_get(v_a_1433_, 2);
lean_inc(v_p_1437_);
lean_dec_ref_known(v_a_1433_, 3);
v_size_1438_ = lean_ctor_get(v_a_1431_, 2);
v___x_1439_ = lean_nat_dec_lt(v_v_1436_, v_size_1438_);
if (v___x_1439_ == 0)
{
lean_object* v___x_1440_; 
lean_dec(v_p_1437_);
lean_dec(v_v_1436_);
lean_dec(v_k_1435_);
lean_dec_ref(v_v_1432_);
v___x_1440_ = lean_box(0);
return v___x_1440_;
}
else
{
lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; 
v___x_1441_ = l_instInhabitedRat;
v___x_1442_ = l_Rat_ofInt(v_k_1435_);
v___x_1443_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1441_, v_a_1431_, v_v_1436_);
lean_dec(v_v_1436_);
v___x_1444_ = l_Rat_mul(v___x_1442_, v___x_1443_);
lean_dec_ref(v___x_1442_);
v___x_1445_ = l_Rat_add(v_v_1432_, v___x_1444_);
v_v_1432_ = v___x_1445_;
v_a_1433_ = v_p_1437_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_eval_x3f_go___boxed(lean_object* v_a_1447_, lean_object* v_v_1448_, lean_object* v_a_1449_){
_start:
{
lean_object* v_res_1450_; 
v_res_1450_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_eval_x3f_go(v_a_1447_, v_v_1448_, v_a_1449_);
lean_dec_ref(v_a_1447_);
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Grind_Linarith_Poly_eval_x3f_spec__0(lean_object* v_a_1451_){
_start:
{
lean_object* v___x_1452_; lean_object* v___x_1453_; 
v___x_1452_ = lean_nat_to_int(v_a_1451_);
v___x_1453_ = l_Rat_ofInt(v___x_1452_);
return v___x_1453_;
}
}
static lean_object* _init_l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0(void){
_start:
{
lean_object* v___x_1454_; lean_object* v___x_1455_; 
v___x_1454_ = lean_unsigned_to_nat(0u);
v___x_1455_ = l_Nat_cast___at___00Lean_Grind_Linarith_Poly_eval_x3f_spec__0(v___x_1454_);
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_eval_x3f(lean_object* v_p_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_){
_start:
{
lean_object* v___x_1469_; 
v___x_1469_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1457_, v_a_1458_, v_a_1459_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_);
if (lean_obj_tag(v___x_1469_) == 0)
{
lean_object* v_a_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1480_; 
v_a_1470_ = lean_ctor_get(v___x_1469_, 0);
v_isSharedCheck_1480_ = !lean_is_exclusive(v___x_1469_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1472_ = v___x_1469_;
v_isShared_1473_ = v_isSharedCheck_1480_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_a_1470_);
lean_dec(v___x_1469_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1480_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v_assignment_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1478_; 
v_assignment_1474_ = lean_ctor_get(v_a_1470_, 35);
lean_inc_ref(v_assignment_1474_);
lean_dec(v_a_1470_);
v___x_1475_ = lean_obj_once(&l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0, &l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0_once, _init_l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0);
v___x_1476_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_eval_x3f_go(v_assignment_1474_, v___x_1475_, v_p_1456_);
lean_dec_ref(v_assignment_1474_);
if (v_isShared_1473_ == 0)
{
lean_ctor_set(v___x_1472_, 0, v___x_1476_);
v___x_1478_ = v___x_1472_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v___x_1476_);
v___x_1478_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
return v___x_1478_;
}
}
}
else
{
lean_object* v_a_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1488_; 
lean_dec(v_p_1456_);
v_a_1481_ = lean_ctor_get(v___x_1469_, 0);
v_isSharedCheck_1488_ = !lean_is_exclusive(v___x_1469_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1483_ = v___x_1469_;
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_a_1481_);
lean_dec(v___x_1469_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v___x_1486_; 
if (v_isShared_1484_ == 0)
{
v___x_1486_ = v___x_1483_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_a_1481_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
return v___x_1486_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_eval_x3f___boxed(lean_object* v_p_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_){
_start:
{
lean_object* v_res_1502_; 
v_res_1502_ = l_Lean_Grind_Linarith_Poly_eval_x3f(v_p_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_);
lean_dec(v_a_1500_);
lean_dec_ref(v_a_1499_);
lean_dec(v_a_1498_);
lean_dec_ref(v_a_1497_);
lean_dec(v_a_1496_);
lean_dec_ref(v_a_1495_);
lean_dec(v_a_1494_);
lean_dec_ref(v_a_1493_);
lean_dec(v_a_1492_);
lean_dec(v_a_1491_);
lean_dec(v_a_1490_);
return v_res_1502_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00Lean_Grind_Linarith_Poly_eval_x3f_spec__0_spec__0(lean_object* v_a_1503_){
_start:
{
lean_object* v___x_1504_; 
v___x_1504_ = lean_nat_to_int(v_a_1503_);
return v___x_1504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_satisfied(lean_object* v_c_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_){
_start:
{
lean_object* v_p_1518_; uint8_t v_strict_1519_; lean_object* v___x_1520_; 
v_p_1518_ = lean_ctor_get(v_c_1505_, 0);
lean_inc(v_p_1518_);
v_strict_1519_ = lean_ctor_get_uint8(v_c_1505_, sizeof(void*)*2);
lean_dec_ref(v_c_1505_);
v___x_1520_ = l_Lean_Grind_Linarith_Poly_eval_x3f(v_p_1518_, v_a_1506_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_);
if (lean_obj_tag(v___x_1520_) == 0)
{
lean_object* v_a_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1546_; 
v_a_1521_ = lean_ctor_get(v___x_1520_, 0);
v_isSharedCheck_1546_ = !lean_is_exclusive(v___x_1520_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1523_ = v___x_1520_;
v_isShared_1524_ = v_isSharedCheck_1546_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_a_1521_);
lean_dec(v___x_1520_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1546_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
if (lean_obj_tag(v_a_1521_) == 1)
{
if (v_strict_1519_ == 0)
{
lean_object* v_val_1525_; lean_object* v___x_1526_; uint8_t v___x_1527_; uint8_t v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1531_; 
v_val_1525_ = lean_ctor_get(v_a_1521_, 0);
lean_inc(v_val_1525_);
lean_dec_ref_known(v_a_1521_, 1);
v___x_1526_ = lean_obj_once(&l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0, &l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0_once, _init_l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0);
v___x_1527_ = l_Rat_instDecidableLe(v_val_1525_, v___x_1526_);
v___x_1528_ = l_Lean_Bool_toLBool(v___x_1527_);
v___x_1529_ = lean_box(v___x_1528_);
if (v_isShared_1524_ == 0)
{
lean_ctor_set(v___x_1523_, 0, v___x_1529_);
v___x_1531_ = v___x_1523_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v___x_1529_);
v___x_1531_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
return v___x_1531_;
}
}
else
{
lean_object* v_val_1533_; lean_object* v___x_1534_; uint8_t v___x_1535_; uint8_t v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1539_; 
v_val_1533_ = lean_ctor_get(v_a_1521_, 0);
lean_inc(v_val_1533_);
lean_dec_ref_known(v_a_1521_, 1);
v___x_1534_ = lean_obj_once(&l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0, &l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0_once, _init_l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0);
v___x_1535_ = l_Rat_blt(v_val_1533_, v___x_1534_);
v___x_1536_ = l_Lean_Bool_toLBool(v___x_1535_);
v___x_1537_ = lean_box(v___x_1536_);
if (v_isShared_1524_ == 0)
{
lean_ctor_set(v___x_1523_, 0, v___x_1537_);
v___x_1539_ = v___x_1523_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v___x_1537_);
v___x_1539_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
return v___x_1539_;
}
}
}
else
{
uint8_t v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1544_; 
lean_dec(v_a_1521_);
v___x_1541_ = 2;
v___x_1542_ = lean_box(v___x_1541_);
if (v_isShared_1524_ == 0)
{
lean_ctor_set(v___x_1523_, 0, v___x_1542_);
v___x_1544_ = v___x_1523_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v___x_1542_);
v___x_1544_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
return v___x_1544_;
}
}
}
}
else
{
lean_object* v_a_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1554_; 
v_a_1547_ = lean_ctor_get(v___x_1520_, 0);
v_isSharedCheck_1554_ = !lean_is_exclusive(v___x_1520_);
if (v_isSharedCheck_1554_ == 0)
{
v___x_1549_ = v___x_1520_;
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_a_1547_);
lean_dec(v___x_1520_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v___x_1552_; 
if (v_isShared_1550_ == 0)
{
v___x_1552_ = v___x_1549_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v_a_1547_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
return v___x_1552_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_satisfied___boxed(lean_object* v_c_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_){
_start:
{
lean_object* v_res_1568_; 
v_res_1568_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_satisfied(v_c_1555_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_);
lean_dec(v_a_1566_);
lean_dec_ref(v_a_1565_);
lean_dec(v_a_1564_);
lean_dec_ref(v_a_1563_);
lean_dec(v_a_1562_);
lean_dec_ref(v_a_1561_);
lean_dec(v_a_1560_);
lean_dec_ref(v_a_1559_);
lean_dec(v_a_1558_);
lean_dec(v_a_1557_);
lean_dec(v_a_1556_);
return v_res_1568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_satisfied(lean_object* v_c_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_){
_start:
{
lean_object* v_p_1582_; lean_object* v___x_1583_; 
v_p_1582_ = lean_ctor_get(v_c_1569_, 0);
lean_inc(v_p_1582_);
lean_dec_ref(v_c_1569_);
v___x_1583_ = l_Lean_Grind_Linarith_Poly_eval_x3f(v_p_1582_, v_a_1570_, v_a_1571_, v_a_1572_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_);
if (lean_obj_tag(v___x_1583_) == 0)
{
lean_object* v_a_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1603_; 
v_a_1584_ = lean_ctor_get(v___x_1583_, 0);
v_isSharedCheck_1603_ = !lean_is_exclusive(v___x_1583_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1586_ = v___x_1583_;
v_isShared_1587_ = v_isSharedCheck_1603_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_a_1584_);
lean_dec(v___x_1583_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1603_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
uint8_t v___y_1589_; 
if (lean_obj_tag(v_a_1584_) == 1)
{
lean_object* v_val_1595_; lean_object* v___x_1596_; uint8_t v___x_1597_; 
v_val_1595_ = lean_ctor_get(v_a_1584_, 0);
lean_inc(v_val_1595_);
lean_dec_ref_known(v_a_1584_, 1);
v___x_1596_ = lean_obj_once(&l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0, &l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0_once, _init_l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0);
v___x_1597_ = l_instDecidableEqRat_decEq(v_val_1595_, v___x_1596_);
lean_dec(v_val_1595_);
if (v___x_1597_ == 0)
{
uint8_t v___x_1598_; 
v___x_1598_ = 1;
v___y_1589_ = v___x_1598_;
goto v___jp_1588_;
}
else
{
uint8_t v___x_1599_; 
v___x_1599_ = 0;
v___y_1589_ = v___x_1599_;
goto v___jp_1588_;
}
}
else
{
uint8_t v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; 
lean_del_object(v___x_1586_);
lean_dec(v_a_1584_);
v___x_1600_ = 2;
v___x_1601_ = lean_box(v___x_1600_);
v___x_1602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1602_, 0, v___x_1601_);
return v___x_1602_;
}
v___jp_1588_:
{
uint8_t v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1593_; 
v___x_1590_ = l_Lean_Bool_toLBool(v___y_1589_);
v___x_1591_ = lean_box(v___x_1590_);
if (v_isShared_1587_ == 0)
{
lean_ctor_set(v___x_1586_, 0, v___x_1591_);
v___x_1593_ = v___x_1586_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v___x_1591_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
return v___x_1593_;
}
}
}
}
else
{
lean_object* v_a_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1611_; 
v_a_1604_ = lean_ctor_get(v___x_1583_, 0);
v_isSharedCheck_1611_ = !lean_is_exclusive(v___x_1583_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1606_ = v___x_1583_;
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_a_1604_);
lean_dec(v___x_1583_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v___x_1609_; 
if (v_isShared_1607_ == 0)
{
v___x_1609_ = v___x_1606_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_a_1604_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
return v___x_1609_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_satisfied___boxed(lean_object* v_c_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_){
_start:
{
lean_object* v_res_1625_; 
v_res_1625_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_satisfied(v_c_1612_, v_a_1613_, v_a_1614_, v_a_1615_, v_a_1616_, v_a_1617_, v_a_1618_, v_a_1619_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_);
lean_dec(v_a_1623_);
lean_dec_ref(v_a_1622_);
lean_dec(v_a_1621_);
lean_dec_ref(v_a_1620_);
lean_dec(v_a_1619_);
lean_dec_ref(v_a_1618_);
lean_dec(v_a_1617_);
lean_dec_ref(v_a_1616_);
lean_dec(v_a_1615_);
lean_dec(v_a_1614_);
lean_dec(v_a_1613_);
return v_res_1625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg___lam__0(lean_object* v_a_1626_, lean_object* v_x_1627_, lean_object* v_s_1628_){
_start:
{
lean_object* v_structs_1629_; lean_object* v_typeIdOf_1630_; lean_object* v_exprToStructId_1631_; lean_object* v_exprToStructIdEntries_1632_; lean_object* v_forbiddenNatModules_1633_; lean_object* v_natStructs_1634_; lean_object* v_natTypeIdOf_1635_; lean_object* v_exprToNatStructId_1636_; lean_object* v___x_1637_; uint8_t v___x_1638_; 
v_structs_1629_ = lean_ctor_get(v_s_1628_, 0);
v_typeIdOf_1630_ = lean_ctor_get(v_s_1628_, 1);
v_exprToStructId_1631_ = lean_ctor_get(v_s_1628_, 2);
v_exprToStructIdEntries_1632_ = lean_ctor_get(v_s_1628_, 3);
v_forbiddenNatModules_1633_ = lean_ctor_get(v_s_1628_, 4);
v_natStructs_1634_ = lean_ctor_get(v_s_1628_, 5);
v_natTypeIdOf_1635_ = lean_ctor_get(v_s_1628_, 6);
v_exprToNatStructId_1636_ = lean_ctor_get(v_s_1628_, 7);
v___x_1637_ = lean_array_get_size(v_structs_1629_);
v___x_1638_ = lean_nat_dec_lt(v_a_1626_, v___x_1637_);
if (v___x_1638_ == 0)
{
return v_s_1628_;
}
else
{
lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1700_; 
lean_inc_ref(v_exprToNatStructId_1636_);
lean_inc_ref(v_natTypeIdOf_1635_);
lean_inc_ref(v_natStructs_1634_);
lean_inc_ref(v_forbiddenNatModules_1633_);
lean_inc_ref(v_exprToStructIdEntries_1632_);
lean_inc_ref(v_exprToStructId_1631_);
lean_inc_ref(v_typeIdOf_1630_);
lean_inc_ref(v_structs_1629_);
v_isSharedCheck_1700_ = !lean_is_exclusive(v_s_1628_);
if (v_isSharedCheck_1700_ == 0)
{
lean_object* v_unused_1701_; lean_object* v_unused_1702_; lean_object* v_unused_1703_; lean_object* v_unused_1704_; lean_object* v_unused_1705_; lean_object* v_unused_1706_; lean_object* v_unused_1707_; lean_object* v_unused_1708_; 
v_unused_1701_ = lean_ctor_get(v_s_1628_, 7);
lean_dec(v_unused_1701_);
v_unused_1702_ = lean_ctor_get(v_s_1628_, 6);
lean_dec(v_unused_1702_);
v_unused_1703_ = lean_ctor_get(v_s_1628_, 5);
lean_dec(v_unused_1703_);
v_unused_1704_ = lean_ctor_get(v_s_1628_, 4);
lean_dec(v_unused_1704_);
v_unused_1705_ = lean_ctor_get(v_s_1628_, 3);
lean_dec(v_unused_1705_);
v_unused_1706_ = lean_ctor_get(v_s_1628_, 2);
lean_dec(v_unused_1706_);
v_unused_1707_ = lean_ctor_get(v_s_1628_, 1);
lean_dec(v_unused_1707_);
v_unused_1708_ = lean_ctor_get(v_s_1628_, 0);
lean_dec(v_unused_1708_);
v___x_1640_ = v_s_1628_;
v_isShared_1641_ = v_isSharedCheck_1700_;
goto v_resetjp_1639_;
}
else
{
lean_dec(v_s_1628_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1700_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v_v_1642_; lean_object* v_id_1643_; lean_object* v_ringId_x3f_1644_; lean_object* v_type_1645_; lean_object* v_u_1646_; lean_object* v_intModuleInst_1647_; lean_object* v_leInst_x3f_1648_; lean_object* v_ltInst_x3f_1649_; lean_object* v_lawfulOrderLTInst_x3f_1650_; lean_object* v_isPreorderInst_x3f_1651_; lean_object* v_orderedAddInst_x3f_1652_; lean_object* v_isLinearInst_x3f_1653_; lean_object* v_noNatDivInst_x3f_1654_; lean_object* v_ringInst_x3f_1655_; lean_object* v_commRingInst_x3f_1656_; lean_object* v_orderedRingInst_x3f_1657_; lean_object* v_fieldInst_x3f_1658_; lean_object* v_charInst_x3f_1659_; lean_object* v_zero_1660_; lean_object* v_ofNatZero_1661_; lean_object* v_one_x3f_1662_; lean_object* v_leFn_x3f_1663_; lean_object* v_ltFn_x3f_1664_; lean_object* v_addFn_1665_; lean_object* v_zsmulFn_1666_; lean_object* v_nsmulFn_1667_; lean_object* v_zsmulFn_x3f_1668_; lean_object* v_nsmulFn_x3f_1669_; lean_object* v_homomulFn_x3f_1670_; lean_object* v_subFn_1671_; lean_object* v_negFn_1672_; lean_object* v_vars_1673_; lean_object* v_varMap_1674_; lean_object* v_lowers_1675_; lean_object* v_uppers_1676_; lean_object* v_diseqs_1677_; lean_object* v_assignment_1678_; uint8_t v_caseSplits_1679_; lean_object* v_conflict_x3f_1680_; lean_object* v_diseqSplits_1681_; lean_object* v_elimEqs_1682_; lean_object* v_elimStack_1683_; lean_object* v_occurs_1684_; lean_object* v_ignored_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1699_; 
v_v_1642_ = lean_array_fget(v_structs_1629_, v_a_1626_);
v_id_1643_ = lean_ctor_get(v_v_1642_, 0);
v_ringId_x3f_1644_ = lean_ctor_get(v_v_1642_, 1);
v_type_1645_ = lean_ctor_get(v_v_1642_, 2);
v_u_1646_ = lean_ctor_get(v_v_1642_, 3);
v_intModuleInst_1647_ = lean_ctor_get(v_v_1642_, 4);
v_leInst_x3f_1648_ = lean_ctor_get(v_v_1642_, 5);
v_ltInst_x3f_1649_ = lean_ctor_get(v_v_1642_, 6);
v_lawfulOrderLTInst_x3f_1650_ = lean_ctor_get(v_v_1642_, 7);
v_isPreorderInst_x3f_1651_ = lean_ctor_get(v_v_1642_, 8);
v_orderedAddInst_x3f_1652_ = lean_ctor_get(v_v_1642_, 9);
v_isLinearInst_x3f_1653_ = lean_ctor_get(v_v_1642_, 10);
v_noNatDivInst_x3f_1654_ = lean_ctor_get(v_v_1642_, 11);
v_ringInst_x3f_1655_ = lean_ctor_get(v_v_1642_, 12);
v_commRingInst_x3f_1656_ = lean_ctor_get(v_v_1642_, 13);
v_orderedRingInst_x3f_1657_ = lean_ctor_get(v_v_1642_, 14);
v_fieldInst_x3f_1658_ = lean_ctor_get(v_v_1642_, 15);
v_charInst_x3f_1659_ = lean_ctor_get(v_v_1642_, 16);
v_zero_1660_ = lean_ctor_get(v_v_1642_, 17);
v_ofNatZero_1661_ = lean_ctor_get(v_v_1642_, 18);
v_one_x3f_1662_ = lean_ctor_get(v_v_1642_, 19);
v_leFn_x3f_1663_ = lean_ctor_get(v_v_1642_, 20);
v_ltFn_x3f_1664_ = lean_ctor_get(v_v_1642_, 21);
v_addFn_1665_ = lean_ctor_get(v_v_1642_, 22);
v_zsmulFn_1666_ = lean_ctor_get(v_v_1642_, 23);
v_nsmulFn_1667_ = lean_ctor_get(v_v_1642_, 24);
v_zsmulFn_x3f_1668_ = lean_ctor_get(v_v_1642_, 25);
v_nsmulFn_x3f_1669_ = lean_ctor_get(v_v_1642_, 26);
v_homomulFn_x3f_1670_ = lean_ctor_get(v_v_1642_, 27);
v_subFn_1671_ = lean_ctor_get(v_v_1642_, 28);
v_negFn_1672_ = lean_ctor_get(v_v_1642_, 29);
v_vars_1673_ = lean_ctor_get(v_v_1642_, 30);
v_varMap_1674_ = lean_ctor_get(v_v_1642_, 31);
v_lowers_1675_ = lean_ctor_get(v_v_1642_, 32);
v_uppers_1676_ = lean_ctor_get(v_v_1642_, 33);
v_diseqs_1677_ = lean_ctor_get(v_v_1642_, 34);
v_assignment_1678_ = lean_ctor_get(v_v_1642_, 35);
v_caseSplits_1679_ = lean_ctor_get_uint8(v_v_1642_, sizeof(void*)*42);
v_conflict_x3f_1680_ = lean_ctor_get(v_v_1642_, 36);
v_diseqSplits_1681_ = lean_ctor_get(v_v_1642_, 37);
v_elimEqs_1682_ = lean_ctor_get(v_v_1642_, 38);
v_elimStack_1683_ = lean_ctor_get(v_v_1642_, 39);
v_occurs_1684_ = lean_ctor_get(v_v_1642_, 40);
v_ignored_1685_ = lean_ctor_get(v_v_1642_, 41);
v_isSharedCheck_1699_ = !lean_is_exclusive(v_v_1642_);
if (v_isSharedCheck_1699_ == 0)
{
v___x_1687_ = v_v_1642_;
v_isShared_1688_ = v_isSharedCheck_1699_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_ignored_1685_);
lean_inc(v_occurs_1684_);
lean_inc(v_elimStack_1683_);
lean_inc(v_elimEqs_1682_);
lean_inc(v_diseqSplits_1681_);
lean_inc(v_conflict_x3f_1680_);
lean_inc(v_assignment_1678_);
lean_inc(v_diseqs_1677_);
lean_inc(v_uppers_1676_);
lean_inc(v_lowers_1675_);
lean_inc(v_varMap_1674_);
lean_inc(v_vars_1673_);
lean_inc(v_negFn_1672_);
lean_inc(v_subFn_1671_);
lean_inc(v_homomulFn_x3f_1670_);
lean_inc(v_nsmulFn_x3f_1669_);
lean_inc(v_zsmulFn_x3f_1668_);
lean_inc(v_nsmulFn_1667_);
lean_inc(v_zsmulFn_1666_);
lean_inc(v_addFn_1665_);
lean_inc(v_ltFn_x3f_1664_);
lean_inc(v_leFn_x3f_1663_);
lean_inc(v_one_x3f_1662_);
lean_inc(v_ofNatZero_1661_);
lean_inc(v_zero_1660_);
lean_inc(v_charInst_x3f_1659_);
lean_inc(v_fieldInst_x3f_1658_);
lean_inc(v_orderedRingInst_x3f_1657_);
lean_inc(v_commRingInst_x3f_1656_);
lean_inc(v_ringInst_x3f_1655_);
lean_inc(v_noNatDivInst_x3f_1654_);
lean_inc(v_isLinearInst_x3f_1653_);
lean_inc(v_orderedAddInst_x3f_1652_);
lean_inc(v_isPreorderInst_x3f_1651_);
lean_inc(v_lawfulOrderLTInst_x3f_1650_);
lean_inc(v_ltInst_x3f_1649_);
lean_inc(v_leInst_x3f_1648_);
lean_inc(v_intModuleInst_1647_);
lean_inc(v_u_1646_);
lean_inc(v_type_1645_);
lean_inc(v_ringId_x3f_1644_);
lean_inc(v_id_1643_);
lean_dec(v_v_1642_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1699_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v___x_1689_; lean_object* v_xs_x27_1690_; lean_object* v___x_1691_; lean_object* v___x_1693_; 
v___x_1689_ = lean_box(0);
v_xs_x27_1690_ = lean_array_fset(v_structs_1629_, v_a_1626_, v___x_1689_);
v___x_1691_ = l_Lean_Meta_Grind_Arith_shrink(v_assignment_1678_, v_x_1627_);
if (v_isShared_1688_ == 0)
{
lean_ctor_set(v___x_1687_, 35, v___x_1691_);
v___x_1693_ = v___x_1687_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v_id_1643_);
lean_ctor_set(v_reuseFailAlloc_1698_, 1, v_ringId_x3f_1644_);
lean_ctor_set(v_reuseFailAlloc_1698_, 2, v_type_1645_);
lean_ctor_set(v_reuseFailAlloc_1698_, 3, v_u_1646_);
lean_ctor_set(v_reuseFailAlloc_1698_, 4, v_intModuleInst_1647_);
lean_ctor_set(v_reuseFailAlloc_1698_, 5, v_leInst_x3f_1648_);
lean_ctor_set(v_reuseFailAlloc_1698_, 6, v_ltInst_x3f_1649_);
lean_ctor_set(v_reuseFailAlloc_1698_, 7, v_lawfulOrderLTInst_x3f_1650_);
lean_ctor_set(v_reuseFailAlloc_1698_, 8, v_isPreorderInst_x3f_1651_);
lean_ctor_set(v_reuseFailAlloc_1698_, 9, v_orderedAddInst_x3f_1652_);
lean_ctor_set(v_reuseFailAlloc_1698_, 10, v_isLinearInst_x3f_1653_);
lean_ctor_set(v_reuseFailAlloc_1698_, 11, v_noNatDivInst_x3f_1654_);
lean_ctor_set(v_reuseFailAlloc_1698_, 12, v_ringInst_x3f_1655_);
lean_ctor_set(v_reuseFailAlloc_1698_, 13, v_commRingInst_x3f_1656_);
lean_ctor_set(v_reuseFailAlloc_1698_, 14, v_orderedRingInst_x3f_1657_);
lean_ctor_set(v_reuseFailAlloc_1698_, 15, v_fieldInst_x3f_1658_);
lean_ctor_set(v_reuseFailAlloc_1698_, 16, v_charInst_x3f_1659_);
lean_ctor_set(v_reuseFailAlloc_1698_, 17, v_zero_1660_);
lean_ctor_set(v_reuseFailAlloc_1698_, 18, v_ofNatZero_1661_);
lean_ctor_set(v_reuseFailAlloc_1698_, 19, v_one_x3f_1662_);
lean_ctor_set(v_reuseFailAlloc_1698_, 20, v_leFn_x3f_1663_);
lean_ctor_set(v_reuseFailAlloc_1698_, 21, v_ltFn_x3f_1664_);
lean_ctor_set(v_reuseFailAlloc_1698_, 22, v_addFn_1665_);
lean_ctor_set(v_reuseFailAlloc_1698_, 23, v_zsmulFn_1666_);
lean_ctor_set(v_reuseFailAlloc_1698_, 24, v_nsmulFn_1667_);
lean_ctor_set(v_reuseFailAlloc_1698_, 25, v_zsmulFn_x3f_1668_);
lean_ctor_set(v_reuseFailAlloc_1698_, 26, v_nsmulFn_x3f_1669_);
lean_ctor_set(v_reuseFailAlloc_1698_, 27, v_homomulFn_x3f_1670_);
lean_ctor_set(v_reuseFailAlloc_1698_, 28, v_subFn_1671_);
lean_ctor_set(v_reuseFailAlloc_1698_, 29, v_negFn_1672_);
lean_ctor_set(v_reuseFailAlloc_1698_, 30, v_vars_1673_);
lean_ctor_set(v_reuseFailAlloc_1698_, 31, v_varMap_1674_);
lean_ctor_set(v_reuseFailAlloc_1698_, 32, v_lowers_1675_);
lean_ctor_set(v_reuseFailAlloc_1698_, 33, v_uppers_1676_);
lean_ctor_set(v_reuseFailAlloc_1698_, 34, v_diseqs_1677_);
lean_ctor_set(v_reuseFailAlloc_1698_, 35, v___x_1691_);
lean_ctor_set(v_reuseFailAlloc_1698_, 36, v_conflict_x3f_1680_);
lean_ctor_set(v_reuseFailAlloc_1698_, 37, v_diseqSplits_1681_);
lean_ctor_set(v_reuseFailAlloc_1698_, 38, v_elimEqs_1682_);
lean_ctor_set(v_reuseFailAlloc_1698_, 39, v_elimStack_1683_);
lean_ctor_set(v_reuseFailAlloc_1698_, 40, v_occurs_1684_);
lean_ctor_set(v_reuseFailAlloc_1698_, 41, v_ignored_1685_);
lean_ctor_set_uint8(v_reuseFailAlloc_1698_, sizeof(void*)*42, v_caseSplits_1679_);
v___x_1693_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
lean_object* v___x_1694_; lean_object* v___x_1696_; 
v___x_1694_ = lean_array_fset(v_xs_x27_1690_, v_a_1626_, v___x_1693_);
if (v_isShared_1641_ == 0)
{
lean_ctor_set(v___x_1640_, 0, v___x_1694_);
v___x_1696_ = v___x_1640_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v___x_1694_);
lean_ctor_set(v_reuseFailAlloc_1697_, 1, v_typeIdOf_1630_);
lean_ctor_set(v_reuseFailAlloc_1697_, 2, v_exprToStructId_1631_);
lean_ctor_set(v_reuseFailAlloc_1697_, 3, v_exprToStructIdEntries_1632_);
lean_ctor_set(v_reuseFailAlloc_1697_, 4, v_forbiddenNatModules_1633_);
lean_ctor_set(v_reuseFailAlloc_1697_, 5, v_natStructs_1634_);
lean_ctor_set(v_reuseFailAlloc_1697_, 6, v_natTypeIdOf_1635_);
lean_ctor_set(v_reuseFailAlloc_1697_, 7, v_exprToNatStructId_1636_);
v___x_1696_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
return v___x_1696_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg___lam__0___boxed(lean_object* v_a_1709_, lean_object* v_x_1710_, lean_object* v_s_1711_){
_start:
{
lean_object* v_res_1712_; 
v_res_1712_ = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg___lam__0(v_a_1709_, v_x_1710_, v_s_1711_);
lean_dec(v_x_1710_);
lean_dec(v_a_1709_);
return v_res_1712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg(lean_object* v_x_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_){
_start:
{
lean_object* v___f_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; 
lean_inc(v_a_1714_);
v___f_1717_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1717_, 0, v_a_1714_);
lean_closure_set(v___f_1717_, 1, v_x_1713_);
v___x_1718_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_1719_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1718_, v___f_1717_, v_a_1715_);
return v___x_1719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg___boxed(lean_object* v_x_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_){
_start:
{
lean_object* v_res_1724_; 
v_res_1724_ = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg(v_x_1720_, v_a_1721_, v_a_1722_);
lean_dec(v_a_1722_);
lean_dec(v_a_1721_);
return v_res_1724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom(lean_object* v_x_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_){
_start:
{
lean_object* v___x_1738_; 
v___x_1738_ = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg(v_x_1725_, v_a_1726_, v_a_1727_);
return v___x_1738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___boxed(lean_object* v_x_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_){
_start:
{
lean_object* v_res_1752_; 
v_res_1752_ = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom(v_x_1739_, v_a_1740_, v_a_1741_, v_a_1742_, v_a_1743_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_, v_a_1750_);
lean_dec(v_a_1750_);
lean_dec_ref(v_a_1749_);
lean_dec(v_a_1748_);
lean_dec_ref(v_a_1747_);
lean_dec(v_a_1746_);
lean_dec_ref(v_a_1745_);
lean_dec(v_a_1744_);
lean_dec_ref(v_a_1743_);
lean_dec(v_a_1742_);
lean_dec(v_a_1741_);
lean_dec(v_a_1740_);
return v_res_1752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getVar(lean_object* v_x_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_, lean_object* v_a_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_, lean_object* v_a_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_){
_start:
{
lean_object* v___x_1766_; 
v___x_1766_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1754_, v_a_1755_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_, v_a_1760_, v_a_1761_, v_a_1762_, v_a_1763_, v_a_1764_);
if (lean_obj_tag(v___x_1766_) == 0)
{
lean_object* v_a_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1783_; 
v_a_1767_ = lean_ctor_get(v___x_1766_, 0);
v_isSharedCheck_1783_ = !lean_is_exclusive(v___x_1766_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1769_ = v___x_1766_;
v_isShared_1770_ = v_isSharedCheck_1783_;
goto v_resetjp_1768_;
}
else
{
lean_inc(v_a_1767_);
lean_dec(v___x_1766_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1783_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v_vars_1771_; lean_object* v_size_1772_; lean_object* v___x_1773_; uint8_t v___x_1774_; 
v_vars_1771_ = lean_ctor_get(v_a_1767_, 30);
lean_inc_ref(v_vars_1771_);
lean_dec(v_a_1767_);
v_size_1772_ = lean_ctor_get(v_vars_1771_, 2);
v___x_1773_ = l_Lean_instInhabitedExpr;
v___x_1774_ = lean_nat_dec_lt(v_x_1753_, v_size_1772_);
if (v___x_1774_ == 0)
{
lean_object* v___x_1775_; lean_object* v___x_1777_; 
lean_dec_ref(v_vars_1771_);
v___x_1775_ = l_outOfBounds___redArg(v___x_1773_);
if (v_isShared_1770_ == 0)
{
lean_ctor_set(v___x_1769_, 0, v___x_1775_);
v___x_1777_ = v___x_1769_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v___x_1775_);
v___x_1777_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
return v___x_1777_;
}
}
else
{
lean_object* v___x_1779_; lean_object* v___x_1781_; 
v___x_1779_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1773_, v_vars_1771_, v_x_1753_);
lean_dec_ref(v_vars_1771_);
if (v_isShared_1770_ == 0)
{
lean_ctor_set(v___x_1769_, 0, v___x_1779_);
v___x_1781_ = v___x_1769_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v___x_1779_);
v___x_1781_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
return v___x_1781_;
}
}
}
}
else
{
lean_object* v_a_1784_; lean_object* v___x_1786_; uint8_t v_isShared_1787_; uint8_t v_isSharedCheck_1791_; 
v_a_1784_ = lean_ctor_get(v___x_1766_, 0);
v_isSharedCheck_1791_ = !lean_is_exclusive(v___x_1766_);
if (v_isSharedCheck_1791_ == 0)
{
v___x_1786_ = v___x_1766_;
v_isShared_1787_ = v_isSharedCheck_1791_;
goto v_resetjp_1785_;
}
else
{
lean_inc(v_a_1784_);
lean_dec(v___x_1766_);
v___x_1786_ = lean_box(0);
v_isShared_1787_ = v_isSharedCheck_1791_;
goto v_resetjp_1785_;
}
v_resetjp_1785_:
{
lean_object* v___x_1789_; 
if (v_isShared_1787_ == 0)
{
v___x_1789_ = v___x_1786_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v_a_1784_);
v___x_1789_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
return v___x_1789_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getVar___boxed(lean_object* v_x_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_){
_start:
{
lean_object* v_res_1805_; 
v_res_1805_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_x_1792_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_);
lean_dec(v_a_1803_);
lean_dec_ref(v_a_1802_);
lean_dec(v_a_1801_);
lean_dec_ref(v_a_1800_);
lean_dec(v_a_1799_);
lean_dec_ref(v_a_1798_);
lean_dec(v_a_1797_);
lean_dec_ref(v_a_1796_);
lean_dec(v_a_1795_);
lean_dec(v_a_1794_);
lean_dec(v_a_1793_);
lean_dec(v_x_1792_);
return v_res_1805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_inconsistent(lean_object* v_a_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_){
_start:
{
lean_object* v___x_1818_; 
v___x_1818_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_1807_);
if (lean_obj_tag(v___x_1818_) == 0)
{
lean_object* v_a_1819_; uint8_t v___x_1820_; 
v_a_1819_ = lean_ctor_get(v___x_1818_, 0);
lean_inc(v_a_1819_);
v___x_1820_ = lean_unbox(v_a_1819_);
if (v___x_1820_ == 0)
{
lean_object* v___x_1821_; 
lean_dec_ref_known(v___x_1818_, 1);
v___x_1821_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_);
if (lean_obj_tag(v___x_1821_) == 0)
{
lean_object* v_a_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1835_; 
v_a_1822_ = lean_ctor_get(v___x_1821_, 0);
v_isSharedCheck_1835_ = !lean_is_exclusive(v___x_1821_);
if (v_isSharedCheck_1835_ == 0)
{
v___x_1824_ = v___x_1821_;
v_isShared_1825_ = v_isSharedCheck_1835_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_a_1822_);
lean_dec(v___x_1821_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1835_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v_conflict_x3f_1826_; 
v_conflict_x3f_1826_ = lean_ctor_get(v_a_1822_, 36);
lean_inc(v_conflict_x3f_1826_);
lean_dec(v_a_1822_);
if (lean_obj_tag(v_conflict_x3f_1826_) == 0)
{
lean_object* v___x_1828_; 
if (v_isShared_1825_ == 0)
{
lean_ctor_set(v___x_1824_, 0, v_a_1819_);
v___x_1828_ = v___x_1824_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v_a_1819_);
v___x_1828_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
return v___x_1828_;
}
}
else
{
uint8_t v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1833_; 
lean_dec_ref_known(v_conflict_x3f_1826_, 1);
lean_dec(v_a_1819_);
v___x_1830_ = 1;
v___x_1831_ = lean_box(v___x_1830_);
if (v_isShared_1825_ == 0)
{
lean_ctor_set(v___x_1824_, 0, v___x_1831_);
v___x_1833_ = v___x_1824_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v___x_1831_);
v___x_1833_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
return v___x_1833_;
}
}
}
}
else
{
lean_object* v_a_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1843_; 
lean_dec(v_a_1819_);
v_a_1836_ = lean_ctor_get(v___x_1821_, 0);
v_isSharedCheck_1843_ = !lean_is_exclusive(v___x_1821_);
if (v_isSharedCheck_1843_ == 0)
{
v___x_1838_ = v___x_1821_;
v_isShared_1839_ = v_isSharedCheck_1843_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_a_1836_);
lean_dec(v___x_1821_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1843_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v___x_1841_; 
if (v_isShared_1839_ == 0)
{
v___x_1841_ = v___x_1838_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v_a_1836_);
v___x_1841_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
return v___x_1841_;
}
}
}
}
else
{
lean_dec(v_a_1819_);
return v___x_1818_;
}
}
else
{
return v___x_1818_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_inconsistent___boxed(lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_){
_start:
{
lean_object* v_res_1856_; 
v_res_1856_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v_a_1844_, v_a_1845_, v_a_1846_, v_a_1847_, v_a_1848_, v_a_1849_, v_a_1850_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_);
lean_dec(v_a_1854_);
lean_dec_ref(v_a_1853_);
lean_dec(v_a_1852_);
lean_dec_ref(v_a_1851_);
lean_dec(v_a_1850_);
lean_dec_ref(v_a_1849_);
lean_dec(v_a_1848_);
lean_dec_ref(v_a_1847_);
lean_dec(v_a_1846_);
lean_dec(v_a_1845_);
lean_dec(v_a_1844_);
return v_res_1856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_eliminated(lean_object* v_x_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_){
_start:
{
lean_object* v___x_1870_; 
v___x_1870_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_, v_a_1862_, v_a_1863_, v_a_1864_, v_a_1865_, v_a_1866_, v_a_1867_, v_a_1868_);
if (lean_obj_tag(v___x_1870_) == 0)
{
lean_object* v_a_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1893_; 
v_a_1871_ = lean_ctor_get(v___x_1870_, 0);
v_isSharedCheck_1893_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1873_ = v___x_1870_;
v_isShared_1874_ = v_isSharedCheck_1893_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_a_1871_);
lean_dec(v___x_1870_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1893_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v___y_1876_; lean_object* v_elimEqs_1887_; lean_object* v_size_1888_; lean_object* v___x_1889_; uint8_t v___x_1890_; 
v_elimEqs_1887_ = lean_ctor_get(v_a_1871_, 38);
lean_inc_ref(v_elimEqs_1887_);
lean_dec(v_a_1871_);
v_size_1888_ = lean_ctor_get(v_elimEqs_1887_, 2);
v___x_1889_ = lean_box(0);
v___x_1890_ = lean_nat_dec_lt(v_x_1857_, v_size_1888_);
if (v___x_1890_ == 0)
{
lean_object* v___x_1891_; 
lean_dec_ref(v_elimEqs_1887_);
v___x_1891_ = l_outOfBounds___redArg(v___x_1889_);
v___y_1876_ = v___x_1891_;
goto v___jp_1875_;
}
else
{
lean_object* v___x_1892_; 
v___x_1892_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1889_, v_elimEqs_1887_, v_x_1857_);
lean_dec_ref(v_elimEqs_1887_);
v___y_1876_ = v___x_1892_;
goto v___jp_1875_;
}
v___jp_1875_:
{
if (lean_obj_tag(v___y_1876_) == 0)
{
uint8_t v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1880_; 
v___x_1877_ = 0;
v___x_1878_ = lean_box(v___x_1877_);
if (v_isShared_1874_ == 0)
{
lean_ctor_set(v___x_1873_, 0, v___x_1878_);
v___x_1880_ = v___x_1873_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v___x_1878_);
v___x_1880_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
return v___x_1880_;
}
}
else
{
uint8_t v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1885_; 
lean_dec_ref_known(v___y_1876_, 1);
v___x_1882_ = 1;
v___x_1883_ = lean_box(v___x_1882_);
if (v_isShared_1874_ == 0)
{
lean_ctor_set(v___x_1873_, 0, v___x_1883_);
v___x_1885_ = v___x_1873_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v___x_1883_);
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
}
else
{
lean_object* v_a_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1901_; 
v_a_1894_ = lean_ctor_get(v___x_1870_, 0);
v_isSharedCheck_1901_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1896_ = v___x_1870_;
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_a_1894_);
lean_dec(v___x_1870_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1899_; 
if (v_isShared_1897_ == 0)
{
v___x_1899_ = v___x_1896_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v_a_1894_);
v___x_1899_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
return v___x_1899_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_eliminated___boxed(lean_object* v_x_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_){
_start:
{
lean_object* v_res_1915_; 
v_res_1915_ = l_Lean_Meta_Grind_Arith_Linear_eliminated(v_x_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_, v_a_1912_, v_a_1913_);
lean_dec(v_a_1913_);
lean_dec_ref(v_a_1912_);
lean_dec(v_a_1911_);
lean_dec_ref(v_a_1910_);
lean_dec(v_a_1909_);
lean_dec_ref(v_a_1908_);
lean_dec(v_a_1907_);
lean_dec_ref(v_a_1906_);
lean_dec(v_a_1905_);
lean_dec(v_a_1904_);
lean_dec(v_a_1903_);
lean_dec(v_x_1902_);
return v_res_1915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOccursOf(lean_object* v_x_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_){
_start:
{
lean_object* v___x_1929_; 
v___x_1929_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1917_, v_a_1918_, v_a_1919_, v_a_1920_, v_a_1921_, v_a_1922_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_);
if (lean_obj_tag(v___x_1929_) == 0)
{
lean_object* v_a_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1946_; 
v_a_1930_ = lean_ctor_get(v___x_1929_, 0);
v_isSharedCheck_1946_ = !lean_is_exclusive(v___x_1929_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1932_ = v___x_1929_;
v_isShared_1933_ = v_isSharedCheck_1946_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_a_1930_);
lean_dec(v___x_1929_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1946_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v_occurs_1934_; lean_object* v_size_1935_; lean_object* v___x_1936_; uint8_t v___x_1937_; 
v_occurs_1934_ = lean_ctor_get(v_a_1930_, 40);
lean_inc_ref(v_occurs_1934_);
lean_dec(v_a_1930_);
v_size_1935_ = lean_ctor_get(v_occurs_1934_, 2);
v___x_1936_ = lean_box(1);
v___x_1937_ = lean_nat_dec_lt(v_x_1916_, v_size_1935_);
if (v___x_1937_ == 0)
{
lean_object* v___x_1938_; lean_object* v___x_1940_; 
lean_dec_ref(v_occurs_1934_);
v___x_1938_ = l_outOfBounds___redArg(v___x_1936_);
if (v_isShared_1933_ == 0)
{
lean_ctor_set(v___x_1932_, 0, v___x_1938_);
v___x_1940_ = v___x_1932_;
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
else
{
lean_object* v___x_1942_; lean_object* v___x_1944_; 
v___x_1942_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1936_, v_occurs_1934_, v_x_1916_);
lean_dec_ref(v_occurs_1934_);
if (v_isShared_1933_ == 0)
{
lean_ctor_set(v___x_1932_, 0, v___x_1942_);
v___x_1944_ = v___x_1932_;
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
else
{
lean_object* v_a_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1954_; 
v_a_1947_ = lean_ctor_get(v___x_1929_, 0);
v_isSharedCheck_1954_ = !lean_is_exclusive(v___x_1929_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1949_ = v___x_1929_;
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_a_1947_);
lean_dec(v___x_1929_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v___x_1952_; 
if (v_isShared_1950_ == 0)
{
v___x_1952_ = v___x_1949_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v_a_1947_);
v___x_1952_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
return v___x_1952_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOccursOf___boxed(lean_object* v_x_1955_, lean_object* v_a_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_){
_start:
{
lean_object* v_res_1968_; 
v_res_1968_ = l_Lean_Meta_Grind_Arith_Linear_getOccursOf(v_x_1955_, v_a_1956_, v_a_1957_, v_a_1958_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_, v_a_1965_, v_a_1966_);
lean_dec(v_a_1966_);
lean_dec_ref(v_a_1965_);
lean_dec(v_a_1964_);
lean_dec_ref(v_a_1963_);
lean_dec(v_a_1962_);
lean_dec_ref(v_a_1961_);
lean_dec(v_a_1960_);
lean_dec_ref(v_a_1959_);
lean_dec(v_a_1958_);
lean_dec(v_a_1957_);
lean_dec(v_a_1956_);
lean_dec(v_x_1955_);
return v_res_1968_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg(lean_object* v_k_1969_, lean_object* v_t_1970_){
_start:
{
if (lean_obj_tag(v_t_1970_) == 0)
{
lean_object* v_k_1971_; lean_object* v_l_1972_; lean_object* v_r_1973_; uint8_t v___x_1974_; 
v_k_1971_ = lean_ctor_get(v_t_1970_, 1);
v_l_1972_ = lean_ctor_get(v_t_1970_, 3);
v_r_1973_ = lean_ctor_get(v_t_1970_, 4);
v___x_1974_ = lean_nat_dec_lt(v_k_1969_, v_k_1971_);
if (v___x_1974_ == 0)
{
uint8_t v___x_1975_; 
v___x_1975_ = lean_nat_dec_eq(v_k_1969_, v_k_1971_);
if (v___x_1975_ == 0)
{
v_t_1970_ = v_r_1973_;
goto _start;
}
else
{
return v___x_1975_;
}
}
else
{
v_t_1970_ = v_l_1972_;
goto _start;
}
}
else
{
uint8_t v___x_1978_; 
v___x_1978_ = 0;
return v___x_1978_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg___boxed(lean_object* v_k_1979_, lean_object* v_t_1980_){
_start:
{
uint8_t v_res_1981_; lean_object* v_r_1982_; 
v_res_1981_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg(v_k_1979_, v_t_1980_);
lean_dec(v_t_1980_);
lean_dec(v_k_1979_);
v_r_1982_ = lean_box(v_res_1981_);
return v_r_1982_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1___redArg(lean_object* v_k_1983_, lean_object* v_v_1984_, lean_object* v_t_1985_){
_start:
{
if (lean_obj_tag(v_t_1985_) == 0)
{
lean_object* v_size_1986_; lean_object* v_k_1987_; lean_object* v_v_1988_; lean_object* v_l_1989_; lean_object* v_r_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_2271_; 
v_size_1986_ = lean_ctor_get(v_t_1985_, 0);
v_k_1987_ = lean_ctor_get(v_t_1985_, 1);
v_v_1988_ = lean_ctor_get(v_t_1985_, 2);
v_l_1989_ = lean_ctor_get(v_t_1985_, 3);
v_r_1990_ = lean_ctor_get(v_t_1985_, 4);
v_isSharedCheck_2271_ = !lean_is_exclusive(v_t_1985_);
if (v_isSharedCheck_2271_ == 0)
{
v___x_1992_ = v_t_1985_;
v_isShared_1993_ = v_isSharedCheck_2271_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_r_1990_);
lean_inc(v_l_1989_);
lean_inc(v_v_1988_);
lean_inc(v_k_1987_);
lean_inc(v_size_1986_);
lean_dec(v_t_1985_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_2271_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
uint8_t v___x_1994_; 
v___x_1994_ = lean_nat_dec_lt(v_k_1983_, v_k_1987_);
if (v___x_1994_ == 0)
{
uint8_t v___x_1995_; 
v___x_1995_ = lean_nat_dec_eq(v_k_1983_, v_k_1987_);
if (v___x_1995_ == 0)
{
lean_object* v_impl_1996_; lean_object* v___x_1997_; 
lean_dec(v_size_1986_);
v_impl_1996_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1___redArg(v_k_1983_, v_v_1984_, v_r_1990_);
v___x_1997_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1989_) == 0)
{
lean_object* v_size_1998_; lean_object* v_size_1999_; lean_object* v_k_2000_; lean_object* v_v_2001_; lean_object* v_l_2002_; lean_object* v_r_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; uint8_t v___x_2006_; 
v_size_1998_ = lean_ctor_get(v_l_1989_, 0);
v_size_1999_ = lean_ctor_get(v_impl_1996_, 0);
lean_inc(v_size_1999_);
v_k_2000_ = lean_ctor_get(v_impl_1996_, 1);
lean_inc(v_k_2000_);
v_v_2001_ = lean_ctor_get(v_impl_1996_, 2);
lean_inc(v_v_2001_);
v_l_2002_ = lean_ctor_get(v_impl_1996_, 3);
lean_inc(v_l_2002_);
v_r_2003_ = lean_ctor_get(v_impl_1996_, 4);
lean_inc(v_r_2003_);
v___x_2004_ = lean_unsigned_to_nat(3u);
v___x_2005_ = lean_nat_mul(v___x_2004_, v_size_1998_);
v___x_2006_ = lean_nat_dec_lt(v___x_2005_, v_size_1999_);
lean_dec(v___x_2005_);
if (v___x_2006_ == 0)
{
lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2010_; 
lean_dec(v_r_2003_);
lean_dec(v_l_2002_);
lean_dec(v_v_2001_);
lean_dec(v_k_2000_);
v___x_2007_ = lean_nat_add(v___x_1997_, v_size_1998_);
v___x_2008_ = lean_nat_add(v___x_2007_, v_size_1999_);
lean_dec(v_size_1999_);
lean_dec(v___x_2007_);
if (v_isShared_1993_ == 0)
{
lean_ctor_set(v___x_1992_, 4, v_impl_1996_);
lean_ctor_set(v___x_1992_, 0, v___x_2008_);
v___x_2010_ = v___x_1992_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v___x_2008_);
lean_ctor_set(v_reuseFailAlloc_2011_, 1, v_k_1987_);
lean_ctor_set(v_reuseFailAlloc_2011_, 2, v_v_1988_);
lean_ctor_set(v_reuseFailAlloc_2011_, 3, v_l_1989_);
lean_ctor_set(v_reuseFailAlloc_2011_, 4, v_impl_1996_);
v___x_2010_ = v_reuseFailAlloc_2011_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
return v___x_2010_;
}
}
else
{
lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2075_; 
v_isSharedCheck_2075_ = !lean_is_exclusive(v_impl_1996_);
if (v_isSharedCheck_2075_ == 0)
{
lean_object* v_unused_2076_; lean_object* v_unused_2077_; lean_object* v_unused_2078_; lean_object* v_unused_2079_; lean_object* v_unused_2080_; 
v_unused_2076_ = lean_ctor_get(v_impl_1996_, 4);
lean_dec(v_unused_2076_);
v_unused_2077_ = lean_ctor_get(v_impl_1996_, 3);
lean_dec(v_unused_2077_);
v_unused_2078_ = lean_ctor_get(v_impl_1996_, 2);
lean_dec(v_unused_2078_);
v_unused_2079_ = lean_ctor_get(v_impl_1996_, 1);
lean_dec(v_unused_2079_);
v_unused_2080_ = lean_ctor_get(v_impl_1996_, 0);
lean_dec(v_unused_2080_);
v___x_2013_ = v_impl_1996_;
v_isShared_2014_ = v_isSharedCheck_2075_;
goto v_resetjp_2012_;
}
else
{
lean_dec(v_impl_1996_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2075_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v_size_2015_; lean_object* v_k_2016_; lean_object* v_v_2017_; lean_object* v_l_2018_; lean_object* v_r_2019_; lean_object* v_size_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; uint8_t v___x_2023_; 
v_size_2015_ = lean_ctor_get(v_l_2002_, 0);
v_k_2016_ = lean_ctor_get(v_l_2002_, 1);
v_v_2017_ = lean_ctor_get(v_l_2002_, 2);
v_l_2018_ = lean_ctor_get(v_l_2002_, 3);
v_r_2019_ = lean_ctor_get(v_l_2002_, 4);
v_size_2020_ = lean_ctor_get(v_r_2003_, 0);
v___x_2021_ = lean_unsigned_to_nat(2u);
v___x_2022_ = lean_nat_mul(v___x_2021_, v_size_2020_);
v___x_2023_ = lean_nat_dec_lt(v_size_2015_, v___x_2022_);
lean_dec(v___x_2022_);
if (v___x_2023_ == 0)
{
lean_object* v___x_2025_; uint8_t v_isShared_2026_; uint8_t v_isSharedCheck_2051_; 
lean_inc(v_r_2019_);
lean_inc(v_l_2018_);
lean_inc(v_v_2017_);
lean_inc(v_k_2016_);
v_isSharedCheck_2051_ = !lean_is_exclusive(v_l_2002_);
if (v_isSharedCheck_2051_ == 0)
{
lean_object* v_unused_2052_; lean_object* v_unused_2053_; lean_object* v_unused_2054_; lean_object* v_unused_2055_; lean_object* v_unused_2056_; 
v_unused_2052_ = lean_ctor_get(v_l_2002_, 4);
lean_dec(v_unused_2052_);
v_unused_2053_ = lean_ctor_get(v_l_2002_, 3);
lean_dec(v_unused_2053_);
v_unused_2054_ = lean_ctor_get(v_l_2002_, 2);
lean_dec(v_unused_2054_);
v_unused_2055_ = lean_ctor_get(v_l_2002_, 1);
lean_dec(v_unused_2055_);
v_unused_2056_ = lean_ctor_get(v_l_2002_, 0);
lean_dec(v_unused_2056_);
v___x_2025_ = v_l_2002_;
v_isShared_2026_ = v_isSharedCheck_2051_;
goto v_resetjp_2024_;
}
else
{
lean_dec(v_l_2002_);
v___x_2025_ = lean_box(0);
v_isShared_2026_ = v_isSharedCheck_2051_;
goto v_resetjp_2024_;
}
v_resetjp_2024_:
{
lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___y_2030_; lean_object* v___y_2031_; lean_object* v___y_2032_; lean_object* v___y_2041_; 
v___x_2027_ = lean_nat_add(v___x_1997_, v_size_1998_);
v___x_2028_ = lean_nat_add(v___x_2027_, v_size_1999_);
lean_dec(v_size_1999_);
if (lean_obj_tag(v_l_2018_) == 0)
{
lean_object* v_size_2049_; 
v_size_2049_ = lean_ctor_get(v_l_2018_, 0);
lean_inc(v_size_2049_);
v___y_2041_ = v_size_2049_;
goto v___jp_2040_;
}
else
{
lean_object* v___x_2050_; 
v___x_2050_ = lean_unsigned_to_nat(0u);
v___y_2041_ = v___x_2050_;
goto v___jp_2040_;
}
v___jp_2029_:
{
lean_object* v___x_2033_; lean_object* v___x_2035_; 
v___x_2033_ = lean_nat_add(v___y_2030_, v___y_2032_);
lean_dec(v___y_2032_);
lean_dec(v___y_2030_);
if (v_isShared_2026_ == 0)
{
lean_ctor_set(v___x_2025_, 4, v_r_2003_);
lean_ctor_set(v___x_2025_, 3, v_r_2019_);
lean_ctor_set(v___x_2025_, 2, v_v_2001_);
lean_ctor_set(v___x_2025_, 1, v_k_2000_);
lean_ctor_set(v___x_2025_, 0, v___x_2033_);
v___x_2035_ = v___x_2025_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v___x_2033_);
lean_ctor_set(v_reuseFailAlloc_2039_, 1, v_k_2000_);
lean_ctor_set(v_reuseFailAlloc_2039_, 2, v_v_2001_);
lean_ctor_set(v_reuseFailAlloc_2039_, 3, v_r_2019_);
lean_ctor_set(v_reuseFailAlloc_2039_, 4, v_r_2003_);
v___x_2035_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
lean_object* v___x_2037_; 
if (v_isShared_2014_ == 0)
{
lean_ctor_set(v___x_2013_, 4, v___x_2035_);
lean_ctor_set(v___x_2013_, 3, v___y_2031_);
lean_ctor_set(v___x_2013_, 2, v_v_2017_);
lean_ctor_set(v___x_2013_, 1, v_k_2016_);
lean_ctor_set(v___x_2013_, 0, v___x_2028_);
v___x_2037_ = v___x_2013_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v___x_2028_);
lean_ctor_set(v_reuseFailAlloc_2038_, 1, v_k_2016_);
lean_ctor_set(v_reuseFailAlloc_2038_, 2, v_v_2017_);
lean_ctor_set(v_reuseFailAlloc_2038_, 3, v___y_2031_);
lean_ctor_set(v_reuseFailAlloc_2038_, 4, v___x_2035_);
v___x_2037_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
return v___x_2037_;
}
}
}
v___jp_2040_:
{
lean_object* v___x_2042_; lean_object* v___x_2044_; 
v___x_2042_ = lean_nat_add(v___x_2027_, v___y_2041_);
lean_dec(v___y_2041_);
lean_dec(v___x_2027_);
if (v_isShared_1993_ == 0)
{
lean_ctor_set(v___x_1992_, 4, v_l_2018_);
lean_ctor_set(v___x_1992_, 0, v___x_2042_);
v___x_2044_ = v___x_1992_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v___x_2042_);
lean_ctor_set(v_reuseFailAlloc_2048_, 1, v_k_1987_);
lean_ctor_set(v_reuseFailAlloc_2048_, 2, v_v_1988_);
lean_ctor_set(v_reuseFailAlloc_2048_, 3, v_l_1989_);
lean_ctor_set(v_reuseFailAlloc_2048_, 4, v_l_2018_);
v___x_2044_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
lean_object* v___x_2045_; 
v___x_2045_ = lean_nat_add(v___x_1997_, v_size_2020_);
if (lean_obj_tag(v_r_2019_) == 0)
{
lean_object* v_size_2046_; 
v_size_2046_ = lean_ctor_get(v_r_2019_, 0);
lean_inc(v_size_2046_);
v___y_2030_ = v___x_2045_;
v___y_2031_ = v___x_2044_;
v___y_2032_ = v_size_2046_;
goto v___jp_2029_;
}
else
{
lean_object* v___x_2047_; 
v___x_2047_ = lean_unsigned_to_nat(0u);
v___y_2030_ = v___x_2045_;
v___y_2031_ = v___x_2044_;
v___y_2032_ = v___x_2047_;
goto v___jp_2029_;
}
}
}
}
}
else
{
lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2061_; 
lean_del_object(v___x_1992_);
v___x_2057_ = lean_nat_add(v___x_1997_, v_size_1998_);
v___x_2058_ = lean_nat_add(v___x_2057_, v_size_1999_);
lean_dec(v_size_1999_);
v___x_2059_ = lean_nat_add(v___x_2057_, v_size_2015_);
lean_dec(v___x_2057_);
lean_inc_ref(v_l_1989_);
if (v_isShared_2014_ == 0)
{
lean_ctor_set(v___x_2013_, 4, v_l_2002_);
lean_ctor_set(v___x_2013_, 3, v_l_1989_);
lean_ctor_set(v___x_2013_, 2, v_v_1988_);
lean_ctor_set(v___x_2013_, 1, v_k_1987_);
lean_ctor_set(v___x_2013_, 0, v___x_2059_);
v___x_2061_ = v___x_2013_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v___x_2059_);
lean_ctor_set(v_reuseFailAlloc_2074_, 1, v_k_1987_);
lean_ctor_set(v_reuseFailAlloc_2074_, 2, v_v_1988_);
lean_ctor_set(v_reuseFailAlloc_2074_, 3, v_l_1989_);
lean_ctor_set(v_reuseFailAlloc_2074_, 4, v_l_2002_);
v___x_2061_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2068_; 
v_isSharedCheck_2068_ = !lean_is_exclusive(v_l_1989_);
if (v_isSharedCheck_2068_ == 0)
{
lean_object* v_unused_2069_; lean_object* v_unused_2070_; lean_object* v_unused_2071_; lean_object* v_unused_2072_; lean_object* v_unused_2073_; 
v_unused_2069_ = lean_ctor_get(v_l_1989_, 4);
lean_dec(v_unused_2069_);
v_unused_2070_ = lean_ctor_get(v_l_1989_, 3);
lean_dec(v_unused_2070_);
v_unused_2071_ = lean_ctor_get(v_l_1989_, 2);
lean_dec(v_unused_2071_);
v_unused_2072_ = lean_ctor_get(v_l_1989_, 1);
lean_dec(v_unused_2072_);
v_unused_2073_ = lean_ctor_get(v_l_1989_, 0);
lean_dec(v_unused_2073_);
v___x_2063_ = v_l_1989_;
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
else
{
lean_dec(v_l_1989_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v___x_2066_; 
if (v_isShared_2064_ == 0)
{
lean_ctor_set(v___x_2063_, 4, v_r_2003_);
lean_ctor_set(v___x_2063_, 3, v___x_2061_);
lean_ctor_set(v___x_2063_, 2, v_v_2001_);
lean_ctor_set(v___x_2063_, 1, v_k_2000_);
lean_ctor_set(v___x_2063_, 0, v___x_2058_);
v___x_2066_ = v___x_2063_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v___x_2058_);
lean_ctor_set(v_reuseFailAlloc_2067_, 1, v_k_2000_);
lean_ctor_set(v_reuseFailAlloc_2067_, 2, v_v_2001_);
lean_ctor_set(v_reuseFailAlloc_2067_, 3, v___x_2061_);
lean_ctor_set(v_reuseFailAlloc_2067_, 4, v_r_2003_);
v___x_2066_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
return v___x_2066_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2081_; 
v_l_2081_ = lean_ctor_get(v_impl_1996_, 3);
lean_inc(v_l_2081_);
if (lean_obj_tag(v_l_2081_) == 0)
{
lean_object* v_r_2082_; lean_object* v_k_2083_; lean_object* v_v_2084_; lean_object* v___x_2086_; uint8_t v_isShared_2087_; uint8_t v_isSharedCheck_2107_; 
v_r_2082_ = lean_ctor_get(v_impl_1996_, 4);
v_k_2083_ = lean_ctor_get(v_impl_1996_, 1);
v_v_2084_ = lean_ctor_get(v_impl_1996_, 2);
v_isSharedCheck_2107_ = !lean_is_exclusive(v_impl_1996_);
if (v_isSharedCheck_2107_ == 0)
{
lean_object* v_unused_2108_; lean_object* v_unused_2109_; 
v_unused_2108_ = lean_ctor_get(v_impl_1996_, 3);
lean_dec(v_unused_2108_);
v_unused_2109_ = lean_ctor_get(v_impl_1996_, 0);
lean_dec(v_unused_2109_);
v___x_2086_ = v_impl_1996_;
v_isShared_2087_ = v_isSharedCheck_2107_;
goto v_resetjp_2085_;
}
else
{
lean_inc(v_r_2082_);
lean_inc(v_v_2084_);
lean_inc(v_k_2083_);
lean_dec(v_impl_1996_);
v___x_2086_ = lean_box(0);
v_isShared_2087_ = v_isSharedCheck_2107_;
goto v_resetjp_2085_;
}
v_resetjp_2085_:
{
lean_object* v_k_2088_; lean_object* v_v_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2103_; 
v_k_2088_ = lean_ctor_get(v_l_2081_, 1);
v_v_2089_ = lean_ctor_get(v_l_2081_, 2);
v_isSharedCheck_2103_ = !lean_is_exclusive(v_l_2081_);
if (v_isSharedCheck_2103_ == 0)
{
lean_object* v_unused_2104_; lean_object* v_unused_2105_; lean_object* v_unused_2106_; 
v_unused_2104_ = lean_ctor_get(v_l_2081_, 4);
lean_dec(v_unused_2104_);
v_unused_2105_ = lean_ctor_get(v_l_2081_, 3);
lean_dec(v_unused_2105_);
v_unused_2106_ = lean_ctor_get(v_l_2081_, 0);
lean_dec(v_unused_2106_);
v___x_2091_ = v_l_2081_;
v_isShared_2092_ = v_isSharedCheck_2103_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_v_2089_);
lean_inc(v_k_2088_);
lean_dec(v_l_2081_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2103_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v___x_2093_; lean_object* v___x_2095_; 
v___x_2093_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2082_, 2);
if (v_isShared_2092_ == 0)
{
lean_ctor_set(v___x_2091_, 4, v_r_2082_);
lean_ctor_set(v___x_2091_, 3, v_r_2082_);
lean_ctor_set(v___x_2091_, 2, v_v_1988_);
lean_ctor_set(v___x_2091_, 1, v_k_1987_);
lean_ctor_set(v___x_2091_, 0, v___x_1997_);
v___x_2095_ = v___x_2091_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v___x_1997_);
lean_ctor_set(v_reuseFailAlloc_2102_, 1, v_k_1987_);
lean_ctor_set(v_reuseFailAlloc_2102_, 2, v_v_1988_);
lean_ctor_set(v_reuseFailAlloc_2102_, 3, v_r_2082_);
lean_ctor_set(v_reuseFailAlloc_2102_, 4, v_r_2082_);
v___x_2095_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
lean_object* v___x_2097_; 
lean_inc(v_r_2082_);
if (v_isShared_2087_ == 0)
{
lean_ctor_set(v___x_2086_, 3, v_r_2082_);
lean_ctor_set(v___x_2086_, 0, v___x_1997_);
v___x_2097_ = v___x_2086_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v___x_1997_);
lean_ctor_set(v_reuseFailAlloc_2101_, 1, v_k_2083_);
lean_ctor_set(v_reuseFailAlloc_2101_, 2, v_v_2084_);
lean_ctor_set(v_reuseFailAlloc_2101_, 3, v_r_2082_);
lean_ctor_set(v_reuseFailAlloc_2101_, 4, v_r_2082_);
v___x_2097_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
lean_object* v___x_2099_; 
if (v_isShared_1993_ == 0)
{
lean_ctor_set(v___x_1992_, 4, v___x_2097_);
lean_ctor_set(v___x_1992_, 3, v___x_2095_);
lean_ctor_set(v___x_1992_, 2, v_v_2089_);
lean_ctor_set(v___x_1992_, 1, v_k_2088_);
lean_ctor_set(v___x_1992_, 0, v___x_2093_);
v___x_2099_ = v___x_1992_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v___x_2093_);
lean_ctor_set(v_reuseFailAlloc_2100_, 1, v_k_2088_);
lean_ctor_set(v_reuseFailAlloc_2100_, 2, v_v_2089_);
lean_ctor_set(v_reuseFailAlloc_2100_, 3, v___x_2095_);
lean_ctor_set(v_reuseFailAlloc_2100_, 4, v___x_2097_);
v___x_2099_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
return v___x_2099_;
}
}
}
}
}
}
else
{
lean_object* v_r_2110_; 
v_r_2110_ = lean_ctor_get(v_impl_1996_, 4);
lean_inc(v_r_2110_);
if (lean_obj_tag(v_r_2110_) == 0)
{
lean_object* v_k_2111_; lean_object* v_v_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2123_; 
v_k_2111_ = lean_ctor_get(v_impl_1996_, 1);
v_v_2112_ = lean_ctor_get(v_impl_1996_, 2);
v_isSharedCheck_2123_ = !lean_is_exclusive(v_impl_1996_);
if (v_isSharedCheck_2123_ == 0)
{
lean_object* v_unused_2124_; lean_object* v_unused_2125_; lean_object* v_unused_2126_; 
v_unused_2124_ = lean_ctor_get(v_impl_1996_, 4);
lean_dec(v_unused_2124_);
v_unused_2125_ = lean_ctor_get(v_impl_1996_, 3);
lean_dec(v_unused_2125_);
v_unused_2126_ = lean_ctor_get(v_impl_1996_, 0);
lean_dec(v_unused_2126_);
v___x_2114_ = v_impl_1996_;
v_isShared_2115_ = v_isSharedCheck_2123_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_v_2112_);
lean_inc(v_k_2111_);
lean_dec(v_impl_1996_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2123_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v___x_2116_; lean_object* v___x_2118_; 
v___x_2116_ = lean_unsigned_to_nat(3u);
if (v_isShared_2115_ == 0)
{
lean_ctor_set(v___x_2114_, 4, v_l_2081_);
lean_ctor_set(v___x_2114_, 2, v_v_1988_);
lean_ctor_set(v___x_2114_, 1, v_k_1987_);
lean_ctor_set(v___x_2114_, 0, v___x_1997_);
v___x_2118_ = v___x_2114_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v___x_1997_);
lean_ctor_set(v_reuseFailAlloc_2122_, 1, v_k_1987_);
lean_ctor_set(v_reuseFailAlloc_2122_, 2, v_v_1988_);
lean_ctor_set(v_reuseFailAlloc_2122_, 3, v_l_2081_);
lean_ctor_set(v_reuseFailAlloc_2122_, 4, v_l_2081_);
v___x_2118_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
lean_object* v___x_2120_; 
if (v_isShared_1993_ == 0)
{
lean_ctor_set(v___x_1992_, 4, v_r_2110_);
lean_ctor_set(v___x_1992_, 3, v___x_2118_);
lean_ctor_set(v___x_1992_, 2, v_v_2112_);
lean_ctor_set(v___x_1992_, 1, v_k_2111_);
lean_ctor_set(v___x_1992_, 0, v___x_2116_);
v___x_2120_ = v___x_1992_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v___x_2116_);
lean_ctor_set(v_reuseFailAlloc_2121_, 1, v_k_2111_);
lean_ctor_set(v_reuseFailAlloc_2121_, 2, v_v_2112_);
lean_ctor_set(v_reuseFailAlloc_2121_, 3, v___x_2118_);
lean_ctor_set(v_reuseFailAlloc_2121_, 4, v_r_2110_);
v___x_2120_ = v_reuseFailAlloc_2121_;
goto v_reusejp_2119_;
}
v_reusejp_2119_:
{
return v___x_2120_;
}
}
}
}
else
{
lean_object* v___x_2127_; lean_object* v___x_2129_; 
v___x_2127_ = lean_unsigned_to_nat(2u);
if (v_isShared_1993_ == 0)
{
lean_ctor_set(v___x_1992_, 4, v_impl_1996_);
lean_ctor_set(v___x_1992_, 3, v_r_2110_);
lean_ctor_set(v___x_1992_, 0, v___x_2127_);
v___x_2129_ = v___x_1992_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v___x_2127_);
lean_ctor_set(v_reuseFailAlloc_2130_, 1, v_k_1987_);
lean_ctor_set(v_reuseFailAlloc_2130_, 2, v_v_1988_);
lean_ctor_set(v_reuseFailAlloc_2130_, 3, v_r_2110_);
lean_ctor_set(v_reuseFailAlloc_2130_, 4, v_impl_1996_);
v___x_2129_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
return v___x_2129_;
}
}
}
}
}
else
{
lean_object* v___x_2132_; 
lean_dec(v_v_1988_);
lean_dec(v_k_1987_);
if (v_isShared_1993_ == 0)
{
lean_ctor_set(v___x_1992_, 2, v_v_1984_);
lean_ctor_set(v___x_1992_, 1, v_k_1983_);
v___x_2132_ = v___x_1992_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v_size_1986_);
lean_ctor_set(v_reuseFailAlloc_2133_, 1, v_k_1983_);
lean_ctor_set(v_reuseFailAlloc_2133_, 2, v_v_1984_);
lean_ctor_set(v_reuseFailAlloc_2133_, 3, v_l_1989_);
lean_ctor_set(v_reuseFailAlloc_2133_, 4, v_r_1990_);
v___x_2132_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
return v___x_2132_;
}
}
}
else
{
lean_object* v_impl_2134_; lean_object* v___x_2135_; 
lean_dec(v_size_1986_);
v_impl_2134_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1___redArg(v_k_1983_, v_v_1984_, v_l_1989_);
v___x_2135_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1990_) == 0)
{
lean_object* v_size_2136_; lean_object* v_size_2137_; lean_object* v_k_2138_; lean_object* v_v_2139_; lean_object* v_l_2140_; lean_object* v_r_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; uint8_t v___x_2144_; 
v_size_2136_ = lean_ctor_get(v_r_1990_, 0);
v_size_2137_ = lean_ctor_get(v_impl_2134_, 0);
lean_inc(v_size_2137_);
v_k_2138_ = lean_ctor_get(v_impl_2134_, 1);
lean_inc(v_k_2138_);
v_v_2139_ = lean_ctor_get(v_impl_2134_, 2);
lean_inc(v_v_2139_);
v_l_2140_ = lean_ctor_get(v_impl_2134_, 3);
lean_inc(v_l_2140_);
v_r_2141_ = lean_ctor_get(v_impl_2134_, 4);
lean_inc(v_r_2141_);
v___x_2142_ = lean_unsigned_to_nat(3u);
v___x_2143_ = lean_nat_mul(v___x_2142_, v_size_2136_);
v___x_2144_ = lean_nat_dec_lt(v___x_2143_, v_size_2137_);
lean_dec(v___x_2143_);
if (v___x_2144_ == 0)
{
lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2148_; 
lean_dec(v_r_2141_);
lean_dec(v_l_2140_);
lean_dec(v_v_2139_);
lean_dec(v_k_2138_);
v___x_2145_ = lean_nat_add(v___x_2135_, v_size_2137_);
lean_dec(v_size_2137_);
v___x_2146_ = lean_nat_add(v___x_2145_, v_size_2136_);
lean_dec(v___x_2145_);
if (v_isShared_1993_ == 0)
{
lean_ctor_set(v___x_1992_, 3, v_impl_2134_);
lean_ctor_set(v___x_1992_, 0, v___x_2146_);
v___x_2148_ = v___x_1992_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v___x_2146_);
lean_ctor_set(v_reuseFailAlloc_2149_, 1, v_k_1987_);
lean_ctor_set(v_reuseFailAlloc_2149_, 2, v_v_1988_);
lean_ctor_set(v_reuseFailAlloc_2149_, 3, v_impl_2134_);
lean_ctor_set(v_reuseFailAlloc_2149_, 4, v_r_1990_);
v___x_2148_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
return v___x_2148_;
}
}
else
{
lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2215_; 
v_isSharedCheck_2215_ = !lean_is_exclusive(v_impl_2134_);
if (v_isSharedCheck_2215_ == 0)
{
lean_object* v_unused_2216_; lean_object* v_unused_2217_; lean_object* v_unused_2218_; lean_object* v_unused_2219_; lean_object* v_unused_2220_; 
v_unused_2216_ = lean_ctor_get(v_impl_2134_, 4);
lean_dec(v_unused_2216_);
v_unused_2217_ = lean_ctor_get(v_impl_2134_, 3);
lean_dec(v_unused_2217_);
v_unused_2218_ = lean_ctor_get(v_impl_2134_, 2);
lean_dec(v_unused_2218_);
v_unused_2219_ = lean_ctor_get(v_impl_2134_, 1);
lean_dec(v_unused_2219_);
v_unused_2220_ = lean_ctor_get(v_impl_2134_, 0);
lean_dec(v_unused_2220_);
v___x_2151_ = v_impl_2134_;
v_isShared_2152_ = v_isSharedCheck_2215_;
goto v_resetjp_2150_;
}
else
{
lean_dec(v_impl_2134_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2215_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
lean_object* v_size_2153_; lean_object* v_size_2154_; lean_object* v_k_2155_; lean_object* v_v_2156_; lean_object* v_l_2157_; lean_object* v_r_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; uint8_t v___x_2161_; 
v_size_2153_ = lean_ctor_get(v_l_2140_, 0);
v_size_2154_ = lean_ctor_get(v_r_2141_, 0);
v_k_2155_ = lean_ctor_get(v_r_2141_, 1);
v_v_2156_ = lean_ctor_get(v_r_2141_, 2);
v_l_2157_ = lean_ctor_get(v_r_2141_, 3);
v_r_2158_ = lean_ctor_get(v_r_2141_, 4);
v___x_2159_ = lean_unsigned_to_nat(2u);
v___x_2160_ = lean_nat_mul(v___x_2159_, v_size_2153_);
v___x_2161_ = lean_nat_dec_lt(v_size_2154_, v___x_2160_);
lean_dec(v___x_2160_);
if (v___x_2161_ == 0)
{
lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2190_; 
lean_inc(v_r_2158_);
lean_inc(v_l_2157_);
lean_inc(v_v_2156_);
lean_inc(v_k_2155_);
v_isSharedCheck_2190_ = !lean_is_exclusive(v_r_2141_);
if (v_isSharedCheck_2190_ == 0)
{
lean_object* v_unused_2191_; lean_object* v_unused_2192_; lean_object* v_unused_2193_; lean_object* v_unused_2194_; lean_object* v_unused_2195_; 
v_unused_2191_ = lean_ctor_get(v_r_2141_, 4);
lean_dec(v_unused_2191_);
v_unused_2192_ = lean_ctor_get(v_r_2141_, 3);
lean_dec(v_unused_2192_);
v_unused_2193_ = lean_ctor_get(v_r_2141_, 2);
lean_dec(v_unused_2193_);
v_unused_2194_ = lean_ctor_get(v_r_2141_, 1);
lean_dec(v_unused_2194_);
v_unused_2195_ = lean_ctor_get(v_r_2141_, 0);
lean_dec(v_unused_2195_);
v___x_2163_ = v_r_2141_;
v_isShared_2164_ = v_isSharedCheck_2190_;
goto v_resetjp_2162_;
}
else
{
lean_dec(v_r_2141_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2190_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___y_2168_; lean_object* v___y_2169_; lean_object* v___y_2170_; lean_object* v___x_2178_; lean_object* v___y_2180_; 
v___x_2165_ = lean_nat_add(v___x_2135_, v_size_2137_);
lean_dec(v_size_2137_);
v___x_2166_ = lean_nat_add(v___x_2165_, v_size_2136_);
lean_dec(v___x_2165_);
v___x_2178_ = lean_nat_add(v___x_2135_, v_size_2153_);
if (lean_obj_tag(v_l_2157_) == 0)
{
lean_object* v_size_2188_; 
v_size_2188_ = lean_ctor_get(v_l_2157_, 0);
lean_inc(v_size_2188_);
v___y_2180_ = v_size_2188_;
goto v___jp_2179_;
}
else
{
lean_object* v___x_2189_; 
v___x_2189_ = lean_unsigned_to_nat(0u);
v___y_2180_ = v___x_2189_;
goto v___jp_2179_;
}
v___jp_2167_:
{
lean_object* v___x_2171_; lean_object* v___x_2173_; 
v___x_2171_ = lean_nat_add(v___y_2169_, v___y_2170_);
lean_dec(v___y_2170_);
lean_dec(v___y_2169_);
if (v_isShared_2164_ == 0)
{
lean_ctor_set(v___x_2163_, 4, v_r_1990_);
lean_ctor_set(v___x_2163_, 3, v_r_2158_);
lean_ctor_set(v___x_2163_, 2, v_v_1988_);
lean_ctor_set(v___x_2163_, 1, v_k_1987_);
lean_ctor_set(v___x_2163_, 0, v___x_2171_);
v___x_2173_ = v___x_2163_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v___x_2171_);
lean_ctor_set(v_reuseFailAlloc_2177_, 1, v_k_1987_);
lean_ctor_set(v_reuseFailAlloc_2177_, 2, v_v_1988_);
lean_ctor_set(v_reuseFailAlloc_2177_, 3, v_r_2158_);
lean_ctor_set(v_reuseFailAlloc_2177_, 4, v_r_1990_);
v___x_2173_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
lean_object* v___x_2175_; 
if (v_isShared_2152_ == 0)
{
lean_ctor_set(v___x_2151_, 4, v___x_2173_);
lean_ctor_set(v___x_2151_, 3, v___y_2168_);
lean_ctor_set(v___x_2151_, 2, v_v_2156_);
lean_ctor_set(v___x_2151_, 1, v_k_2155_);
lean_ctor_set(v___x_2151_, 0, v___x_2166_);
v___x_2175_ = v___x_2151_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v___x_2166_);
lean_ctor_set(v_reuseFailAlloc_2176_, 1, v_k_2155_);
lean_ctor_set(v_reuseFailAlloc_2176_, 2, v_v_2156_);
lean_ctor_set(v_reuseFailAlloc_2176_, 3, v___y_2168_);
lean_ctor_set(v_reuseFailAlloc_2176_, 4, v___x_2173_);
v___x_2175_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
return v___x_2175_;
}
}
}
v___jp_2179_:
{
lean_object* v___x_2181_; lean_object* v___x_2183_; 
v___x_2181_ = lean_nat_add(v___x_2178_, v___y_2180_);
lean_dec(v___y_2180_);
lean_dec(v___x_2178_);
if (v_isShared_1993_ == 0)
{
lean_ctor_set(v___x_1992_, 4, v_l_2157_);
lean_ctor_set(v___x_1992_, 3, v_l_2140_);
lean_ctor_set(v___x_1992_, 2, v_v_2139_);
lean_ctor_set(v___x_1992_, 1, v_k_2138_);
lean_ctor_set(v___x_1992_, 0, v___x_2181_);
v___x_2183_ = v___x_1992_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v___x_2181_);
lean_ctor_set(v_reuseFailAlloc_2187_, 1, v_k_2138_);
lean_ctor_set(v_reuseFailAlloc_2187_, 2, v_v_2139_);
lean_ctor_set(v_reuseFailAlloc_2187_, 3, v_l_2140_);
lean_ctor_set(v_reuseFailAlloc_2187_, 4, v_l_2157_);
v___x_2183_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
lean_object* v___x_2184_; 
v___x_2184_ = lean_nat_add(v___x_2135_, v_size_2136_);
if (lean_obj_tag(v_r_2158_) == 0)
{
lean_object* v_size_2185_; 
v_size_2185_ = lean_ctor_get(v_r_2158_, 0);
lean_inc(v_size_2185_);
v___y_2168_ = v___x_2183_;
v___y_2169_ = v___x_2184_;
v___y_2170_ = v_size_2185_;
goto v___jp_2167_;
}
else
{
lean_object* v___x_2186_; 
v___x_2186_ = lean_unsigned_to_nat(0u);
v___y_2168_ = v___x_2183_;
v___y_2169_ = v___x_2184_;
v___y_2170_ = v___x_2186_;
goto v___jp_2167_;
}
}
}
}
}
else
{
lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2201_; 
lean_del_object(v___x_1992_);
v___x_2196_ = lean_nat_add(v___x_2135_, v_size_2137_);
lean_dec(v_size_2137_);
v___x_2197_ = lean_nat_add(v___x_2196_, v_size_2136_);
lean_dec(v___x_2196_);
v___x_2198_ = lean_nat_add(v___x_2135_, v_size_2136_);
v___x_2199_ = lean_nat_add(v___x_2198_, v_size_2154_);
lean_dec(v___x_2198_);
lean_inc_ref(v_r_1990_);
if (v_isShared_2152_ == 0)
{
lean_ctor_set(v___x_2151_, 4, v_r_1990_);
lean_ctor_set(v___x_2151_, 3, v_r_2141_);
lean_ctor_set(v___x_2151_, 2, v_v_1988_);
lean_ctor_set(v___x_2151_, 1, v_k_1987_);
lean_ctor_set(v___x_2151_, 0, v___x_2199_);
v___x_2201_ = v___x_2151_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v___x_2199_);
lean_ctor_set(v_reuseFailAlloc_2214_, 1, v_k_1987_);
lean_ctor_set(v_reuseFailAlloc_2214_, 2, v_v_1988_);
lean_ctor_set(v_reuseFailAlloc_2214_, 3, v_r_2141_);
lean_ctor_set(v_reuseFailAlloc_2214_, 4, v_r_1990_);
v___x_2201_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
lean_object* v___x_2203_; uint8_t v_isShared_2204_; uint8_t v_isSharedCheck_2208_; 
v_isSharedCheck_2208_ = !lean_is_exclusive(v_r_1990_);
if (v_isSharedCheck_2208_ == 0)
{
lean_object* v_unused_2209_; lean_object* v_unused_2210_; lean_object* v_unused_2211_; lean_object* v_unused_2212_; lean_object* v_unused_2213_; 
v_unused_2209_ = lean_ctor_get(v_r_1990_, 4);
lean_dec(v_unused_2209_);
v_unused_2210_ = lean_ctor_get(v_r_1990_, 3);
lean_dec(v_unused_2210_);
v_unused_2211_ = lean_ctor_get(v_r_1990_, 2);
lean_dec(v_unused_2211_);
v_unused_2212_ = lean_ctor_get(v_r_1990_, 1);
lean_dec(v_unused_2212_);
v_unused_2213_ = lean_ctor_get(v_r_1990_, 0);
lean_dec(v_unused_2213_);
v___x_2203_ = v_r_1990_;
v_isShared_2204_ = v_isSharedCheck_2208_;
goto v_resetjp_2202_;
}
else
{
lean_dec(v_r_1990_);
v___x_2203_ = lean_box(0);
v_isShared_2204_ = v_isSharedCheck_2208_;
goto v_resetjp_2202_;
}
v_resetjp_2202_:
{
lean_object* v___x_2206_; 
if (v_isShared_2204_ == 0)
{
lean_ctor_set(v___x_2203_, 4, v___x_2201_);
lean_ctor_set(v___x_2203_, 3, v_l_2140_);
lean_ctor_set(v___x_2203_, 2, v_v_2139_);
lean_ctor_set(v___x_2203_, 1, v_k_2138_);
lean_ctor_set(v___x_2203_, 0, v___x_2197_);
v___x_2206_ = v___x_2203_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v___x_2197_);
lean_ctor_set(v_reuseFailAlloc_2207_, 1, v_k_2138_);
lean_ctor_set(v_reuseFailAlloc_2207_, 2, v_v_2139_);
lean_ctor_set(v_reuseFailAlloc_2207_, 3, v_l_2140_);
lean_ctor_set(v_reuseFailAlloc_2207_, 4, v___x_2201_);
v___x_2206_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
return v___x_2206_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2221_; 
v_l_2221_ = lean_ctor_get(v_impl_2134_, 3);
lean_inc(v_l_2221_);
if (lean_obj_tag(v_l_2221_) == 0)
{
lean_object* v_r_2222_; lean_object* v_k_2223_; lean_object* v_v_2224_; lean_object* v___x_2226_; uint8_t v_isShared_2227_; uint8_t v_isSharedCheck_2235_; 
v_r_2222_ = lean_ctor_get(v_impl_2134_, 4);
v_k_2223_ = lean_ctor_get(v_impl_2134_, 1);
v_v_2224_ = lean_ctor_get(v_impl_2134_, 2);
v_isSharedCheck_2235_ = !lean_is_exclusive(v_impl_2134_);
if (v_isSharedCheck_2235_ == 0)
{
lean_object* v_unused_2236_; lean_object* v_unused_2237_; 
v_unused_2236_ = lean_ctor_get(v_impl_2134_, 3);
lean_dec(v_unused_2236_);
v_unused_2237_ = lean_ctor_get(v_impl_2134_, 0);
lean_dec(v_unused_2237_);
v___x_2226_ = v_impl_2134_;
v_isShared_2227_ = v_isSharedCheck_2235_;
goto v_resetjp_2225_;
}
else
{
lean_inc(v_r_2222_);
lean_inc(v_v_2224_);
lean_inc(v_k_2223_);
lean_dec(v_impl_2134_);
v___x_2226_ = lean_box(0);
v_isShared_2227_ = v_isSharedCheck_2235_;
goto v_resetjp_2225_;
}
v_resetjp_2225_:
{
lean_object* v___x_2228_; lean_object* v___x_2230_; 
v___x_2228_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2222_);
if (v_isShared_2227_ == 0)
{
lean_ctor_set(v___x_2226_, 3, v_r_2222_);
lean_ctor_set(v___x_2226_, 2, v_v_1988_);
lean_ctor_set(v___x_2226_, 1, v_k_1987_);
lean_ctor_set(v___x_2226_, 0, v___x_2135_);
v___x_2230_ = v___x_2226_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v___x_2135_);
lean_ctor_set(v_reuseFailAlloc_2234_, 1, v_k_1987_);
lean_ctor_set(v_reuseFailAlloc_2234_, 2, v_v_1988_);
lean_ctor_set(v_reuseFailAlloc_2234_, 3, v_r_2222_);
lean_ctor_set(v_reuseFailAlloc_2234_, 4, v_r_2222_);
v___x_2230_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
lean_object* v___x_2232_; 
if (v_isShared_1993_ == 0)
{
lean_ctor_set(v___x_1992_, 4, v___x_2230_);
lean_ctor_set(v___x_1992_, 3, v_l_2221_);
lean_ctor_set(v___x_1992_, 2, v_v_2224_);
lean_ctor_set(v___x_1992_, 1, v_k_2223_);
lean_ctor_set(v___x_1992_, 0, v___x_2228_);
v___x_2232_ = v___x_1992_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v___x_2228_);
lean_ctor_set(v_reuseFailAlloc_2233_, 1, v_k_2223_);
lean_ctor_set(v_reuseFailAlloc_2233_, 2, v_v_2224_);
lean_ctor_set(v_reuseFailAlloc_2233_, 3, v_l_2221_);
lean_ctor_set(v_reuseFailAlloc_2233_, 4, v___x_2230_);
v___x_2232_ = v_reuseFailAlloc_2233_;
goto v_reusejp_2231_;
}
v_reusejp_2231_:
{
return v___x_2232_;
}
}
}
}
else
{
lean_object* v_r_2238_; 
v_r_2238_ = lean_ctor_get(v_impl_2134_, 4);
lean_inc(v_r_2238_);
if (lean_obj_tag(v_r_2238_) == 0)
{
lean_object* v_k_2239_; lean_object* v_v_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2263_; 
v_k_2239_ = lean_ctor_get(v_impl_2134_, 1);
v_v_2240_ = lean_ctor_get(v_impl_2134_, 2);
v_isSharedCheck_2263_ = !lean_is_exclusive(v_impl_2134_);
if (v_isSharedCheck_2263_ == 0)
{
lean_object* v_unused_2264_; lean_object* v_unused_2265_; lean_object* v_unused_2266_; 
v_unused_2264_ = lean_ctor_get(v_impl_2134_, 4);
lean_dec(v_unused_2264_);
v_unused_2265_ = lean_ctor_get(v_impl_2134_, 3);
lean_dec(v_unused_2265_);
v_unused_2266_ = lean_ctor_get(v_impl_2134_, 0);
lean_dec(v_unused_2266_);
v___x_2242_ = v_impl_2134_;
v_isShared_2243_ = v_isSharedCheck_2263_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_v_2240_);
lean_inc(v_k_2239_);
lean_dec(v_impl_2134_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2263_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
lean_object* v_k_2244_; lean_object* v_v_2245_; lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2259_; 
v_k_2244_ = lean_ctor_get(v_r_2238_, 1);
v_v_2245_ = lean_ctor_get(v_r_2238_, 2);
v_isSharedCheck_2259_ = !lean_is_exclusive(v_r_2238_);
if (v_isSharedCheck_2259_ == 0)
{
lean_object* v_unused_2260_; lean_object* v_unused_2261_; lean_object* v_unused_2262_; 
v_unused_2260_ = lean_ctor_get(v_r_2238_, 4);
lean_dec(v_unused_2260_);
v_unused_2261_ = lean_ctor_get(v_r_2238_, 3);
lean_dec(v_unused_2261_);
v_unused_2262_ = lean_ctor_get(v_r_2238_, 0);
lean_dec(v_unused_2262_);
v___x_2247_ = v_r_2238_;
v_isShared_2248_ = v_isSharedCheck_2259_;
goto v_resetjp_2246_;
}
else
{
lean_inc(v_v_2245_);
lean_inc(v_k_2244_);
lean_dec(v_r_2238_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2259_;
goto v_resetjp_2246_;
}
v_resetjp_2246_:
{
lean_object* v___x_2249_; lean_object* v___x_2251_; 
v___x_2249_ = lean_unsigned_to_nat(3u);
if (v_isShared_2248_ == 0)
{
lean_ctor_set(v___x_2247_, 4, v_l_2221_);
lean_ctor_set(v___x_2247_, 3, v_l_2221_);
lean_ctor_set(v___x_2247_, 2, v_v_2240_);
lean_ctor_set(v___x_2247_, 1, v_k_2239_);
lean_ctor_set(v___x_2247_, 0, v___x_2135_);
v___x_2251_ = v___x_2247_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v___x_2135_);
lean_ctor_set(v_reuseFailAlloc_2258_, 1, v_k_2239_);
lean_ctor_set(v_reuseFailAlloc_2258_, 2, v_v_2240_);
lean_ctor_set(v_reuseFailAlloc_2258_, 3, v_l_2221_);
lean_ctor_set(v_reuseFailAlloc_2258_, 4, v_l_2221_);
v___x_2251_ = v_reuseFailAlloc_2258_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
lean_object* v___x_2253_; 
if (v_isShared_2243_ == 0)
{
lean_ctor_set(v___x_2242_, 4, v_l_2221_);
lean_ctor_set(v___x_2242_, 2, v_v_1988_);
lean_ctor_set(v___x_2242_, 1, v_k_1987_);
lean_ctor_set(v___x_2242_, 0, v___x_2135_);
v___x_2253_ = v___x_2242_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v___x_2135_);
lean_ctor_set(v_reuseFailAlloc_2257_, 1, v_k_1987_);
lean_ctor_set(v_reuseFailAlloc_2257_, 2, v_v_1988_);
lean_ctor_set(v_reuseFailAlloc_2257_, 3, v_l_2221_);
lean_ctor_set(v_reuseFailAlloc_2257_, 4, v_l_2221_);
v___x_2253_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
lean_object* v___x_2255_; 
if (v_isShared_1993_ == 0)
{
lean_ctor_set(v___x_1992_, 4, v___x_2253_);
lean_ctor_set(v___x_1992_, 3, v___x_2251_);
lean_ctor_set(v___x_1992_, 2, v_v_2245_);
lean_ctor_set(v___x_1992_, 1, v_k_2244_);
lean_ctor_set(v___x_1992_, 0, v___x_2249_);
v___x_2255_ = v___x_1992_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v___x_2249_);
lean_ctor_set(v_reuseFailAlloc_2256_, 1, v_k_2244_);
lean_ctor_set(v_reuseFailAlloc_2256_, 2, v_v_2245_);
lean_ctor_set(v_reuseFailAlloc_2256_, 3, v___x_2251_);
lean_ctor_set(v_reuseFailAlloc_2256_, 4, v___x_2253_);
v___x_2255_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
return v___x_2255_;
}
}
}
}
}
}
else
{
lean_object* v___x_2267_; lean_object* v___x_2269_; 
v___x_2267_ = lean_unsigned_to_nat(2u);
if (v_isShared_1993_ == 0)
{
lean_ctor_set(v___x_1992_, 4, v_r_2238_);
lean_ctor_set(v___x_1992_, 3, v_impl_2134_);
lean_ctor_set(v___x_1992_, 0, v___x_2267_);
v___x_2269_ = v___x_1992_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v___x_2267_);
lean_ctor_set(v_reuseFailAlloc_2270_, 1, v_k_1987_);
lean_ctor_set(v_reuseFailAlloc_2270_, 2, v_v_1988_);
lean_ctor_set(v_reuseFailAlloc_2270_, 3, v_impl_2134_);
lean_ctor_set(v_reuseFailAlloc_2270_, 4, v_r_2238_);
v___x_2269_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
return v___x_2269_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2272_; lean_object* v___x_2273_; 
v___x_2272_ = lean_unsigned_to_nat(1u);
v___x_2273_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2273_, 0, v___x_2272_);
lean_ctor_set(v___x_2273_, 1, v_k_1983_);
lean_ctor_set(v___x_2273_, 2, v_v_1984_);
lean_ctor_set(v___x_2273_, 3, v_t_1985_);
lean_ctor_set(v___x_2273_, 4, v_t_1985_);
return v___x_2273_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2(lean_object* v_y_2274_, lean_object* v_x_2275_, size_t v_x_2276_, size_t v_x_2277_){
_start:
{
if (lean_obj_tag(v_x_2275_) == 0)
{
lean_object* v_cs_2278_; size_t v_j_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; uint8_t v___x_2282_; 
v_cs_2278_ = lean_ctor_get(v_x_2275_, 0);
v_j_2279_ = lean_usize_shift_right(v_x_2276_, v_x_2277_);
v___x_2280_ = lean_usize_to_nat(v_j_2279_);
v___x_2281_ = lean_array_get_size(v_cs_2278_);
v___x_2282_ = lean_nat_dec_lt(v___x_2280_, v___x_2281_);
if (v___x_2282_ == 0)
{
lean_dec(v___x_2280_);
lean_dec(v_y_2274_);
return v_x_2275_;
}
else
{
lean_object* v___x_2284_; uint8_t v_isShared_2285_; uint8_t v_isSharedCheck_2300_; 
lean_inc_ref(v_cs_2278_);
v_isSharedCheck_2300_ = !lean_is_exclusive(v_x_2275_);
if (v_isSharedCheck_2300_ == 0)
{
lean_object* v_unused_2301_; 
v_unused_2301_ = lean_ctor_get(v_x_2275_, 0);
lean_dec(v_unused_2301_);
v___x_2284_ = v_x_2275_;
v_isShared_2285_ = v_isSharedCheck_2300_;
goto v_resetjp_2283_;
}
else
{
lean_dec(v_x_2275_);
v___x_2284_ = lean_box(0);
v_isShared_2285_ = v_isSharedCheck_2300_;
goto v_resetjp_2283_;
}
v_resetjp_2283_:
{
size_t v___x_2286_; size_t v___x_2287_; size_t v___x_2288_; size_t v_i_2289_; size_t v___x_2290_; size_t v_shift_2291_; lean_object* v_v_2292_; lean_object* v___x_2293_; lean_object* v_xs_x27_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2298_; 
v___x_2286_ = ((size_t)1ULL);
v___x_2287_ = lean_usize_shift_left(v___x_2286_, v_x_2277_);
v___x_2288_ = lean_usize_sub(v___x_2287_, v___x_2286_);
v_i_2289_ = lean_usize_land(v_x_2276_, v___x_2288_);
v___x_2290_ = ((size_t)5ULL);
v_shift_2291_ = lean_usize_sub(v_x_2277_, v___x_2290_);
v_v_2292_ = lean_array_fget(v_cs_2278_, v___x_2280_);
v___x_2293_ = lean_box(0);
v_xs_x27_2294_ = lean_array_fset(v_cs_2278_, v___x_2280_, v___x_2293_);
v___x_2295_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2(v_y_2274_, v_v_2292_, v_i_2289_, v_shift_2291_);
v___x_2296_ = lean_array_fset(v_xs_x27_2294_, v___x_2280_, v___x_2295_);
lean_dec(v___x_2280_);
if (v_isShared_2285_ == 0)
{
lean_ctor_set(v___x_2284_, 0, v___x_2296_);
v___x_2298_ = v___x_2284_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v___x_2296_);
v___x_2298_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2297_;
}
v_reusejp_2297_:
{
return v___x_2298_;
}
}
}
}
else
{
lean_object* v_vs_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; uint8_t v___x_2305_; 
v_vs_2302_ = lean_ctor_get(v_x_2275_, 0);
v___x_2303_ = lean_usize_to_nat(v_x_2276_);
v___x_2304_ = lean_array_get_size(v_vs_2302_);
v___x_2305_ = lean_nat_dec_lt(v___x_2303_, v___x_2304_);
if (v___x_2305_ == 0)
{
lean_dec(v___x_2303_);
lean_dec(v_y_2274_);
return v_x_2275_;
}
else
{
lean_object* v___x_2307_; uint8_t v_isShared_2308_; uint8_t v_isSharedCheck_2320_; 
lean_inc_ref(v_vs_2302_);
v_isSharedCheck_2320_ = !lean_is_exclusive(v_x_2275_);
if (v_isSharedCheck_2320_ == 0)
{
lean_object* v_unused_2321_; 
v_unused_2321_ = lean_ctor_get(v_x_2275_, 0);
lean_dec(v_unused_2321_);
v___x_2307_ = v_x_2275_;
v_isShared_2308_ = v_isSharedCheck_2320_;
goto v_resetjp_2306_;
}
else
{
lean_dec(v_x_2275_);
v___x_2307_ = lean_box(0);
v_isShared_2308_ = v_isSharedCheck_2320_;
goto v_resetjp_2306_;
}
v_resetjp_2306_:
{
lean_object* v_v_2309_; lean_object* v___x_2310_; lean_object* v_xs_x27_2311_; lean_object* v___y_2313_; uint8_t v___x_2318_; 
v_v_2309_ = lean_array_fget(v_vs_2302_, v___x_2303_);
v___x_2310_ = lean_box(0);
v_xs_x27_2311_ = lean_array_fset(v_vs_2302_, v___x_2303_, v___x_2310_);
v___x_2318_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg(v_y_2274_, v_v_2309_);
if (v___x_2318_ == 0)
{
lean_object* v___x_2319_; 
v___x_2319_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1___redArg(v_y_2274_, v___x_2310_, v_v_2309_);
v___y_2313_ = v___x_2319_;
goto v___jp_2312_;
}
else
{
lean_dec(v_y_2274_);
v___y_2313_ = v_v_2309_;
goto v___jp_2312_;
}
v___jp_2312_:
{
lean_object* v___x_2314_; lean_object* v___x_2316_; 
v___x_2314_ = lean_array_fset(v_xs_x27_2311_, v___x_2303_, v___y_2313_);
lean_dec(v___x_2303_);
if (v_isShared_2308_ == 0)
{
lean_ctor_set(v___x_2307_, 0, v___x_2314_);
v___x_2316_ = v___x_2307_;
goto v_reusejp_2315_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v___x_2314_);
v___x_2316_ = v_reuseFailAlloc_2317_;
goto v_reusejp_2315_;
}
v_reusejp_2315_:
{
return v___x_2316_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2___boxed(lean_object* v_y_2322_, lean_object* v_x_2323_, lean_object* v_x_2324_, lean_object* v_x_2325_){
_start:
{
size_t v_x_5143__boxed_2326_; size_t v_x_5144__boxed_2327_; lean_object* v_res_2328_; 
v_x_5143__boxed_2326_ = lean_unbox_usize(v_x_2324_);
lean_dec(v_x_2324_);
v_x_5144__boxed_2327_ = lean_unbox_usize(v_x_2325_);
lean_dec(v_x_2325_);
v_res_2328_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2(v_y_2322_, v_x_2323_, v_x_5143__boxed_2326_, v_x_5144__boxed_2327_);
return v_res_2328_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2(lean_object* v_y_2329_, lean_object* v_t_2330_, lean_object* v_i_2331_){
_start:
{
lean_object* v_root_2332_; lean_object* v_tail_2333_; lean_object* v_size_2334_; size_t v_shift_2335_; lean_object* v_tailOff_2336_; lean_object* v___x_2338_; uint8_t v_isShared_2339_; uint8_t v_isSharedCheck_2363_; 
v_root_2332_ = lean_ctor_get(v_t_2330_, 0);
v_tail_2333_ = lean_ctor_get(v_t_2330_, 1);
v_size_2334_ = lean_ctor_get(v_t_2330_, 2);
v_shift_2335_ = lean_ctor_get_usize(v_t_2330_, 4);
v_tailOff_2336_ = lean_ctor_get(v_t_2330_, 3);
v_isSharedCheck_2363_ = !lean_is_exclusive(v_t_2330_);
if (v_isSharedCheck_2363_ == 0)
{
v___x_2338_ = v_t_2330_;
v_isShared_2339_ = v_isSharedCheck_2363_;
goto v_resetjp_2337_;
}
else
{
lean_inc(v_tailOff_2336_);
lean_inc(v_size_2334_);
lean_inc(v_tail_2333_);
lean_inc(v_root_2332_);
lean_dec(v_t_2330_);
v___x_2338_ = lean_box(0);
v_isShared_2339_ = v_isSharedCheck_2363_;
goto v_resetjp_2337_;
}
v_resetjp_2337_:
{
uint8_t v___x_2340_; 
v___x_2340_ = lean_nat_dec_le(v_tailOff_2336_, v_i_2331_);
if (v___x_2340_ == 0)
{
size_t v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2344_; 
v___x_2341_ = lean_usize_of_nat(v_i_2331_);
v___x_2342_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2(v_y_2329_, v_root_2332_, v___x_2341_, v_shift_2335_);
if (v_isShared_2339_ == 0)
{
lean_ctor_set(v___x_2338_, 0, v___x_2342_);
v___x_2344_ = v___x_2338_;
goto v_reusejp_2343_;
}
else
{
lean_object* v_reuseFailAlloc_2345_; 
v_reuseFailAlloc_2345_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2345_, 0, v___x_2342_);
lean_ctor_set(v_reuseFailAlloc_2345_, 1, v_tail_2333_);
lean_ctor_set(v_reuseFailAlloc_2345_, 2, v_size_2334_);
lean_ctor_set(v_reuseFailAlloc_2345_, 3, v_tailOff_2336_);
lean_ctor_set_usize(v_reuseFailAlloc_2345_, 4, v_shift_2335_);
v___x_2344_ = v_reuseFailAlloc_2345_;
goto v_reusejp_2343_;
}
v_reusejp_2343_:
{
return v___x_2344_;
}
}
else
{
lean_object* v___x_2346_; lean_object* v___x_2347_; uint8_t v___x_2348_; 
v___x_2346_ = lean_nat_sub(v_i_2331_, v_tailOff_2336_);
v___x_2347_ = lean_array_get_size(v_tail_2333_);
v___x_2348_ = lean_nat_dec_lt(v___x_2346_, v___x_2347_);
if (v___x_2348_ == 0)
{
lean_object* v___x_2350_; 
lean_dec(v___x_2346_);
lean_dec(v_y_2329_);
if (v_isShared_2339_ == 0)
{
v___x_2350_ = v___x_2338_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v_root_2332_);
lean_ctor_set(v_reuseFailAlloc_2351_, 1, v_tail_2333_);
lean_ctor_set(v_reuseFailAlloc_2351_, 2, v_size_2334_);
lean_ctor_set(v_reuseFailAlloc_2351_, 3, v_tailOff_2336_);
lean_ctor_set_usize(v_reuseFailAlloc_2351_, 4, v_shift_2335_);
v___x_2350_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
return v___x_2350_;
}
}
else
{
lean_object* v_v_2352_; lean_object* v___x_2353_; lean_object* v_xs_x27_2354_; lean_object* v___y_2356_; uint8_t v___x_2361_; 
v_v_2352_ = lean_array_fget(v_tail_2333_, v___x_2346_);
v___x_2353_ = lean_box(0);
v_xs_x27_2354_ = lean_array_fset(v_tail_2333_, v___x_2346_, v___x_2353_);
v___x_2361_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg(v_y_2329_, v_v_2352_);
if (v___x_2361_ == 0)
{
lean_object* v___x_2362_; 
v___x_2362_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1___redArg(v_y_2329_, v___x_2353_, v_v_2352_);
v___y_2356_ = v___x_2362_;
goto v___jp_2355_;
}
else
{
lean_dec(v_y_2329_);
v___y_2356_ = v_v_2352_;
goto v___jp_2355_;
}
v___jp_2355_:
{
lean_object* v___x_2357_; lean_object* v___x_2359_; 
v___x_2357_ = lean_array_fset(v_xs_x27_2354_, v___x_2346_, v___y_2356_);
lean_dec(v___x_2346_);
if (v_isShared_2339_ == 0)
{
lean_ctor_set(v___x_2338_, 1, v___x_2357_);
v___x_2359_ = v___x_2338_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v_root_2332_);
lean_ctor_set(v_reuseFailAlloc_2360_, 1, v___x_2357_);
lean_ctor_set(v_reuseFailAlloc_2360_, 2, v_size_2334_);
lean_ctor_set(v_reuseFailAlloc_2360_, 3, v_tailOff_2336_);
lean_ctor_set_usize(v_reuseFailAlloc_2360_, 4, v_shift_2335_);
v___x_2359_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
return v___x_2359_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2___boxed(lean_object* v_y_2364_, lean_object* v_t_2365_, lean_object* v_i_2366_){
_start:
{
lean_object* v_res_2367_; 
v_res_2367_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2(v_y_2364_, v_t_2365_, v_i_2366_);
lean_dec(v_i_2366_);
return v_res_2367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_addOcc___lam__0(lean_object* v_a_2368_, lean_object* v_y_2369_, lean_object* v_x_2370_, lean_object* v_s_2371_){
_start:
{
lean_object* v_structs_2372_; lean_object* v_typeIdOf_2373_; lean_object* v_exprToStructId_2374_; lean_object* v_exprToStructIdEntries_2375_; lean_object* v_forbiddenNatModules_2376_; lean_object* v_natStructs_2377_; lean_object* v_natTypeIdOf_2378_; lean_object* v_exprToNatStructId_2379_; lean_object* v___x_2380_; uint8_t v___x_2381_; 
v_structs_2372_ = lean_ctor_get(v_s_2371_, 0);
v_typeIdOf_2373_ = lean_ctor_get(v_s_2371_, 1);
v_exprToStructId_2374_ = lean_ctor_get(v_s_2371_, 2);
v_exprToStructIdEntries_2375_ = lean_ctor_get(v_s_2371_, 3);
v_forbiddenNatModules_2376_ = lean_ctor_get(v_s_2371_, 4);
v_natStructs_2377_ = lean_ctor_get(v_s_2371_, 5);
v_natTypeIdOf_2378_ = lean_ctor_get(v_s_2371_, 6);
v_exprToNatStructId_2379_ = lean_ctor_get(v_s_2371_, 7);
v___x_2380_ = lean_array_get_size(v_structs_2372_);
v___x_2381_ = lean_nat_dec_lt(v_a_2368_, v___x_2380_);
if (v___x_2381_ == 0)
{
lean_dec(v_y_2369_);
return v_s_2371_;
}
else
{
lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2443_; 
lean_inc_ref(v_exprToNatStructId_2379_);
lean_inc_ref(v_natTypeIdOf_2378_);
lean_inc_ref(v_natStructs_2377_);
lean_inc_ref(v_forbiddenNatModules_2376_);
lean_inc_ref(v_exprToStructIdEntries_2375_);
lean_inc_ref(v_exprToStructId_2374_);
lean_inc_ref(v_typeIdOf_2373_);
lean_inc_ref(v_structs_2372_);
v_isSharedCheck_2443_ = !lean_is_exclusive(v_s_2371_);
if (v_isSharedCheck_2443_ == 0)
{
lean_object* v_unused_2444_; lean_object* v_unused_2445_; lean_object* v_unused_2446_; lean_object* v_unused_2447_; lean_object* v_unused_2448_; lean_object* v_unused_2449_; lean_object* v_unused_2450_; lean_object* v_unused_2451_; 
v_unused_2444_ = lean_ctor_get(v_s_2371_, 7);
lean_dec(v_unused_2444_);
v_unused_2445_ = lean_ctor_get(v_s_2371_, 6);
lean_dec(v_unused_2445_);
v_unused_2446_ = lean_ctor_get(v_s_2371_, 5);
lean_dec(v_unused_2446_);
v_unused_2447_ = lean_ctor_get(v_s_2371_, 4);
lean_dec(v_unused_2447_);
v_unused_2448_ = lean_ctor_get(v_s_2371_, 3);
lean_dec(v_unused_2448_);
v_unused_2449_ = lean_ctor_get(v_s_2371_, 2);
lean_dec(v_unused_2449_);
v_unused_2450_ = lean_ctor_get(v_s_2371_, 1);
lean_dec(v_unused_2450_);
v_unused_2451_ = lean_ctor_get(v_s_2371_, 0);
lean_dec(v_unused_2451_);
v___x_2383_ = v_s_2371_;
v_isShared_2384_ = v_isSharedCheck_2443_;
goto v_resetjp_2382_;
}
else
{
lean_dec(v_s_2371_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2443_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
lean_object* v_v_2385_; lean_object* v_id_2386_; lean_object* v_ringId_x3f_2387_; lean_object* v_type_2388_; lean_object* v_u_2389_; lean_object* v_intModuleInst_2390_; lean_object* v_leInst_x3f_2391_; lean_object* v_ltInst_x3f_2392_; lean_object* v_lawfulOrderLTInst_x3f_2393_; lean_object* v_isPreorderInst_x3f_2394_; lean_object* v_orderedAddInst_x3f_2395_; lean_object* v_isLinearInst_x3f_2396_; lean_object* v_noNatDivInst_x3f_2397_; lean_object* v_ringInst_x3f_2398_; lean_object* v_commRingInst_x3f_2399_; lean_object* v_orderedRingInst_x3f_2400_; lean_object* v_fieldInst_x3f_2401_; lean_object* v_charInst_x3f_2402_; lean_object* v_zero_2403_; lean_object* v_ofNatZero_2404_; lean_object* v_one_x3f_2405_; lean_object* v_leFn_x3f_2406_; lean_object* v_ltFn_x3f_2407_; lean_object* v_addFn_2408_; lean_object* v_zsmulFn_2409_; lean_object* v_nsmulFn_2410_; lean_object* v_zsmulFn_x3f_2411_; lean_object* v_nsmulFn_x3f_2412_; lean_object* v_homomulFn_x3f_2413_; lean_object* v_subFn_2414_; lean_object* v_negFn_2415_; lean_object* v_vars_2416_; lean_object* v_varMap_2417_; lean_object* v_lowers_2418_; lean_object* v_uppers_2419_; lean_object* v_diseqs_2420_; lean_object* v_assignment_2421_; uint8_t v_caseSplits_2422_; lean_object* v_conflict_x3f_2423_; lean_object* v_diseqSplits_2424_; lean_object* v_elimEqs_2425_; lean_object* v_elimStack_2426_; lean_object* v_occurs_2427_; lean_object* v_ignored_2428_; lean_object* v___x_2430_; uint8_t v_isShared_2431_; uint8_t v_isSharedCheck_2442_; 
v_v_2385_ = lean_array_fget(v_structs_2372_, v_a_2368_);
v_id_2386_ = lean_ctor_get(v_v_2385_, 0);
v_ringId_x3f_2387_ = lean_ctor_get(v_v_2385_, 1);
v_type_2388_ = lean_ctor_get(v_v_2385_, 2);
v_u_2389_ = lean_ctor_get(v_v_2385_, 3);
v_intModuleInst_2390_ = lean_ctor_get(v_v_2385_, 4);
v_leInst_x3f_2391_ = lean_ctor_get(v_v_2385_, 5);
v_ltInst_x3f_2392_ = lean_ctor_get(v_v_2385_, 6);
v_lawfulOrderLTInst_x3f_2393_ = lean_ctor_get(v_v_2385_, 7);
v_isPreorderInst_x3f_2394_ = lean_ctor_get(v_v_2385_, 8);
v_orderedAddInst_x3f_2395_ = lean_ctor_get(v_v_2385_, 9);
v_isLinearInst_x3f_2396_ = lean_ctor_get(v_v_2385_, 10);
v_noNatDivInst_x3f_2397_ = lean_ctor_get(v_v_2385_, 11);
v_ringInst_x3f_2398_ = lean_ctor_get(v_v_2385_, 12);
v_commRingInst_x3f_2399_ = lean_ctor_get(v_v_2385_, 13);
v_orderedRingInst_x3f_2400_ = lean_ctor_get(v_v_2385_, 14);
v_fieldInst_x3f_2401_ = lean_ctor_get(v_v_2385_, 15);
v_charInst_x3f_2402_ = lean_ctor_get(v_v_2385_, 16);
v_zero_2403_ = lean_ctor_get(v_v_2385_, 17);
v_ofNatZero_2404_ = lean_ctor_get(v_v_2385_, 18);
v_one_x3f_2405_ = lean_ctor_get(v_v_2385_, 19);
v_leFn_x3f_2406_ = lean_ctor_get(v_v_2385_, 20);
v_ltFn_x3f_2407_ = lean_ctor_get(v_v_2385_, 21);
v_addFn_2408_ = lean_ctor_get(v_v_2385_, 22);
v_zsmulFn_2409_ = lean_ctor_get(v_v_2385_, 23);
v_nsmulFn_2410_ = lean_ctor_get(v_v_2385_, 24);
v_zsmulFn_x3f_2411_ = lean_ctor_get(v_v_2385_, 25);
v_nsmulFn_x3f_2412_ = lean_ctor_get(v_v_2385_, 26);
v_homomulFn_x3f_2413_ = lean_ctor_get(v_v_2385_, 27);
v_subFn_2414_ = lean_ctor_get(v_v_2385_, 28);
v_negFn_2415_ = lean_ctor_get(v_v_2385_, 29);
v_vars_2416_ = lean_ctor_get(v_v_2385_, 30);
v_varMap_2417_ = lean_ctor_get(v_v_2385_, 31);
v_lowers_2418_ = lean_ctor_get(v_v_2385_, 32);
v_uppers_2419_ = lean_ctor_get(v_v_2385_, 33);
v_diseqs_2420_ = lean_ctor_get(v_v_2385_, 34);
v_assignment_2421_ = lean_ctor_get(v_v_2385_, 35);
v_caseSplits_2422_ = lean_ctor_get_uint8(v_v_2385_, sizeof(void*)*42);
v_conflict_x3f_2423_ = lean_ctor_get(v_v_2385_, 36);
v_diseqSplits_2424_ = lean_ctor_get(v_v_2385_, 37);
v_elimEqs_2425_ = lean_ctor_get(v_v_2385_, 38);
v_elimStack_2426_ = lean_ctor_get(v_v_2385_, 39);
v_occurs_2427_ = lean_ctor_get(v_v_2385_, 40);
v_ignored_2428_ = lean_ctor_get(v_v_2385_, 41);
v_isSharedCheck_2442_ = !lean_is_exclusive(v_v_2385_);
if (v_isSharedCheck_2442_ == 0)
{
v___x_2430_ = v_v_2385_;
v_isShared_2431_ = v_isSharedCheck_2442_;
goto v_resetjp_2429_;
}
else
{
lean_inc(v_ignored_2428_);
lean_inc(v_occurs_2427_);
lean_inc(v_elimStack_2426_);
lean_inc(v_elimEqs_2425_);
lean_inc(v_diseqSplits_2424_);
lean_inc(v_conflict_x3f_2423_);
lean_inc(v_assignment_2421_);
lean_inc(v_diseqs_2420_);
lean_inc(v_uppers_2419_);
lean_inc(v_lowers_2418_);
lean_inc(v_varMap_2417_);
lean_inc(v_vars_2416_);
lean_inc(v_negFn_2415_);
lean_inc(v_subFn_2414_);
lean_inc(v_homomulFn_x3f_2413_);
lean_inc(v_nsmulFn_x3f_2412_);
lean_inc(v_zsmulFn_x3f_2411_);
lean_inc(v_nsmulFn_2410_);
lean_inc(v_zsmulFn_2409_);
lean_inc(v_addFn_2408_);
lean_inc(v_ltFn_x3f_2407_);
lean_inc(v_leFn_x3f_2406_);
lean_inc(v_one_x3f_2405_);
lean_inc(v_ofNatZero_2404_);
lean_inc(v_zero_2403_);
lean_inc(v_charInst_x3f_2402_);
lean_inc(v_fieldInst_x3f_2401_);
lean_inc(v_orderedRingInst_x3f_2400_);
lean_inc(v_commRingInst_x3f_2399_);
lean_inc(v_ringInst_x3f_2398_);
lean_inc(v_noNatDivInst_x3f_2397_);
lean_inc(v_isLinearInst_x3f_2396_);
lean_inc(v_orderedAddInst_x3f_2395_);
lean_inc(v_isPreorderInst_x3f_2394_);
lean_inc(v_lawfulOrderLTInst_x3f_2393_);
lean_inc(v_ltInst_x3f_2392_);
lean_inc(v_leInst_x3f_2391_);
lean_inc(v_intModuleInst_2390_);
lean_inc(v_u_2389_);
lean_inc(v_type_2388_);
lean_inc(v_ringId_x3f_2387_);
lean_inc(v_id_2386_);
lean_dec(v_v_2385_);
v___x_2430_ = lean_box(0);
v_isShared_2431_ = v_isSharedCheck_2442_;
goto v_resetjp_2429_;
}
v_resetjp_2429_:
{
lean_object* v___x_2432_; lean_object* v_xs_x27_2433_; lean_object* v___x_2434_; lean_object* v___x_2436_; 
v___x_2432_ = lean_box(0);
v_xs_x27_2433_ = lean_array_fset(v_structs_2372_, v_a_2368_, v___x_2432_);
v___x_2434_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2(v_y_2369_, v_occurs_2427_, v_x_2370_);
if (v_isShared_2431_ == 0)
{
lean_ctor_set(v___x_2430_, 40, v___x_2434_);
v___x_2436_ = v___x_2430_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2441_; 
v_reuseFailAlloc_2441_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_2441_, 0, v_id_2386_);
lean_ctor_set(v_reuseFailAlloc_2441_, 1, v_ringId_x3f_2387_);
lean_ctor_set(v_reuseFailAlloc_2441_, 2, v_type_2388_);
lean_ctor_set(v_reuseFailAlloc_2441_, 3, v_u_2389_);
lean_ctor_set(v_reuseFailAlloc_2441_, 4, v_intModuleInst_2390_);
lean_ctor_set(v_reuseFailAlloc_2441_, 5, v_leInst_x3f_2391_);
lean_ctor_set(v_reuseFailAlloc_2441_, 6, v_ltInst_x3f_2392_);
lean_ctor_set(v_reuseFailAlloc_2441_, 7, v_lawfulOrderLTInst_x3f_2393_);
lean_ctor_set(v_reuseFailAlloc_2441_, 8, v_isPreorderInst_x3f_2394_);
lean_ctor_set(v_reuseFailAlloc_2441_, 9, v_orderedAddInst_x3f_2395_);
lean_ctor_set(v_reuseFailAlloc_2441_, 10, v_isLinearInst_x3f_2396_);
lean_ctor_set(v_reuseFailAlloc_2441_, 11, v_noNatDivInst_x3f_2397_);
lean_ctor_set(v_reuseFailAlloc_2441_, 12, v_ringInst_x3f_2398_);
lean_ctor_set(v_reuseFailAlloc_2441_, 13, v_commRingInst_x3f_2399_);
lean_ctor_set(v_reuseFailAlloc_2441_, 14, v_orderedRingInst_x3f_2400_);
lean_ctor_set(v_reuseFailAlloc_2441_, 15, v_fieldInst_x3f_2401_);
lean_ctor_set(v_reuseFailAlloc_2441_, 16, v_charInst_x3f_2402_);
lean_ctor_set(v_reuseFailAlloc_2441_, 17, v_zero_2403_);
lean_ctor_set(v_reuseFailAlloc_2441_, 18, v_ofNatZero_2404_);
lean_ctor_set(v_reuseFailAlloc_2441_, 19, v_one_x3f_2405_);
lean_ctor_set(v_reuseFailAlloc_2441_, 20, v_leFn_x3f_2406_);
lean_ctor_set(v_reuseFailAlloc_2441_, 21, v_ltFn_x3f_2407_);
lean_ctor_set(v_reuseFailAlloc_2441_, 22, v_addFn_2408_);
lean_ctor_set(v_reuseFailAlloc_2441_, 23, v_zsmulFn_2409_);
lean_ctor_set(v_reuseFailAlloc_2441_, 24, v_nsmulFn_2410_);
lean_ctor_set(v_reuseFailAlloc_2441_, 25, v_zsmulFn_x3f_2411_);
lean_ctor_set(v_reuseFailAlloc_2441_, 26, v_nsmulFn_x3f_2412_);
lean_ctor_set(v_reuseFailAlloc_2441_, 27, v_homomulFn_x3f_2413_);
lean_ctor_set(v_reuseFailAlloc_2441_, 28, v_subFn_2414_);
lean_ctor_set(v_reuseFailAlloc_2441_, 29, v_negFn_2415_);
lean_ctor_set(v_reuseFailAlloc_2441_, 30, v_vars_2416_);
lean_ctor_set(v_reuseFailAlloc_2441_, 31, v_varMap_2417_);
lean_ctor_set(v_reuseFailAlloc_2441_, 32, v_lowers_2418_);
lean_ctor_set(v_reuseFailAlloc_2441_, 33, v_uppers_2419_);
lean_ctor_set(v_reuseFailAlloc_2441_, 34, v_diseqs_2420_);
lean_ctor_set(v_reuseFailAlloc_2441_, 35, v_assignment_2421_);
lean_ctor_set(v_reuseFailAlloc_2441_, 36, v_conflict_x3f_2423_);
lean_ctor_set(v_reuseFailAlloc_2441_, 37, v_diseqSplits_2424_);
lean_ctor_set(v_reuseFailAlloc_2441_, 38, v_elimEqs_2425_);
lean_ctor_set(v_reuseFailAlloc_2441_, 39, v_elimStack_2426_);
lean_ctor_set(v_reuseFailAlloc_2441_, 40, v___x_2434_);
lean_ctor_set(v_reuseFailAlloc_2441_, 41, v_ignored_2428_);
lean_ctor_set_uint8(v_reuseFailAlloc_2441_, sizeof(void*)*42, v_caseSplits_2422_);
v___x_2436_ = v_reuseFailAlloc_2441_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
lean_object* v___x_2437_; lean_object* v___x_2439_; 
v___x_2437_ = lean_array_fset(v_xs_x27_2433_, v_a_2368_, v___x_2436_);
if (v_isShared_2384_ == 0)
{
lean_ctor_set(v___x_2383_, 0, v___x_2437_);
v___x_2439_ = v___x_2383_;
goto v_reusejp_2438_;
}
else
{
lean_object* v_reuseFailAlloc_2440_; 
v_reuseFailAlloc_2440_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2440_, 0, v___x_2437_);
lean_ctor_set(v_reuseFailAlloc_2440_, 1, v_typeIdOf_2373_);
lean_ctor_set(v_reuseFailAlloc_2440_, 2, v_exprToStructId_2374_);
lean_ctor_set(v_reuseFailAlloc_2440_, 3, v_exprToStructIdEntries_2375_);
lean_ctor_set(v_reuseFailAlloc_2440_, 4, v_forbiddenNatModules_2376_);
lean_ctor_set(v_reuseFailAlloc_2440_, 5, v_natStructs_2377_);
lean_ctor_set(v_reuseFailAlloc_2440_, 6, v_natTypeIdOf_2378_);
lean_ctor_set(v_reuseFailAlloc_2440_, 7, v_exprToNatStructId_2379_);
v___x_2439_ = v_reuseFailAlloc_2440_;
goto v_reusejp_2438_;
}
v_reusejp_2438_:
{
return v___x_2439_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_addOcc___lam__0___boxed(lean_object* v_a_2452_, lean_object* v_y_2453_, lean_object* v_x_2454_, lean_object* v_s_2455_){
_start:
{
lean_object* v_res_2456_; 
v_res_2456_ = l_Lean_Meta_Grind_Arith_Linear_addOcc___lam__0(v_a_2452_, v_y_2453_, v_x_2454_, v_s_2455_);
lean_dec(v_x_2454_);
lean_dec(v_a_2452_);
return v_res_2456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_addOcc(lean_object* v_x_2457_, lean_object* v_y_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_){
_start:
{
lean_object* v___x_2471_; 
v___x_2471_ = l_Lean_Meta_Grind_Arith_Linear_getOccursOf(v_x_2457_, v_a_2459_, v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_);
if (lean_obj_tag(v___x_2471_) == 0)
{
lean_object* v_a_2472_; lean_object* v___x_2474_; uint8_t v_isShared_2475_; uint8_t v_isSharedCheck_2484_; 
v_a_2472_ = lean_ctor_get(v___x_2471_, 0);
v_isSharedCheck_2484_ = !lean_is_exclusive(v___x_2471_);
if (v_isSharedCheck_2484_ == 0)
{
v___x_2474_ = v___x_2471_;
v_isShared_2475_ = v_isSharedCheck_2484_;
goto v_resetjp_2473_;
}
else
{
lean_inc(v_a_2472_);
lean_dec(v___x_2471_);
v___x_2474_ = lean_box(0);
v_isShared_2475_ = v_isSharedCheck_2484_;
goto v_resetjp_2473_;
}
v_resetjp_2473_:
{
uint8_t v___x_2476_; 
v___x_2476_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg(v_y_2458_, v_a_2472_);
lean_dec(v_a_2472_);
if (v___x_2476_ == 0)
{
lean_object* v___f_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; 
lean_del_object(v___x_2474_);
lean_inc(v_a_2459_);
v___f_2477_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_addOcc___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2477_, 0, v_a_2459_);
lean_closure_set(v___f_2477_, 1, v_y_2458_);
lean_closure_set(v___f_2477_, 2, v_x_2457_);
v___x_2478_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2479_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2478_, v___f_2477_, v_a_2460_);
return v___x_2479_;
}
else
{
lean_object* v___x_2480_; lean_object* v___x_2482_; 
lean_dec(v_y_2458_);
lean_dec(v_x_2457_);
v___x_2480_ = lean_box(0);
if (v_isShared_2475_ == 0)
{
lean_ctor_set(v___x_2474_, 0, v___x_2480_);
v___x_2482_ = v___x_2474_;
goto v_reusejp_2481_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v___x_2480_);
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
else
{
lean_object* v_a_2485_; lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2492_; 
lean_dec(v_y_2458_);
lean_dec(v_x_2457_);
v_a_2485_ = lean_ctor_get(v___x_2471_, 0);
v_isSharedCheck_2492_ = !lean_is_exclusive(v___x_2471_);
if (v_isSharedCheck_2492_ == 0)
{
v___x_2487_ = v___x_2471_;
v_isShared_2488_ = v_isSharedCheck_2492_;
goto v_resetjp_2486_;
}
else
{
lean_inc(v_a_2485_);
lean_dec(v___x_2471_);
v___x_2487_ = lean_box(0);
v_isShared_2488_ = v_isSharedCheck_2492_;
goto v_resetjp_2486_;
}
v_resetjp_2486_:
{
lean_object* v___x_2490_; 
if (v_isShared_2488_ == 0)
{
v___x_2490_ = v___x_2487_;
goto v_reusejp_2489_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v_a_2485_);
v___x_2490_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2489_;
}
v_reusejp_2489_:
{
return v___x_2490_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_addOcc___boxed(lean_object* v_x_2493_, lean_object* v_y_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_){
_start:
{
lean_object* v_res_2507_; 
v_res_2507_ = l_Lean_Meta_Grind_Arith_Linear_addOcc(v_x_2493_, v_y_2494_, v_a_2495_, v_a_2496_, v_a_2497_, v_a_2498_, v_a_2499_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_, v_a_2504_, v_a_2505_);
lean_dec(v_a_2505_);
lean_dec_ref(v_a_2504_);
lean_dec(v_a_2503_);
lean_dec_ref(v_a_2502_);
lean_dec(v_a_2501_);
lean_dec_ref(v_a_2500_);
lean_dec(v_a_2499_);
lean_dec_ref(v_a_2498_);
lean_dec(v_a_2497_);
lean_dec(v_a_2496_);
lean_dec(v_a_2495_);
return v_res_2507_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0(lean_object* v_00_u03b2_2508_, lean_object* v_k_2509_, lean_object* v_t_2510_){
_start:
{
uint8_t v___x_2511_; 
v___x_2511_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg(v_k_2509_, v_t_2510_);
return v___x_2511_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___boxed(lean_object* v_00_u03b2_2512_, lean_object* v_k_2513_, lean_object* v_t_2514_){
_start:
{
uint8_t v_res_2515_; lean_object* v_r_2516_; 
v_res_2515_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0(v_00_u03b2_2512_, v_k_2513_, v_t_2514_);
lean_dec(v_t_2514_);
lean_dec(v_k_2513_);
v_r_2516_ = lean_box(v_res_2515_);
return v_r_2516_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1(lean_object* v_00_u03b2_2517_, lean_object* v_k_2518_, lean_object* v_v_2519_, lean_object* v_t_2520_, lean_object* v_hl_2521_){
_start:
{
lean_object* v___x_2522_; 
v___x_2522_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1___redArg(v_k_2518_, v_v_2519_, v_t_2520_);
return v___x_2522_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_updateOccs_go(lean_object* v_y_2523_, lean_object* v_p_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_){
_start:
{
if (lean_obj_tag(v_p_2524_) == 1)
{
lean_object* v_v_2537_; lean_object* v_p_2538_; lean_object* v___x_2539_; 
v_v_2537_ = lean_ctor_get(v_p_2524_, 1);
lean_inc(v_v_2537_);
v_p_2538_ = lean_ctor_get(v_p_2524_, 2);
lean_inc(v_p_2538_);
lean_dec_ref_known(v_p_2524_, 3);
lean_inc(v_y_2523_);
v___x_2539_ = l_Lean_Meta_Grind_Arith_Linear_addOcc(v_v_2537_, v_y_2523_, v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_, v_a_2535_);
if (lean_obj_tag(v___x_2539_) == 0)
{
lean_dec_ref_known(v___x_2539_, 1);
v_p_2524_ = v_p_2538_;
goto _start;
}
else
{
lean_dec(v_p_2538_);
lean_dec(v_y_2523_);
return v___x_2539_;
}
}
else
{
lean_object* v___x_2541_; lean_object* v___x_2542_; 
lean_dec(v_p_2524_);
lean_dec(v_y_2523_);
v___x_2541_ = lean_box(0);
v___x_2542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2542_, 0, v___x_2541_);
return v___x_2542_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_updateOccs_go___boxed(lean_object* v_y_2543_, lean_object* v_p_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_){
_start:
{
lean_object* v_res_2557_; 
v_res_2557_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_updateOccs_go(v_y_2543_, v_p_2544_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_);
lean_dec(v_a_2555_);
lean_dec_ref(v_a_2554_);
lean_dec(v_a_2553_);
lean_dec_ref(v_a_2552_);
lean_dec(v_a_2551_);
lean_dec_ref(v_a_2550_);
lean_dec(v_a_2549_);
lean_dec_ref(v_a_2548_);
lean_dec(v_a_2547_);
lean_dec(v_a_2546_);
lean_dec(v_a_2545_);
return v_res_2557_;
}
}
static lean_object* _init_l_Lean_Grind_Linarith_Poly_updateOccs___closed__1(void){
_start:
{
lean_object* v___x_2559_; lean_object* v___x_2560_; 
v___x_2559_ = ((lean_object*)(l_Lean_Grind_Linarith_Poly_updateOccs___closed__0));
v___x_2560_ = l_Lean_stringToMessageData(v___x_2559_);
return v___x_2560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_updateOccs(lean_object* v_p_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_){
_start:
{
if (lean_obj_tag(v_p_2561_) == 1)
{
lean_object* v_v_2574_; lean_object* v_p_2575_; lean_object* v___x_2576_; 
v_v_2574_ = lean_ctor_get(v_p_2561_, 1);
lean_inc(v_v_2574_);
v_p_2575_ = lean_ctor_get(v_p_2561_, 2);
lean_inc(v_p_2575_);
lean_dec_ref_known(v_p_2561_, 3);
v___x_2576_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_updateOccs_go(v_v_2574_, v_p_2575_, v_a_2562_, v_a_2563_, v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_);
return v___x_2576_;
}
else
{
lean_object* v___x_2577_; lean_object* v___x_2578_; 
lean_dec(v_p_2561_);
v___x_2577_ = lean_obj_once(&l_Lean_Grind_Linarith_Poly_updateOccs___closed__1, &l_Lean_Grind_Linarith_Poly_updateOccs___closed__1_once, _init_l_Lean_Grind_Linarith_Poly_updateOccs___closed__1);
v___x_2578_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_2577_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_);
return v___x_2578_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_updateOccs___boxed(lean_object* v_p_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_){
_start:
{
lean_object* v_res_2592_; 
v_res_2592_ = l_Lean_Grind_Linarith_Poly_updateOccs(v_p_2579_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_, v_a_2585_, v_a_2586_, v_a_2587_, v_a_2588_, v_a_2589_, v_a_2590_);
lean_dec(v_a_2590_);
lean_dec_ref(v_a_2589_);
lean_dec(v_a_2588_);
lean_dec_ref(v_a_2587_);
lean_dec(v_a_2586_);
lean_dec_ref(v_a_2585_);
lean_dec(v_a_2584_);
lean_dec_ref(v_a_2583_);
lean_dec(v_a_2582_);
lean_dec(v_a_2581_);
lean_dec(v_a_2580_);
return v_res_2592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_findVarToSubst(lean_object* v_p_2593_, lean_object* v_a_2594_, lean_object* v_a_2595_, lean_object* v_a_2596_, lean_object* v_a_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_){
_start:
{
if (lean_obj_tag(v_p_2593_) == 0)
{
lean_object* v___x_2606_; lean_object* v___x_2607_; 
v___x_2606_ = lean_box(0);
v___x_2607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2607_, 0, v___x_2606_);
return v___x_2607_;
}
else
{
lean_object* v_k_2608_; lean_object* v_v_2609_; lean_object* v_p_2610_; lean_object* v___x_2611_; 
v_k_2608_ = lean_ctor_get(v_p_2593_, 0);
v_v_2609_ = lean_ctor_get(v_p_2593_, 1);
v_p_2610_ = lean_ctor_get(v_p_2593_, 2);
v___x_2611_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_2594_, v_a_2595_, v_a_2596_, v_a_2597_, v_a_2598_, v_a_2599_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_);
if (lean_obj_tag(v___x_2611_) == 0)
{
lean_object* v_a_2612_; lean_object* v___x_2614_; uint8_t v_isShared_2615_; uint8_t v_isSharedCheck_2638_; 
v_a_2612_ = lean_ctor_get(v___x_2611_, 0);
v_isSharedCheck_2638_ = !lean_is_exclusive(v___x_2611_);
if (v_isSharedCheck_2638_ == 0)
{
v___x_2614_ = v___x_2611_;
v_isShared_2615_ = v_isSharedCheck_2638_;
goto v_resetjp_2613_;
}
else
{
lean_inc(v_a_2612_);
lean_dec(v___x_2611_);
v___x_2614_ = lean_box(0);
v_isShared_2615_ = v_isSharedCheck_2638_;
goto v_resetjp_2613_;
}
v_resetjp_2613_:
{
lean_object* v___y_2617_; lean_object* v_elimEqs_2632_; lean_object* v_size_2633_; lean_object* v___x_2634_; uint8_t v___x_2635_; 
v_elimEqs_2632_ = lean_ctor_get(v_a_2612_, 38);
lean_inc_ref(v_elimEqs_2632_);
lean_dec(v_a_2612_);
v_size_2633_ = lean_ctor_get(v_elimEqs_2632_, 2);
v___x_2634_ = lean_box(0);
v___x_2635_ = lean_nat_dec_lt(v_v_2609_, v_size_2633_);
if (v___x_2635_ == 0)
{
lean_object* v___x_2636_; 
lean_dec_ref(v_elimEqs_2632_);
v___x_2636_ = l_outOfBounds___redArg(v___x_2634_);
v___y_2617_ = v___x_2636_;
goto v___jp_2616_;
}
else
{
lean_object* v___x_2637_; 
v___x_2637_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2634_, v_elimEqs_2632_, v_v_2609_);
lean_dec_ref(v_elimEqs_2632_);
v___y_2617_ = v___x_2637_;
goto v___jp_2616_;
}
v___jp_2616_:
{
if (lean_obj_tag(v___y_2617_) == 1)
{
lean_object* v_val_2618_; lean_object* v___x_2620_; uint8_t v_isShared_2621_; uint8_t v_isSharedCheck_2630_; 
v_val_2618_ = lean_ctor_get(v___y_2617_, 0);
v_isSharedCheck_2630_ = !lean_is_exclusive(v___y_2617_);
if (v_isSharedCheck_2630_ == 0)
{
v___x_2620_ = v___y_2617_;
v_isShared_2621_ = v_isSharedCheck_2630_;
goto v_resetjp_2619_;
}
else
{
lean_inc(v_val_2618_);
lean_dec(v___y_2617_);
v___x_2620_ = lean_box(0);
v_isShared_2621_ = v_isSharedCheck_2630_;
goto v_resetjp_2619_;
}
v_resetjp_2619_:
{
lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2625_; 
lean_inc(v_v_2609_);
v___x_2622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2622_, 0, v_v_2609_);
lean_ctor_set(v___x_2622_, 1, v_val_2618_);
lean_inc(v_k_2608_);
v___x_2623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2623_, 0, v_k_2608_);
lean_ctor_set(v___x_2623_, 1, v___x_2622_);
if (v_isShared_2621_ == 0)
{
lean_ctor_set(v___x_2620_, 0, v___x_2623_);
v___x_2625_ = v___x_2620_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2629_; 
v_reuseFailAlloc_2629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2629_, 0, v___x_2623_);
v___x_2625_ = v_reuseFailAlloc_2629_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
lean_object* v___x_2627_; 
if (v_isShared_2615_ == 0)
{
lean_ctor_set(v___x_2614_, 0, v___x_2625_);
v___x_2627_ = v___x_2614_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2628_; 
v_reuseFailAlloc_2628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2628_, 0, v___x_2625_);
v___x_2627_ = v_reuseFailAlloc_2628_;
goto v_reusejp_2626_;
}
v_reusejp_2626_:
{
return v___x_2627_;
}
}
}
}
else
{
lean_dec(v___y_2617_);
lean_del_object(v___x_2614_);
v_p_2593_ = v_p_2610_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2639_; lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2646_; 
v_a_2639_ = lean_ctor_get(v___x_2611_, 0);
v_isSharedCheck_2646_ = !lean_is_exclusive(v___x_2611_);
if (v_isSharedCheck_2646_ == 0)
{
v___x_2641_ = v___x_2611_;
v_isShared_2642_ = v_isSharedCheck_2646_;
goto v_resetjp_2640_;
}
else
{
lean_inc(v_a_2639_);
lean_dec(v___x_2611_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2646_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
lean_object* v___x_2644_; 
if (v_isShared_2642_ == 0)
{
v___x_2644_ = v___x_2641_;
goto v_reusejp_2643_;
}
else
{
lean_object* v_reuseFailAlloc_2645_; 
v_reuseFailAlloc_2645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2645_, 0, v_a_2639_);
v___x_2644_ = v_reuseFailAlloc_2645_;
goto v_reusejp_2643_;
}
v_reusejp_2643_:
{
return v___x_2644_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_findVarToSubst___boxed(lean_object* v_p_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_){
_start:
{
lean_object* v_res_2660_; 
v_res_2660_ = l_Lean_Grind_Linarith_Poly_findVarToSubst(v_p_2647_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_, v_a_2656_, v_a_2657_, v_a_2658_);
lean_dec(v_a_2658_);
lean_dec_ref(v_a_2657_);
lean_dec(v_a_2656_);
lean_dec_ref(v_a_2655_);
lean_dec(v_a_2654_);
lean_dec_ref(v_a_2653_);
lean_dec(v_a_2652_);
lean_dec_ref(v_a_2651_);
lean_dec(v_a_2650_);
lean_dec(v_a_2649_);
lean_dec(v_a_2648_);
lean_dec(v_p_2647_);
return v_res_2660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_gcdCoeffsAux(lean_object* v_x_2661_, lean_object* v_x_2662_){
_start:
{
if (lean_obj_tag(v_x_2661_) == 0)
{
return v_x_2662_;
}
else
{
lean_object* v_k_2663_; lean_object* v_p_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; 
v_k_2663_ = lean_ctor_get(v_x_2661_, 0);
v_p_2664_ = lean_ctor_get(v_x_2661_, 2);
v___x_2665_ = lean_nat_to_int(v_x_2662_);
v___x_2666_ = l_Int_gcd(v_k_2663_, v___x_2665_);
lean_dec(v___x_2665_);
v_x_2661_ = v_p_2664_;
v_x_2662_ = v___x_2666_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_gcdCoeffsAux___boxed(lean_object* v_x_2668_, lean_object* v_x_2669_){
_start:
{
lean_object* v_res_2670_; 
v_res_2670_ = l_Lean_Grind_Linarith_Poly_gcdCoeffsAux(v_x_2668_, v_x_2669_);
lean_dec(v_x_2668_);
return v_res_2670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_gcdCoeffs(lean_object* v_p_2671_){
_start:
{
if (lean_obj_tag(v_p_2671_) == 0)
{
lean_object* v___x_2672_; 
v___x_2672_ = lean_unsigned_to_nat(1u);
return v___x_2672_;
}
else
{
lean_object* v_k_2673_; lean_object* v_p_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; 
v_k_2673_ = lean_ctor_get(v_p_2671_, 0);
v_p_2674_ = lean_ctor_get(v_p_2671_, 2);
v___x_2675_ = lean_nat_abs(v_k_2673_);
v___x_2676_ = l_Lean_Grind_Linarith_Poly_gcdCoeffsAux(v_p_2674_, v___x_2675_);
return v___x_2676_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_gcdCoeffs___boxed(lean_object* v_p_2677_){
_start:
{
lean_object* v_res_2678_; 
v_res_2678_ = l_Lean_Grind_Linarith_Poly_gcdCoeffs(v_p_2677_);
lean_dec(v_p_2677_);
return v_res_2678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_div(lean_object* v_p_2679_, lean_object* v_k_2680_){
_start:
{
if (lean_obj_tag(v_p_2679_) == 0)
{
return v_p_2679_;
}
else
{
lean_object* v_k_2681_; lean_object* v_v_2682_; lean_object* v_p_2683_; lean_object* v___x_2685_; uint8_t v_isShared_2686_; uint8_t v_isSharedCheck_2692_; 
v_k_2681_ = lean_ctor_get(v_p_2679_, 0);
v_v_2682_ = lean_ctor_get(v_p_2679_, 1);
v_p_2683_ = lean_ctor_get(v_p_2679_, 2);
v_isSharedCheck_2692_ = !lean_is_exclusive(v_p_2679_);
if (v_isSharedCheck_2692_ == 0)
{
v___x_2685_ = v_p_2679_;
v_isShared_2686_ = v_isSharedCheck_2692_;
goto v_resetjp_2684_;
}
else
{
lean_inc(v_p_2683_);
lean_inc(v_v_2682_);
lean_inc(v_k_2681_);
lean_dec(v_p_2679_);
v___x_2685_ = lean_box(0);
v_isShared_2686_ = v_isSharedCheck_2692_;
goto v_resetjp_2684_;
}
v_resetjp_2684_:
{
lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2690_; 
v___x_2687_ = lean_int_ediv(v_k_2681_, v_k_2680_);
lean_dec(v_k_2681_);
v___x_2688_ = l_Lean_Grind_Linarith_Poly_div(v_p_2683_, v_k_2680_);
if (v_isShared_2686_ == 0)
{
lean_ctor_set(v___x_2685_, 2, v___x_2688_);
lean_ctor_set(v___x_2685_, 0, v___x_2687_);
v___x_2690_ = v___x_2685_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v___x_2687_);
lean_ctor_set(v_reuseFailAlloc_2691_, 1, v_v_2682_);
lean_ctor_set(v_reuseFailAlloc_2691_, 2, v___x_2688_);
v___x_2690_ = v_reuseFailAlloc_2691_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
return v___x_2690_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_div___boxed(lean_object* v_p_2693_, lean_object* v_k_2694_){
_start:
{
lean_object* v_res_2695_; 
v_res_2695_ = l_Lean_Grind_Linarith_Poly_div(v_p_2693_, v_k_2694_);
lean_dec(v_k_2694_);
return v_res_2695_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__0(void){
_start:
{
lean_object* v___x_2696_; lean_object* v___x_2697_; 
v___x_2696_ = lean_unsigned_to_nat(1u);
v___x_2697_ = lean_nat_to_int(v___x_2696_);
return v___x_2697_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__1(void){
_start:
{
lean_object* v___x_2698_; lean_object* v___x_2699_; 
v___x_2698_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__0);
v___x_2699_ = lean_int_neg(v___x_2698_);
return v___x_2699_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go(lean_object* v_k_2700_, lean_object* v_x_2701_, lean_object* v_p_2702_){
_start:
{
lean_object* v___x_2703_; uint8_t v___x_2704_; 
v___x_2703_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__0);
v___x_2704_ = lean_int_dec_eq(v_k_2700_, v___x_2703_);
if (v___x_2704_ == 0)
{
lean_object* v___x_2705_; uint8_t v___x_2706_; 
v___x_2705_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__1);
v___x_2706_ = lean_int_dec_eq(v_k_2700_, v___x_2705_);
if (v___x_2706_ == 0)
{
if (lean_obj_tag(v_p_2702_) == 0)
{
lean_object* v___x_2707_; 
v___x_2707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2707_, 0, v_k_2700_);
lean_ctor_set(v___x_2707_, 1, v_x_2701_);
return v___x_2707_;
}
else
{
lean_object* v_k_2708_; lean_object* v_v_2709_; lean_object* v_p_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; uint8_t v___x_2713_; 
v_k_2708_ = lean_ctor_get(v_p_2702_, 0);
lean_inc(v_k_2708_);
v_v_2709_ = lean_ctor_get(v_p_2702_, 1);
lean_inc(v_v_2709_);
v_p_2710_ = lean_ctor_get(v_p_2702_, 2);
lean_inc(v_p_2710_);
lean_dec_ref_known(v_p_2702_, 3);
v___x_2711_ = lean_nat_abs(v_k_2708_);
v___x_2712_ = lean_nat_abs(v_k_2700_);
v___x_2713_ = lean_nat_dec_lt(v___x_2711_, v___x_2712_);
lean_dec(v___x_2712_);
lean_dec(v___x_2711_);
if (v___x_2713_ == 0)
{
lean_dec(v_v_2709_);
lean_dec(v_k_2708_);
v_p_2702_ = v_p_2710_;
goto _start;
}
else
{
lean_dec(v_x_2701_);
lean_dec(v_k_2700_);
v_k_2700_ = v_k_2708_;
v_x_2701_ = v_v_2709_;
v_p_2702_ = v_p_2710_;
goto _start;
}
}
}
else
{
lean_object* v___x_2716_; 
lean_dec(v_p_2702_);
v___x_2716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2716_, 0, v_k_2700_);
lean_ctor_set(v___x_2716_, 1, v_x_2701_);
return v___x_2716_;
}
}
else
{
lean_object* v___x_2717_; 
lean_dec(v_p_2702_);
v___x_2717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2717_, 0, v_k_2700_);
lean_ctor_set(v___x_2717_, 1, v_x_2701_);
return v___x_2717_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_pickVarToElim_x3f(lean_object* v_p_2718_){
_start:
{
if (lean_obj_tag(v_p_2718_) == 0)
{
lean_object* v___x_2719_; 
v___x_2719_ = lean_box(0);
return v___x_2719_;
}
else
{
lean_object* v_k_2720_; lean_object* v_v_2721_; lean_object* v_p_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; 
v_k_2720_ = lean_ctor_get(v_p_2718_, 0);
lean_inc(v_k_2720_);
v_v_2721_ = lean_ctor_get(v_p_2718_, 1);
lean_inc(v_v_2721_);
v_p_2722_ = lean_ctor_get(v_p_2718_, 2);
lean_inc(v_p_2722_);
lean_dec_ref_known(v_p_2718_, 3);
v___x_2723_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go(v_k_2720_, v_v_2721_, v_p_2722_);
v___x_2724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2724_, 0, v___x_2723_);
return v___x_2724_;
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
