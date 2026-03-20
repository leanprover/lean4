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
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Linear_linearExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t l_Rat_instDecidableLe(lean_object*, lean_object*);
uint8_t l_Bool_toLBool(uint8_t);
uint8_t l_Rat_blt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* l_Int_gcd(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint64_t l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_shrink(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isInconsistent___redArg(lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Grind_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg___closed__1;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Linear_setTermStructId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "expression in two different structure in linarith module"};
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_setTermStructId___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Linear_setTermStructId___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId___closed__1;
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2___redArg(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_addOcc___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_addOcc___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_addOcc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_addOcc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v_one_x3f_61_);
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
lean_dec_ref(v_ringId_x3f_106_);
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
lean_dec_ref(v___x_151_);
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
lean_dec_ref(v_orderedRingInst_x3f_167_);
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
lean_dec_ref(v_isLinearInst_x3f_215_);
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
lean_dec_ref(v_noNatDivInst_x3f_265_);
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
lean_object* v_k_x27_305_; uint8_t v___x_306_; 
v_k_x27_305_ = lean_array_fget_borrowed(v_keys_298_, v_i_300_);
v___x_306_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_k_301_, v_k_x27_305_);
if (v___x_306_ == 0)
{
lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_307_ = lean_unsigned_to_nat(1u);
v___x_308_ = lean_nat_add(v_i_300_, v___x_307_);
lean_dec(v_i_300_);
v_i_300_ = v___x_308_;
goto _start;
}
else
{
lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_310_ = lean_array_fget_borrowed(v_vals_299_, v_i_300_);
lean_dec(v_i_300_);
lean_inc(v___x_310_);
v___x_311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_311_, 0, v___x_310_);
return v___x_311_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_312_, lean_object* v_vals_313_, lean_object* v_i_314_, lean_object* v_k_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_312_, v_vals_313_, v_i_314_, v_k_315_);
lean_dec_ref(v_k_315_);
lean_dec_ref(v_vals_313_);
lean_dec_ref(v_keys_312_);
return v_res_316_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_317_; size_t v___x_318_; size_t v___x_319_; 
v___x_317_ = ((size_t)5ULL);
v___x_318_ = ((size_t)1ULL);
v___x_319_ = lean_usize_shift_left(v___x_318_, v___x_317_);
return v___x_319_;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_320_; size_t v___x_321_; size_t v___x_322_; 
v___x_320_ = ((size_t)1ULL);
v___x_321_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg___closed__0);
v___x_322_ = lean_usize_sub(v___x_321_, v___x_320_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg(lean_object* v_x_323_, size_t v_x_324_, lean_object* v_x_325_){
_start:
{
if (lean_obj_tag(v_x_323_) == 0)
{
lean_object* v_es_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_347_; 
v_es_326_ = lean_ctor_get(v_x_323_, 0);
v_isSharedCheck_347_ = !lean_is_exclusive(v_x_323_);
if (v_isSharedCheck_347_ == 0)
{
v___x_328_ = v_x_323_;
v_isShared_329_ = v_isSharedCheck_347_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_es_326_);
lean_dec(v_x_323_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_347_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_330_; size_t v___x_331_; size_t v___x_332_; size_t v___x_333_; lean_object* v_j_334_; lean_object* v___x_335_; 
v___x_330_ = lean_box(2);
v___x_331_ = ((size_t)5ULL);
v___x_332_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg___closed__1);
v___x_333_ = lean_usize_land(v_x_324_, v___x_332_);
v_j_334_ = lean_usize_to_nat(v___x_333_);
v___x_335_ = lean_array_get(v___x_330_, v_es_326_, v_j_334_);
lean_dec(v_j_334_);
lean_dec_ref(v_es_326_);
switch(lean_obj_tag(v___x_335_))
{
case 0:
{
lean_object* v_key_336_; lean_object* v_val_337_; uint8_t v___x_338_; 
v_key_336_ = lean_ctor_get(v___x_335_, 0);
lean_inc(v_key_336_);
v_val_337_ = lean_ctor_get(v___x_335_, 1);
lean_inc(v_val_337_);
lean_dec_ref(v___x_335_);
v___x_338_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_325_, v_key_336_);
lean_dec(v_key_336_);
if (v___x_338_ == 0)
{
lean_object* v___x_339_; 
lean_dec(v_val_337_);
lean_del_object(v___x_328_);
v___x_339_ = lean_box(0);
return v___x_339_;
}
else
{
lean_object* v___x_341_; 
if (v_isShared_329_ == 0)
{
lean_ctor_set_tag(v___x_328_, 1);
lean_ctor_set(v___x_328_, 0, v_val_337_);
v___x_341_ = v___x_328_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v_val_337_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
}
case 1:
{
lean_object* v_node_343_; size_t v___x_344_; 
lean_del_object(v___x_328_);
v_node_343_ = lean_ctor_get(v___x_335_, 0);
lean_inc(v_node_343_);
lean_dec_ref(v___x_335_);
v___x_344_ = lean_usize_shift_right(v_x_324_, v___x_331_);
v_x_323_ = v_node_343_;
v_x_324_ = v___x_344_;
goto _start;
}
default: 
{
lean_object* v___x_346_; 
lean_del_object(v___x_328_);
v___x_346_ = lean_box(0);
return v___x_346_;
}
}
}
}
else
{
lean_object* v_ks_348_; lean_object* v_vs_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v_ks_348_ = lean_ctor_get(v_x_323_, 0);
lean_inc_ref(v_ks_348_);
v_vs_349_ = lean_ctor_get(v_x_323_, 1);
lean_inc_ref(v_vs_349_);
lean_dec_ref(v_x_323_);
v___x_350_ = lean_unsigned_to_nat(0u);
v___x_351_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_348_, v_vs_349_, v___x_350_, v_x_325_);
lean_dec_ref(v_vs_349_);
lean_dec_ref(v_ks_348_);
return v___x_351_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_352_, lean_object* v_x_353_, lean_object* v_x_354_){
_start:
{
size_t v_x_960__boxed_355_; lean_object* v_res_356_; 
v_x_960__boxed_355_ = lean_unbox_usize(v_x_353_);
lean_dec(v_x_353_);
v_res_356_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg(v_x_352_, v_x_960__boxed_355_, v_x_354_);
lean_dec_ref(v_x_354_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0___redArg(lean_object* v_x_357_, lean_object* v_x_358_){
_start:
{
uint64_t v___x_359_; size_t v___x_360_; lean_object* v___x_361_; 
v___x_359_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_358_);
v___x_360_ = lean_uint64_to_usize(v___x_359_);
v___x_361_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg(v_x_357_, v___x_360_, v_x_358_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0___redArg___boxed(lean_object* v_x_362_, lean_object* v_x_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0___redArg(v_x_362_, v_x_363_);
lean_dec_ref(v_x_363_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg(lean_object* v_e_365_, lean_object* v_a_366_, lean_object* v_a_367_){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_366_, v_a_367_);
if (lean_obj_tag(v___x_369_) == 0)
{
lean_object* v_a_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_379_; 
v_a_370_ = lean_ctor_get(v___x_369_, 0);
v_isSharedCheck_379_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_379_ == 0)
{
v___x_372_ = v___x_369_;
v_isShared_373_ = v_isSharedCheck_379_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_a_370_);
lean_dec(v___x_369_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_379_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v_exprToStructId_374_; lean_object* v___x_375_; lean_object* v___x_377_; 
v_exprToStructId_374_ = lean_ctor_get(v_a_370_, 2);
lean_inc_ref(v_exprToStructId_374_);
lean_dec(v_a_370_);
v___x_375_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0___redArg(v_exprToStructId_374_, v_e_365_);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 0, v___x_375_);
v___x_377_ = v___x_372_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v___x_375_);
v___x_377_ = v_reuseFailAlloc_378_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
return v___x_377_;
}
}
}
else
{
lean_object* v_a_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_387_; 
v_a_380_ = lean_ctor_get(v___x_369_, 0);
v_isSharedCheck_387_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_387_ == 0)
{
v___x_382_ = v___x_369_;
v_isShared_383_ = v_isSharedCheck_387_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_a_380_);
lean_dec(v___x_369_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_387_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v___x_385_; 
if (v_isShared_383_ == 0)
{
v___x_385_ = v___x_382_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v_a_380_);
v___x_385_ = v_reuseFailAlloc_386_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
return v___x_385_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg___boxed(lean_object* v_e_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg(v_e_388_, v_a_389_, v_a_390_);
lean_dec_ref(v_a_390_);
lean_dec(v_a_389_);
lean_dec_ref(v_e_388_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f(lean_object* v_e_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_){
_start:
{
lean_object* v___x_405_; 
v___x_405_ = l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg(v_e_393_, v_a_394_, v_a_402_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___boxed(lean_object* v_e_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f(v_e_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_);
lean_dec(v_a_416_);
lean_dec_ref(v_a_415_);
lean_dec(v_a_414_);
lean_dec_ref(v_a_413_);
lean_dec(v_a_412_);
lean_dec_ref(v_a_411_);
lean_dec(v_a_410_);
lean_dec_ref(v_a_409_);
lean_dec(v_a_408_);
lean_dec(v_a_407_);
lean_dec_ref(v_e_406_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0(lean_object* v_00_u03b2_419_, lean_object* v_x_420_, lean_object* v_x_421_){
_start:
{
lean_object* v___x_422_; 
v___x_422_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0___redArg(v_x_420_, v_x_421_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0___boxed(lean_object* v_00_u03b2_423_, lean_object* v_x_424_, lean_object* v_x_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0(v_00_u03b2_423_, v_x_424_, v_x_425_);
lean_dec_ref(v_x_425_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0(lean_object* v_00_u03b2_427_, lean_object* v_x_428_, size_t v_x_429_, lean_object* v_x_430_){
_start:
{
lean_object* v___x_431_; 
v___x_431_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg(v_x_428_, v_x_429_, v_x_430_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_432_, lean_object* v_x_433_, lean_object* v_x_434_, lean_object* v_x_435_){
_start:
{
size_t v_x_1125__boxed_436_; lean_object* v_res_437_; 
v_x_1125__boxed_436_ = lean_unbox_usize(v_x_434_);
lean_dec(v_x_434_);
v_res_437_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0(v_00_u03b2_432_, v_x_433_, v_x_1125__boxed_436_, v_x_435_);
lean_dec_ref(v_x_435_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_438_, lean_object* v_keys_439_, lean_object* v_vals_440_, lean_object* v_heq_441_, lean_object* v_i_442_, lean_object* v_k_443_){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_439_, v_vals_440_, v_i_442_, v_k_443_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_445_, lean_object* v_keys_446_, lean_object* v_vals_447_, lean_object* v_heq_448_, lean_object* v_i_449_, lean_object* v_k_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_445_, v_keys_446_, v_vals_447_, v_heq_448_, v_i_449_, v_k_450_);
lean_dec_ref(v_k_450_);
lean_dec_ref(v_vals_447_);
lean_dec_ref(v_keys_446_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_452_, lean_object* v_x_453_, lean_object* v_x_454_, lean_object* v_x_455_){
_start:
{
lean_object* v_ks_456_; lean_object* v_vs_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_481_; 
v_ks_456_ = lean_ctor_get(v_x_452_, 0);
v_vs_457_ = lean_ctor_get(v_x_452_, 1);
v_isSharedCheck_481_ = !lean_is_exclusive(v_x_452_);
if (v_isSharedCheck_481_ == 0)
{
v___x_459_ = v_x_452_;
v_isShared_460_ = v_isSharedCheck_481_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_vs_457_);
lean_inc(v_ks_456_);
lean_dec(v_x_452_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_481_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_461_; uint8_t v___x_462_; 
v___x_461_ = lean_array_get_size(v_ks_456_);
v___x_462_ = lean_nat_dec_lt(v_x_453_, v___x_461_);
if (v___x_462_ == 0)
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_466_; 
lean_dec(v_x_453_);
v___x_463_ = lean_array_push(v_ks_456_, v_x_454_);
v___x_464_ = lean_array_push(v_vs_457_, v_x_455_);
if (v_isShared_460_ == 0)
{
lean_ctor_set(v___x_459_, 1, v___x_464_);
lean_ctor_set(v___x_459_, 0, v___x_463_);
v___x_466_ = v___x_459_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v___x_463_);
lean_ctor_set(v_reuseFailAlloc_467_, 1, v___x_464_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
else
{
lean_object* v_k_x27_468_; uint8_t v___x_469_; 
v_k_x27_468_ = lean_array_fget_borrowed(v_ks_456_, v_x_453_);
v___x_469_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_454_, v_k_x27_468_);
if (v___x_469_ == 0)
{
lean_object* v___x_471_; 
if (v_isShared_460_ == 0)
{
v___x_471_ = v___x_459_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_ks_456_);
lean_ctor_set(v_reuseFailAlloc_475_, 1, v_vs_457_);
v___x_471_ = v_reuseFailAlloc_475_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_472_ = lean_unsigned_to_nat(1u);
v___x_473_ = lean_nat_add(v_x_453_, v___x_472_);
lean_dec(v_x_453_);
v_x_452_ = v___x_471_;
v_x_453_ = v___x_473_;
goto _start;
}
}
else
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_479_; 
v___x_476_ = lean_array_fset(v_ks_456_, v_x_453_, v_x_454_);
v___x_477_ = lean_array_fset(v_vs_457_, v_x_453_, v_x_455_);
lean_dec(v_x_453_);
if (v_isShared_460_ == 0)
{
lean_ctor_set(v___x_459_, 1, v___x_477_);
lean_ctor_set(v___x_459_, 0, v___x_476_);
v___x_479_ = v___x_459_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v___x_476_);
lean_ctor_set(v_reuseFailAlloc_480_, 1, v___x_477_);
v___x_479_ = v_reuseFailAlloc_480_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
return v___x_479_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1___redArg(lean_object* v_n_482_, lean_object* v_k_483_, lean_object* v_v_484_){
_start:
{
lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_485_ = lean_unsigned_to_nat(0u);
v___x_486_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1_spec__2___redArg(v_n_482_, v___x_485_, v_k_483_, v_v_484_);
return v___x_486_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_487_; 
v___x_487_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg(lean_object* v_x_488_, size_t v_x_489_, size_t v_x_490_, lean_object* v_x_491_, lean_object* v_x_492_){
_start:
{
if (lean_obj_tag(v_x_488_) == 0)
{
lean_object* v_es_493_; size_t v___x_494_; size_t v___x_495_; size_t v___x_496_; size_t v___x_497_; lean_object* v_j_498_; lean_object* v___x_499_; uint8_t v___x_500_; 
v_es_493_ = lean_ctor_get(v_x_488_, 0);
v___x_494_ = ((size_t)5ULL);
v___x_495_ = ((size_t)1ULL);
v___x_496_ = lean_usize_once(&l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f_spec__0_spec__0___redArg___closed__1);
v___x_497_ = lean_usize_land(v_x_489_, v___x_496_);
v_j_498_ = lean_usize_to_nat(v___x_497_);
v___x_499_ = lean_array_get_size(v_es_493_);
v___x_500_ = lean_nat_dec_lt(v_j_498_, v___x_499_);
if (v___x_500_ == 0)
{
lean_dec(v_j_498_);
lean_dec(v_x_492_);
lean_dec_ref(v_x_491_);
return v_x_488_;
}
else
{
lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_537_; 
lean_inc_ref(v_es_493_);
v_isSharedCheck_537_ = !lean_is_exclusive(v_x_488_);
if (v_isSharedCheck_537_ == 0)
{
lean_object* v_unused_538_; 
v_unused_538_ = lean_ctor_get(v_x_488_, 0);
lean_dec(v_unused_538_);
v___x_502_ = v_x_488_;
v_isShared_503_ = v_isSharedCheck_537_;
goto v_resetjp_501_;
}
else
{
lean_dec(v_x_488_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_537_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v_v_504_; lean_object* v___x_505_; lean_object* v_xs_x27_506_; lean_object* v___y_508_; 
v_v_504_ = lean_array_fget(v_es_493_, v_j_498_);
v___x_505_ = lean_box(0);
v_xs_x27_506_ = lean_array_fset(v_es_493_, v_j_498_, v___x_505_);
switch(lean_obj_tag(v_v_504_))
{
case 0:
{
lean_object* v_key_513_; lean_object* v_val_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_524_; 
v_key_513_ = lean_ctor_get(v_v_504_, 0);
v_val_514_ = lean_ctor_get(v_v_504_, 1);
v_isSharedCheck_524_ = !lean_is_exclusive(v_v_504_);
if (v_isSharedCheck_524_ == 0)
{
v___x_516_ = v_v_504_;
v_isShared_517_ = v_isSharedCheck_524_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_val_514_);
lean_inc(v_key_513_);
lean_dec(v_v_504_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_524_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
uint8_t v___x_518_; 
v___x_518_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_491_, v_key_513_);
if (v___x_518_ == 0)
{
lean_object* v___x_519_; lean_object* v___x_520_; 
lean_del_object(v___x_516_);
v___x_519_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_513_, v_val_514_, v_x_491_, v_x_492_);
v___x_520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_520_, 0, v___x_519_);
v___y_508_ = v___x_520_;
goto v___jp_507_;
}
else
{
lean_object* v___x_522_; 
lean_dec(v_val_514_);
lean_dec(v_key_513_);
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 1, v_x_492_);
lean_ctor_set(v___x_516_, 0, v_x_491_);
v___x_522_ = v___x_516_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v_x_491_);
lean_ctor_set(v_reuseFailAlloc_523_, 1, v_x_492_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
v___y_508_ = v___x_522_;
goto v___jp_507_;
}
}
}
}
case 1:
{
lean_object* v_node_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_535_; 
v_node_525_ = lean_ctor_get(v_v_504_, 0);
v_isSharedCheck_535_ = !lean_is_exclusive(v_v_504_);
if (v_isSharedCheck_535_ == 0)
{
v___x_527_ = v_v_504_;
v_isShared_528_ = v_isSharedCheck_535_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_node_525_);
lean_dec(v_v_504_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_535_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
size_t v___x_529_; size_t v___x_530_; lean_object* v___x_531_; lean_object* v___x_533_; 
v___x_529_ = lean_usize_shift_right(v_x_489_, v___x_494_);
v___x_530_ = lean_usize_add(v_x_490_, v___x_495_);
v___x_531_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg(v_node_525_, v___x_529_, v___x_530_, v_x_491_, v_x_492_);
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 0, v___x_531_);
v___x_533_ = v___x_527_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v___x_531_);
v___x_533_ = v_reuseFailAlloc_534_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
v___y_508_ = v___x_533_;
goto v___jp_507_;
}
}
}
default: 
{
lean_object* v___x_536_; 
v___x_536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_536_, 0, v_x_491_);
lean_ctor_set(v___x_536_, 1, v_x_492_);
v___y_508_ = v___x_536_;
goto v___jp_507_;
}
}
v___jp_507_:
{
lean_object* v___x_509_; lean_object* v___x_511_; 
v___x_509_ = lean_array_fset(v_xs_x27_506_, v_j_498_, v___y_508_);
lean_dec(v_j_498_);
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 0, v___x_509_);
v___x_511_ = v___x_502_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v___x_509_);
v___x_511_ = v_reuseFailAlloc_512_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
return v___x_511_;
}
}
}
}
}
else
{
lean_object* v_ks_539_; lean_object* v_vs_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_560_; 
v_ks_539_ = lean_ctor_get(v_x_488_, 0);
v_vs_540_ = lean_ctor_get(v_x_488_, 1);
v_isSharedCheck_560_ = !lean_is_exclusive(v_x_488_);
if (v_isSharedCheck_560_ == 0)
{
v___x_542_ = v_x_488_;
v_isShared_543_ = v_isSharedCheck_560_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_vs_540_);
lean_inc(v_ks_539_);
lean_dec(v_x_488_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_560_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_545_; 
if (v_isShared_543_ == 0)
{
v___x_545_ = v___x_542_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_ks_539_);
lean_ctor_set(v_reuseFailAlloc_559_, 1, v_vs_540_);
v___x_545_ = v_reuseFailAlloc_559_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
lean_object* v_newNode_546_; uint8_t v___y_548_; size_t v___x_554_; uint8_t v___x_555_; 
v_newNode_546_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1___redArg(v___x_545_, v_x_491_, v_x_492_);
v___x_554_ = ((size_t)7ULL);
v___x_555_ = lean_usize_dec_le(v___x_554_, v_x_490_);
if (v___x_555_ == 0)
{
lean_object* v___x_556_; lean_object* v___x_557_; uint8_t v___x_558_; 
v___x_556_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_546_);
v___x_557_ = lean_unsigned_to_nat(4u);
v___x_558_ = lean_nat_dec_lt(v___x_556_, v___x_557_);
lean_dec(v___x_556_);
v___y_548_ = v___x_558_;
goto v___jp_547_;
}
else
{
v___y_548_ = v___x_555_;
goto v___jp_547_;
}
v___jp_547_:
{
if (v___y_548_ == 0)
{
lean_object* v_ks_549_; lean_object* v_vs_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
v_ks_549_ = lean_ctor_get(v_newNode_546_, 0);
lean_inc_ref(v_ks_549_);
v_vs_550_ = lean_ctor_get(v_newNode_546_, 1);
lean_inc_ref(v_vs_550_);
lean_dec_ref(v_newNode_546_);
v___x_551_ = lean_unsigned_to_nat(0u);
v___x_552_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg___closed__0);
v___x_553_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2___redArg(v_x_490_, v_ks_549_, v_vs_550_, v___x_551_, v___x_552_);
lean_dec_ref(v_vs_550_);
lean_dec_ref(v_ks_549_);
return v___x_553_;
}
else
{
return v_newNode_546_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2___redArg(size_t v_depth_561_, lean_object* v_keys_562_, lean_object* v_vals_563_, lean_object* v_i_564_, lean_object* v_entries_565_){
_start:
{
lean_object* v___x_566_; uint8_t v___x_567_; 
v___x_566_ = lean_array_get_size(v_keys_562_);
v___x_567_ = lean_nat_dec_lt(v_i_564_, v___x_566_);
if (v___x_567_ == 0)
{
lean_dec(v_i_564_);
return v_entries_565_;
}
else
{
lean_object* v_k_568_; lean_object* v_v_569_; uint64_t v___x_570_; size_t v_h_571_; size_t v___x_572_; lean_object* v___x_573_; size_t v___x_574_; size_t v___x_575_; size_t v___x_576_; size_t v_h_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
v_k_568_ = lean_array_fget_borrowed(v_keys_562_, v_i_564_);
v_v_569_ = lean_array_fget_borrowed(v_vals_563_, v_i_564_);
v___x_570_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_568_);
v_h_571_ = lean_uint64_to_usize(v___x_570_);
v___x_572_ = ((size_t)5ULL);
v___x_573_ = lean_unsigned_to_nat(1u);
v___x_574_ = ((size_t)1ULL);
v___x_575_ = lean_usize_sub(v_depth_561_, v___x_574_);
v___x_576_ = lean_usize_mul(v___x_572_, v___x_575_);
v_h_577_ = lean_usize_shift_right(v_h_571_, v___x_576_);
v___x_578_ = lean_nat_add(v_i_564_, v___x_573_);
lean_dec(v_i_564_);
lean_inc(v_v_569_);
lean_inc(v_k_568_);
v___x_579_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg(v_entries_565_, v_h_577_, v_depth_561_, v_k_568_, v_v_569_);
v_i_564_ = v___x_578_;
v_entries_565_ = v___x_579_;
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
size_t v_x_8320__boxed_593_; size_t v_x_8321__boxed_594_; lean_object* v_res_595_; 
v_x_8320__boxed_593_ = lean_unbox_usize(v_x_589_);
lean_dec(v_x_589_);
v_x_8321__boxed_594_ = lean_unbox_usize(v_x_590_);
lean_dec(v_x_590_);
v_res_595_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg(v_x_588_, v_x_8320__boxed_593_, v_x_8321__boxed_594_, v_x_591_, v_x_592_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0___redArg(lean_object* v_x_596_, lean_object* v_x_597_, lean_object* v_x_598_){
_start:
{
uint64_t v___x_599_; size_t v___x_600_; size_t v___x_601_; lean_object* v___x_602_; 
v___x_599_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_597_);
v___x_600_ = lean_uint64_to_usize(v___x_599_);
v___x_601_ = ((size_t)1ULL);
v___x_602_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg(v_x_596_, v___x_600_, v___x_601_, v_x_597_, v_x_598_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId___lam__0(lean_object* v_e_603_, lean_object* v_a_604_, lean_object* v_s_605_){
_start:
{
lean_object* v_structs_606_; lean_object* v_typeIdOf_607_; lean_object* v_exprToStructId_608_; lean_object* v_exprToStructIdEntries_609_; lean_object* v_forbiddenNatModules_610_; lean_object* v_natStructs_611_; lean_object* v_natTypeIdOf_612_; lean_object* v_exprToNatStructId_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_623_; 
v_structs_606_ = lean_ctor_get(v_s_605_, 0);
v_typeIdOf_607_ = lean_ctor_get(v_s_605_, 1);
v_exprToStructId_608_ = lean_ctor_get(v_s_605_, 2);
v_exprToStructIdEntries_609_ = lean_ctor_get(v_s_605_, 3);
v_forbiddenNatModules_610_ = lean_ctor_get(v_s_605_, 4);
v_natStructs_611_ = lean_ctor_get(v_s_605_, 5);
v_natTypeIdOf_612_ = lean_ctor_get(v_s_605_, 6);
v_exprToNatStructId_613_ = lean_ctor_get(v_s_605_, 7);
v_isSharedCheck_623_ = !lean_is_exclusive(v_s_605_);
if (v_isSharedCheck_623_ == 0)
{
v___x_615_ = v_s_605_;
v_isShared_616_ = v_isSharedCheck_623_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_exprToNatStructId_613_);
lean_inc(v_natTypeIdOf_612_);
lean_inc(v_natStructs_611_);
lean_inc(v_forbiddenNatModules_610_);
lean_inc(v_exprToStructIdEntries_609_);
lean_inc(v_exprToStructId_608_);
lean_inc(v_typeIdOf_607_);
lean_inc(v_structs_606_);
lean_dec(v_s_605_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_623_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_621_; 
lean_inc(v_a_604_);
lean_inc_ref(v_e_603_);
v___x_617_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0___redArg(v_exprToStructId_608_, v_e_603_, v_a_604_);
v___x_618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_618_, 0, v_e_603_);
lean_ctor_set(v___x_618_, 1, v_a_604_);
v___x_619_ = l_Lean_PersistentArray_push___redArg(v_exprToStructIdEntries_609_, v___x_618_);
if (v_isShared_616_ == 0)
{
lean_ctor_set(v___x_615_, 3, v___x_619_);
lean_ctor_set(v___x_615_, 2, v___x_617_);
v___x_621_ = v___x_615_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_structs_606_);
lean_ctor_set(v_reuseFailAlloc_622_, 1, v_typeIdOf_607_);
lean_ctor_set(v_reuseFailAlloc_622_, 2, v___x_617_);
lean_ctor_set(v_reuseFailAlloc_622_, 3, v___x_619_);
lean_ctor_set(v_reuseFailAlloc_622_, 4, v_forbiddenNatModules_610_);
lean_ctor_set(v_reuseFailAlloc_622_, 5, v_natStructs_611_);
lean_ctor_set(v_reuseFailAlloc_622_, 6, v_natTypeIdOf_612_);
lean_ctor_set(v_reuseFailAlloc_622_, 7, v_exprToNatStructId_613_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_setTermStructId___closed__1(void){
_start:
{
lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_625_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_setTermStructId___closed__0));
v___x_626_ = l_Lean_stringToMessageData(v___x_625_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId(lean_object* v_e_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_){
_start:
{
lean_object* v___x_643_; 
v___x_643_ = l_Lean_Meta_Grind_Arith_Linear_getTermStructId_x3f___redArg(v_e_627_, v_a_629_, v_a_637_);
if (lean_obj_tag(v___x_643_) == 0)
{
lean_object* v_a_644_; 
v_a_644_ = lean_ctor_get(v___x_643_, 0);
lean_inc(v_a_644_);
lean_dec_ref(v___x_643_);
if (lean_obj_tag(v_a_644_) == 1)
{
lean_object* v_val_645_; uint8_t v___x_646_; 
v_val_645_ = lean_ctor_get(v_a_644_, 0);
lean_inc(v_val_645_);
lean_dec_ref(v_a_644_);
v___x_646_ = lean_nat_dec_eq(v_val_645_, v_a_628_);
lean_dec(v_a_628_);
lean_dec(v_val_645_);
if (v___x_646_ == 0)
{
lean_object* v___x_647_; 
v___x_647_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_631_);
if (lean_obj_tag(v___x_647_) == 0)
{
lean_object* v_a_648_; uint8_t v_verbose_649_; 
v_a_648_ = lean_ctor_get(v___x_647_, 0);
lean_inc(v_a_648_);
lean_dec_ref(v___x_647_);
v_verbose_649_ = lean_ctor_get_uint8(v_a_648_, sizeof(void*)*11 + 15);
lean_dec(v_a_648_);
if (v_verbose_649_ == 0)
{
lean_dec_ref(v_e_627_);
goto v___jp_640_;
}
else
{
lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_650_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_setTermStructId___closed__1, &l_Lean_Meta_Grind_Arith_Linear_setTermStructId___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_setTermStructId___closed__1);
v___x_651_ = l_Lean_indentExpr(v_e_627_);
v___x_652_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_652_, 0, v___x_650_);
lean_ctor_set(v___x_652_, 1, v___x_651_);
v___x_653_ = l_Lean_Meta_Grind_reportIssue(v___x_652_, v_a_630_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_);
if (lean_obj_tag(v___x_653_) == 0)
{
lean_dec_ref(v___x_653_);
goto v___jp_640_;
}
else
{
return v___x_653_;
}
}
}
else
{
lean_object* v_a_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_661_; 
lean_dec_ref(v_e_627_);
v_a_654_ = lean_ctor_get(v___x_647_, 0);
v_isSharedCheck_661_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_661_ == 0)
{
v___x_656_ = v___x_647_;
v_isShared_657_ = v_isSharedCheck_661_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_a_654_);
lean_dec(v___x_647_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_661_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v___x_659_; 
if (v_isShared_657_ == 0)
{
v___x_659_ = v___x_656_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_a_654_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
return v___x_659_;
}
}
}
}
else
{
lean_dec_ref(v_e_627_);
goto v___jp_640_;
}
}
else
{
lean_object* v___f_662_; lean_object* v___x_663_; lean_object* v___x_664_; 
lean_dec(v_a_644_);
v___f_662_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_setTermStructId___lam__0), 3, 2);
lean_closure_set(v___f_662_, 0, v_e_627_);
lean_closure_set(v___f_662_, 1, v_a_628_);
v___x_663_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_664_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_663_, v___f_662_, v_a_629_);
return v___x_664_;
}
}
else
{
lean_object* v_a_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_672_; 
lean_dec(v_a_628_);
lean_dec_ref(v_e_627_);
v_a_665_ = lean_ctor_get(v___x_643_, 0);
v_isSharedCheck_672_ = !lean_is_exclusive(v___x_643_);
if (v_isSharedCheck_672_ == 0)
{
v___x_667_ = v___x_643_;
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_a_665_);
lean_dec(v___x_643_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_670_; 
if (v_isShared_668_ == 0)
{
v___x_670_ = v___x_667_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_a_665_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
}
v___jp_640_:
{
lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_641_ = lean_box(0);
v___x_642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_642_, 0, v___x_641_);
return v___x_642_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_setTermStructId___boxed(lean_object* v_e_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_){
_start:
{
lean_object* v_res_686_; 
v_res_686_ = l_Lean_Meta_Grind_Arith_Linear_setTermStructId(v_e_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_, v_a_682_, v_a_683_, v_a_684_);
lean_dec(v_a_684_);
lean_dec_ref(v_a_683_);
lean_dec(v_a_682_);
lean_dec_ref(v_a_681_);
lean_dec(v_a_680_);
lean_dec_ref(v_a_679_);
lean_dec(v_a_678_);
lean_dec_ref(v_a_677_);
lean_dec(v_a_676_);
lean_dec(v_a_675_);
return v_res_686_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0(lean_object* v_00_u03b2_687_, lean_object* v_x_688_, lean_object* v_x_689_, lean_object* v_x_690_){
_start:
{
lean_object* v___x_691_; 
v___x_691_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0___redArg(v_x_688_, v_x_689_, v_x_690_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0(lean_object* v_00_u03b2_692_, lean_object* v_x_693_, size_t v_x_694_, size_t v_x_695_, lean_object* v_x_696_, lean_object* v_x_697_){
_start:
{
lean_object* v___x_698_; 
v___x_698_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___redArg(v_x_693_, v_x_694_, v_x_695_, v_x_696_, v_x_697_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0___boxed(lean_object* v_00_u03b2_699_, lean_object* v_x_700_, lean_object* v_x_701_, lean_object* v_x_702_, lean_object* v_x_703_, lean_object* v_x_704_){
_start:
{
size_t v_x_8631__boxed_705_; size_t v_x_8632__boxed_706_; lean_object* v_res_707_; 
v_x_8631__boxed_705_ = lean_unbox_usize(v_x_701_);
lean_dec(v_x_701_);
v_x_8632__boxed_706_ = lean_unbox_usize(v_x_702_);
lean_dec(v_x_702_);
v_res_707_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0(v_00_u03b2_699_, v_x_700_, v_x_8631__boxed_705_, v_x_8632__boxed_706_, v_x_703_, v_x_704_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_708_, lean_object* v_n_709_, lean_object* v_k_710_, lean_object* v_v_711_){
_start:
{
lean_object* v___x_712_; 
v___x_712_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1___redArg(v_n_709_, v_k_710_, v_v_711_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_713_, size_t v_depth_714_, lean_object* v_keys_715_, lean_object* v_vals_716_, lean_object* v_heq_717_, lean_object* v_i_718_, lean_object* v_entries_719_){
_start:
{
lean_object* v___x_720_; 
v___x_720_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2___redArg(v_depth_714_, v_keys_715_, v_vals_716_, v_i_718_, v_entries_719_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_721_, lean_object* v_depth_722_, lean_object* v_keys_723_, lean_object* v_vals_724_, lean_object* v_heq_725_, lean_object* v_i_726_, lean_object* v_entries_727_){
_start:
{
size_t v_depth_boxed_728_; lean_object* v_res_729_; 
v_depth_boxed_728_ = lean_unbox_usize(v_depth_722_);
lean_dec(v_depth_722_);
v_res_729_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__2(v_00_u03b2_721_, v_depth_boxed_728_, v_keys_723_, v_vals_724_, v_heq_725_, v_i_726_, v_entries_727_);
lean_dec_ref(v_vals_724_);
lean_dec_ref(v_keys_723_);
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_730_, lean_object* v_x_731_, lean_object* v_x_732_, lean_object* v_x_733_, lean_object* v_x_734_){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermStructId_spec__0_spec__0_spec__1_spec__2___redArg(v_x_731_, v_x_732_, v_x_733_, v_x_734_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0_spec__0(lean_object* v_msgData_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_){
_start:
{
lean_object* v___x_742_; lean_object* v_env_743_; lean_object* v___x_744_; lean_object* v_mctx_745_; lean_object* v_lctx_746_; lean_object* v_options_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_742_ = lean_st_ref_get(v___y_740_);
v_env_743_ = lean_ctor_get(v___x_742_, 0);
lean_inc_ref(v_env_743_);
lean_dec(v___x_742_);
v___x_744_ = lean_st_ref_get(v___y_738_);
v_mctx_745_ = lean_ctor_get(v___x_744_, 0);
lean_inc_ref(v_mctx_745_);
lean_dec(v___x_744_);
v_lctx_746_ = lean_ctor_get(v___y_737_, 2);
v_options_747_ = lean_ctor_get(v___y_739_, 2);
lean_inc_ref(v_options_747_);
lean_inc_ref(v_lctx_746_);
v___x_748_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_748_, 0, v_env_743_);
lean_ctor_set(v___x_748_, 1, v_mctx_745_);
lean_ctor_set(v___x_748_, 2, v_lctx_746_);
lean_ctor_set(v___x_748_, 3, v_options_747_);
v___x_749_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_749_, 0, v___x_748_);
lean_ctor_set(v___x_749_, 1, v_msgData_736_);
v___x_750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_750_, 0, v___x_749_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0_spec__0___boxed(lean_object* v_msgData_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0_spec__0(v_msgData_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_);
lean_dec(v___y_755_);
lean_dec_ref(v___y_754_);
lean_dec(v___y_753_);
lean_dec_ref(v___y_752_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(lean_object* v_msg_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_){
_start:
{
lean_object* v_ref_764_; lean_object* v___x_765_; lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_774_; 
v_ref_764_ = lean_ctor_get(v___y_761_, 5);
v___x_765_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0_spec__0(v_msg_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_);
v_a_766_ = lean_ctor_get(v___x_765_, 0);
v_isSharedCheck_774_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_774_ == 0)
{
v___x_768_ = v___x_765_;
v_isShared_769_ = v_isSharedCheck_774_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_dec(v___x_765_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_774_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_770_; lean_object* v___x_772_; 
lean_inc(v_ref_764_);
v___x_770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_770_, 0, v_ref_764_);
lean_ctor_set(v___x_770_, 1, v_a_766_);
if (v_isShared_769_ == 0)
{
lean_ctor_set_tag(v___x_768_, 1);
lean_ctor_set(v___x_768_, 0, v___x_770_);
v___x_772_ = v___x_768_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v___x_770_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg___boxed(lean_object* v_msg_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v_msg_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_);
lean_dec(v___y_779_);
lean_dec_ref(v___y_778_);
lean_dec(v___y_777_);
lean_dec_ref(v___y_776_);
return v_res_781_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___closed__1(void){
_start:
{
lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_783_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___closed__0));
v___x_784_ = l_Lean_stringToMessageData(v___x_783_);
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst(lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_){
_start:
{
lean_object* v___x_797_; 
v___x_797_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_785_, v_a_786_, v_a_787_, v_a_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_, v_a_794_, v_a_795_);
if (lean_obj_tag(v___x_797_) == 0)
{
lean_object* v_a_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_809_; 
v_a_798_ = lean_ctor_get(v___x_797_, 0);
v_isSharedCheck_809_ = !lean_is_exclusive(v___x_797_);
if (v_isSharedCheck_809_ == 0)
{
v___x_800_ = v___x_797_;
v_isShared_801_ = v_isSharedCheck_809_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_a_798_);
lean_dec(v___x_797_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_809_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v_noNatDivInst_x3f_802_; 
v_noNatDivInst_x3f_802_ = lean_ctor_get(v_a_798_, 11);
lean_inc(v_noNatDivInst_x3f_802_);
lean_dec(v_a_798_);
if (lean_obj_tag(v_noNatDivInst_x3f_802_) == 1)
{
lean_object* v_val_803_; lean_object* v___x_805_; 
v_val_803_ = lean_ctor_get(v_noNatDivInst_x3f_802_, 0);
lean_inc(v_val_803_);
lean_dec_ref(v_noNatDivInst_x3f_802_);
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 0, v_val_803_);
v___x_805_ = v___x_800_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v_val_803_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
return v___x_805_;
}
}
else
{
lean_object* v___x_807_; lean_object* v___x_808_; 
lean_dec(v_noNatDivInst_x3f_802_);
lean_del_object(v___x_800_);
v___x_807_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___closed__1);
v___x_808_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_807_, v_a_792_, v_a_793_, v_a_794_, v_a_795_);
return v___x_808_;
}
}
}
else
{
lean_object* v_a_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_817_; 
v_a_810_ = lean_ctor_get(v___x_797_, 0);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_797_);
if (v_isSharedCheck_817_ == 0)
{
v___x_812_ = v___x_797_;
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_a_810_);
lean_dec(v___x_797_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_815_; 
if (v_isShared_813_ == 0)
{
v___x_815_ = v___x_812_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_a_810_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst___boxed(lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l_Lean_Meta_Grind_Arith_Linear_getNoNatDivInst(v_a_818_, v_a_819_, v_a_820_, v_a_821_, v_a_822_, v_a_823_, v_a_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_);
lean_dec(v_a_828_);
lean_dec_ref(v_a_827_);
lean_dec(v_a_826_);
lean_dec_ref(v_a_825_);
lean_dec(v_a_824_);
lean_dec_ref(v_a_823_);
lean_dec(v_a_822_);
lean_dec_ref(v_a_821_);
lean_dec(v_a_820_);
lean_dec(v_a_819_);
lean_dec(v_a_818_);
return v_res_830_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0(lean_object* v_00_u03b1_831_, lean_object* v_msg_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_){
_start:
{
lean_object* v___x_845_; 
v___x_845_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v_msg_832_, v___y_840_, v___y_841_, v___y_842_, v___y_843_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___boxed(lean_object* v_00_u03b1_846_, lean_object* v_msg_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_){
_start:
{
lean_object* v_res_860_; 
v_res_860_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0(v_00_u03b1_846_, v_msg_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_);
lean_dec(v___y_858_);
lean_dec_ref(v___y_857_);
lean_dec(v___y_856_);
lean_dec_ref(v___y_855_);
lean_dec(v___y_854_);
lean_dec_ref(v___y_853_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
lean_dec(v___y_850_);
lean_dec(v___y_849_);
lean_dec(v___y_848_);
return v_res_860_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLEInst___closed__1(void){
_start:
{
lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_862_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLEInst___closed__0));
v___x_863_ = l_Lean_stringToMessageData(v___x_862_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLEInst(lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_){
_start:
{
lean_object* v___x_876_; 
v___x_876_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_864_, v_a_865_, v_a_866_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_);
if (lean_obj_tag(v___x_876_) == 0)
{
lean_object* v_a_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_888_; 
v_a_877_ = lean_ctor_get(v___x_876_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_888_ == 0)
{
v___x_879_ = v___x_876_;
v_isShared_880_ = v_isSharedCheck_888_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_a_877_);
lean_dec(v___x_876_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_888_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v_leInst_x3f_881_; 
v_leInst_x3f_881_ = lean_ctor_get(v_a_877_, 5);
lean_inc(v_leInst_x3f_881_);
lean_dec(v_a_877_);
if (lean_obj_tag(v_leInst_x3f_881_) == 1)
{
lean_object* v_val_882_; lean_object* v___x_884_; 
v_val_882_ = lean_ctor_get(v_leInst_x3f_881_, 0);
lean_inc(v_val_882_);
lean_dec_ref(v_leInst_x3f_881_);
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 0, v_val_882_);
v___x_884_ = v___x_879_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_val_882_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
else
{
lean_object* v___x_886_; lean_object* v___x_887_; 
lean_dec(v_leInst_x3f_881_);
lean_del_object(v___x_879_);
v___x_886_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLEInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLEInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLEInst___closed__1);
v___x_887_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_886_, v_a_871_, v_a_872_, v_a_873_, v_a_874_);
return v___x_887_;
}
}
}
else
{
lean_object* v_a_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_896_; 
v_a_889_ = lean_ctor_get(v___x_876_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_896_ == 0)
{
v___x_891_ = v___x_876_;
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_a_889_);
lean_dec(v___x_876_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_894_; 
if (v_isShared_892_ == 0)
{
v___x_894_ = v___x_891_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_a_889_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLEInst___boxed(lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l_Lean_Meta_Grind_Arith_Linear_getLEInst(v_a_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_);
lean_dec(v_a_907_);
lean_dec_ref(v_a_906_);
lean_dec(v_a_905_);
lean_dec_ref(v_a_904_);
lean_dec(v_a_903_);
lean_dec_ref(v_a_902_);
lean_dec(v_a_901_);
lean_dec_ref(v_a_900_);
lean_dec(v_a_899_);
lean_dec(v_a_898_);
lean_dec(v_a_897_);
return v_res_909_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLTInst___closed__1(void){
_start:
{
lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_911_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLTInst___closed__0));
v___x_912_ = l_Lean_stringToMessageData(v___x_911_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLTInst(lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_){
_start:
{
lean_object* v___x_925_; 
v___x_925_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_, v_a_918_, v_a_919_, v_a_920_, v_a_921_, v_a_922_, v_a_923_);
if (lean_obj_tag(v___x_925_) == 0)
{
lean_object* v_a_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_937_; 
v_a_926_ = lean_ctor_get(v___x_925_, 0);
v_isSharedCheck_937_ = !lean_is_exclusive(v___x_925_);
if (v_isSharedCheck_937_ == 0)
{
v___x_928_ = v___x_925_;
v_isShared_929_ = v_isSharedCheck_937_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_a_926_);
lean_dec(v___x_925_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_937_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v_ltInst_x3f_930_; 
v_ltInst_x3f_930_ = lean_ctor_get(v_a_926_, 6);
lean_inc(v_ltInst_x3f_930_);
lean_dec(v_a_926_);
if (lean_obj_tag(v_ltInst_x3f_930_) == 1)
{
lean_object* v_val_931_; lean_object* v___x_933_; 
v_val_931_ = lean_ctor_get(v_ltInst_x3f_930_, 0);
lean_inc(v_val_931_);
lean_dec_ref(v_ltInst_x3f_930_);
if (v_isShared_929_ == 0)
{
lean_ctor_set(v___x_928_, 0, v_val_931_);
v___x_933_ = v___x_928_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v_val_931_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
return v___x_933_;
}
}
else
{
lean_object* v___x_935_; lean_object* v___x_936_; 
lean_dec(v_ltInst_x3f_930_);
lean_del_object(v___x_928_);
v___x_935_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLTInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLTInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLTInst___closed__1);
v___x_936_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_935_, v_a_920_, v_a_921_, v_a_922_, v_a_923_);
return v___x_936_;
}
}
}
else
{
lean_object* v_a_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_945_; 
v_a_938_ = lean_ctor_get(v___x_925_, 0);
v_isSharedCheck_945_ = !lean_is_exclusive(v___x_925_);
if (v_isSharedCheck_945_ == 0)
{
v___x_940_ = v___x_925_;
v_isShared_941_ = v_isSharedCheck_945_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_a_938_);
lean_dec(v___x_925_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_945_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___x_943_; 
if (v_isShared_941_ == 0)
{
v___x_943_ = v___x_940_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v_a_938_);
v___x_943_ = v_reuseFailAlloc_944_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
return v___x_943_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLTInst___boxed(lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_Lean_Meta_Grind_Arith_Linear_getLTInst(v_a_946_, v_a_947_, v_a_948_, v_a_949_, v_a_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_);
lean_dec(v_a_956_);
lean_dec_ref(v_a_955_);
lean_dec(v_a_954_);
lean_dec_ref(v_a_953_);
lean_dec(v_a_952_);
lean_dec_ref(v_a_951_);
lean_dec(v_a_950_);
lean_dec_ref(v_a_949_);
lean_dec(v_a_948_);
lean_dec(v_a_947_);
lean_dec(v_a_946_);
return v_res_958_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___closed__1(void){
_start:
{
lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_960_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___closed__0));
v___x_961_ = l_Lean_stringToMessageData(v___x_960_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst(lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_){
_start:
{
lean_object* v___x_974_; 
v___x_974_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_962_, v_a_963_, v_a_964_, v_a_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
if (lean_obj_tag(v___x_974_) == 0)
{
lean_object* v_a_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_986_; 
v_a_975_ = lean_ctor_get(v___x_974_, 0);
v_isSharedCheck_986_ = !lean_is_exclusive(v___x_974_);
if (v_isSharedCheck_986_ == 0)
{
v___x_977_ = v___x_974_;
v_isShared_978_ = v_isSharedCheck_986_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_a_975_);
lean_dec(v___x_974_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_986_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v_lawfulOrderLTInst_x3f_979_; 
v_lawfulOrderLTInst_x3f_979_ = lean_ctor_get(v_a_975_, 7);
lean_inc(v_lawfulOrderLTInst_x3f_979_);
lean_dec(v_a_975_);
if (lean_obj_tag(v_lawfulOrderLTInst_x3f_979_) == 1)
{
lean_object* v_val_980_; lean_object* v___x_982_; 
v_val_980_ = lean_ctor_get(v_lawfulOrderLTInst_x3f_979_, 0);
lean_inc(v_val_980_);
lean_dec_ref(v_lawfulOrderLTInst_x3f_979_);
if (v_isShared_978_ == 0)
{
lean_ctor_set(v___x_977_, 0, v_val_980_);
v___x_982_ = v___x_977_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v_val_980_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
return v___x_982_;
}
}
else
{
lean_object* v___x_984_; lean_object* v___x_985_; 
lean_dec(v_lawfulOrderLTInst_x3f_979_);
lean_del_object(v___x_977_);
v___x_984_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___closed__1);
v___x_985_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_984_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
return v___x_985_;
}
}
}
else
{
lean_object* v_a_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_994_; 
v_a_987_ = lean_ctor_get(v___x_974_, 0);
v_isSharedCheck_994_ = !lean_is_exclusive(v___x_974_);
if (v_isSharedCheck_994_ == 0)
{
v___x_989_ = v___x_974_;
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_a_987_);
lean_dec(v___x_974_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___x_992_; 
if (v_isShared_990_ == 0)
{
v___x_992_ = v___x_989_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v_a_987_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
return v___x_992_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst___boxed(lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_){
_start:
{
lean_object* v_res_1007_; 
v_res_1007_ = l_Lean_Meta_Grind_Arith_Linear_getLawfulOrderLTInst(v_a_995_, v_a_996_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_, v_a_1004_, v_a_1005_);
lean_dec(v_a_1005_);
lean_dec_ref(v_a_1004_);
lean_dec(v_a_1003_);
lean_dec_ref(v_a_1002_);
lean_dec(v_a_1001_);
lean_dec_ref(v_a_1000_);
lean_dec(v_a_999_);
lean_dec_ref(v_a_998_);
lean_dec(v_a_997_);
lean_dec(v_a_996_);
lean_dec(v_a_995_);
return v_res_1007_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___closed__1(void){
_start:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1009_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___closed__0));
v___x_1010_ = l_Lean_stringToMessageData(v___x_1009_);
return v___x_1010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst(lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_){
_start:
{
lean_object* v___x_1023_; 
v___x_1023_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_);
if (lean_obj_tag(v___x_1023_) == 0)
{
lean_object* v_a_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1035_; 
v_a_1024_ = lean_ctor_get(v___x_1023_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1026_ = v___x_1023_;
v_isShared_1027_ = v_isSharedCheck_1035_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_a_1024_);
lean_dec(v___x_1023_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1035_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v_isPreorderInst_x3f_1028_; 
v_isPreorderInst_x3f_1028_ = lean_ctor_get(v_a_1024_, 8);
lean_inc(v_isPreorderInst_x3f_1028_);
lean_dec(v_a_1024_);
if (lean_obj_tag(v_isPreorderInst_x3f_1028_) == 1)
{
lean_object* v_val_1029_; lean_object* v___x_1031_; 
v_val_1029_ = lean_ctor_get(v_isPreorderInst_x3f_1028_, 0);
lean_inc(v_val_1029_);
lean_dec_ref(v_isPreorderInst_x3f_1028_);
if (v_isShared_1027_ == 0)
{
lean_ctor_set(v___x_1026_, 0, v_val_1029_);
v___x_1031_ = v___x_1026_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v_val_1029_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
else
{
lean_object* v___x_1033_; lean_object* v___x_1034_; 
lean_dec(v_isPreorderInst_x3f_1028_);
lean_del_object(v___x_1026_);
v___x_1033_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___closed__1);
v___x_1034_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_1033_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_);
return v___x_1034_;
}
}
}
else
{
lean_object* v_a_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1043_; 
v_a_1036_ = lean_ctor_get(v___x_1023_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_1023_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1038_ = v___x_1023_;
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_a_1036_);
lean_dec(v___x_1023_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst___boxed(lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l_Lean_Meta_Grind_Arith_Linear_getIsPreorderInst(v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_);
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
lean_dec(v_a_1044_);
return v_res_1056_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1(void){
_start:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1058_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__0));
v___x_1059_ = l_Lean_stringToMessageData(v___x_1058_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst(lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_){
_start:
{
lean_object* v___x_1072_; 
v___x_1072_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_);
if (lean_obj_tag(v___x_1072_) == 0)
{
lean_object* v_a_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1084_; 
v_a_1073_ = lean_ctor_get(v___x_1072_, 0);
v_isSharedCheck_1084_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1084_ == 0)
{
v___x_1075_ = v___x_1072_;
v_isShared_1076_ = v_isSharedCheck_1084_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_a_1073_);
lean_dec(v___x_1072_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1084_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v_orderedAddInst_x3f_1077_; 
v_orderedAddInst_x3f_1077_ = lean_ctor_get(v_a_1073_, 9);
lean_inc(v_orderedAddInst_x3f_1077_);
lean_dec(v_a_1073_);
if (lean_obj_tag(v_orderedAddInst_x3f_1077_) == 1)
{
lean_object* v_val_1078_; lean_object* v___x_1080_; 
v_val_1078_ = lean_ctor_get(v_orderedAddInst_x3f_1077_, 0);
lean_inc(v_val_1078_);
lean_dec_ref(v_orderedAddInst_x3f_1077_);
if (v_isShared_1076_ == 0)
{
lean_ctor_set(v___x_1075_, 0, v_val_1078_);
v___x_1080_ = v___x_1075_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v_val_1078_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
else
{
lean_object* v___x_1082_; lean_object* v___x_1083_; 
lean_dec(v_orderedAddInst_x3f_1077_);
lean_del_object(v___x_1075_);
v___x_1082_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1);
v___x_1083_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_1082_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_);
return v___x_1083_;
}
}
}
else
{
lean_object* v_a_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1092_; 
v_a_1085_ = lean_ctor_get(v___x_1072_, 0);
v_isSharedCheck_1092_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1092_ == 0)
{
v___x_1087_ = v___x_1072_;
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_a_1085_);
lean_dec(v___x_1072_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v___x_1090_; 
if (v_isShared_1088_ == 0)
{
v___x_1090_ = v___x_1087_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v_a_1085_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
return v___x_1090_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___boxed(lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_){
_start:
{
lean_object* v_res_1105_; 
v_res_1105_ = l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst(v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_);
lean_dec(v_a_1103_);
lean_dec_ref(v_a_1102_);
lean_dec(v_a_1101_);
lean_dec_ref(v_a_1100_);
lean_dec(v_a_1099_);
lean_dec_ref(v_a_1098_);
lean_dec(v_a_1097_);
lean_dec_ref(v_a_1096_);
lean_dec(v_a_1095_);
lean_dec(v_a_1094_);
lean_dec(v_a_1093_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isOrderedAdd(lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_){
_start:
{
lean_object* v___x_1118_; 
v___x_1118_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_);
if (lean_obj_tag(v___x_1118_) == 0)
{
lean_object* v_a_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1134_; 
v_a_1119_ = lean_ctor_get(v___x_1118_, 0);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1121_ = v___x_1118_;
v_isShared_1122_ = v_isSharedCheck_1134_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_a_1119_);
lean_dec(v___x_1118_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1134_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v_orderedAddInst_x3f_1123_; 
v_orderedAddInst_x3f_1123_ = lean_ctor_get(v_a_1119_, 9);
lean_inc(v_orderedAddInst_x3f_1123_);
lean_dec(v_a_1119_);
if (lean_obj_tag(v_orderedAddInst_x3f_1123_) == 0)
{
uint8_t v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1127_; 
v___x_1124_ = 0;
v___x_1125_ = lean_box(v___x_1124_);
if (v_isShared_1122_ == 0)
{
lean_ctor_set(v___x_1121_, 0, v___x_1125_);
v___x_1127_ = v___x_1121_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v___x_1125_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
return v___x_1127_;
}
}
else
{
uint8_t v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1132_; 
lean_dec_ref(v_orderedAddInst_x3f_1123_);
v___x_1129_ = 1;
v___x_1130_ = lean_box(v___x_1129_);
if (v_isShared_1122_ == 0)
{
lean_ctor_set(v___x_1121_, 0, v___x_1130_);
v___x_1132_ = v___x_1121_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v___x_1130_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
}
}
else
{
lean_object* v_a_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1142_; 
v_a_1135_ = lean_ctor_get(v___x_1118_, 0);
v_isSharedCheck_1142_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1137_ = v___x_1118_;
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_a_1135_);
lean_dec(v___x_1118_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1140_; 
if (v_isShared_1138_ == 0)
{
v___x_1140_ = v___x_1137_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_a_1135_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_isOrderedAdd___boxed(lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_){
_start:
{
lean_object* v_res_1155_; 
v_res_1155_ = l_Lean_Meta_Grind_Arith_Linear_isOrderedAdd(v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_);
lean_dec(v_a_1153_);
lean_dec_ref(v_a_1152_);
lean_dec(v_a_1151_);
lean_dec_ref(v_a_1150_);
lean_dec(v_a_1149_);
lean_dec_ref(v_a_1148_);
lean_dec(v_a_1147_);
lean_dec_ref(v_a_1146_);
lean_dec(v_a_1145_);
lean_dec(v_a_1144_);
lean_dec(v_a_1143_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___redArg___lam__0(lean_object* v_toPure_1156_, lean_object* v_inst_1157_, lean_object* v_inst_1158_, lean_object* v_____do__lift_1159_){
_start:
{
lean_object* v_ltFn_x3f_1160_; 
v_ltFn_x3f_1160_ = lean_ctor_get(v_____do__lift_1159_, 21);
lean_inc(v_ltFn_x3f_1160_);
lean_dec_ref(v_____do__lift_1159_);
if (lean_obj_tag(v_ltFn_x3f_1160_) == 1)
{
lean_object* v_val_1161_; lean_object* v___x_1162_; 
lean_dec_ref(v_inst_1158_);
lean_dec_ref(v_inst_1157_);
v_val_1161_ = lean_ctor_get(v_ltFn_x3f_1160_, 0);
lean_inc(v_val_1161_);
lean_dec_ref(v_ltFn_x3f_1160_);
v___x_1162_ = lean_apply_2(v_toPure_1156_, lean_box(0), v_val_1161_);
return v___x_1162_;
}
else
{
lean_object* v___x_1163_; lean_object* v___x_1164_; 
lean_dec(v_ltFn_x3f_1160_);
lean_dec(v_toPure_1156_);
v___x_1163_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getOrderedAddInst___closed__1);
v___x_1164_ = l_Lean_throwError___redArg(v_inst_1157_, v_inst_1158_, v___x_1163_);
return v___x_1164_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn___redArg(lean_object* v_inst_1165_, lean_object* v_inst_1166_, lean_object* v_inst_1167_){
_start:
{
lean_object* v_toApplicative_1168_; lean_object* v_toBind_1169_; lean_object* v_toPure_1170_; lean_object* v___f_1171_; lean_object* v___x_1172_; 
v_toApplicative_1168_ = lean_ctor_get(v_inst_1165_, 0);
v_toBind_1169_ = lean_ctor_get(v_inst_1165_, 1);
lean_inc(v_toBind_1169_);
v_toPure_1170_ = lean_ctor_get(v_toApplicative_1168_, 1);
lean_inc(v_toPure_1170_);
v___f_1171_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_getLtFn___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1171_, 0, v_toPure_1170_);
lean_closure_set(v___f_1171_, 1, v_inst_1165_);
lean_closure_set(v___f_1171_, 2, v_inst_1166_);
v___x_1172_ = lean_apply_4(v_toBind_1169_, lean_box(0), lean_box(0), v_inst_1167_, v___f_1171_);
return v___x_1172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLtFn(lean_object* v_m_1173_, lean_object* v_inst_1174_, lean_object* v_inst_1175_, lean_object* v_inst_1176_){
_start:
{
lean_object* v___x_1177_; 
v___x_1177_ = l_Lean_Meta_Grind_Arith_Linear_getLtFn___redArg(v_inst_1174_, v_inst_1175_, v_inst_1176_);
return v___x_1177_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1179_; lean_object* v___x_1180_; 
v___x_1179_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0___closed__0));
v___x_1180_ = l_Lean_stringToMessageData(v___x_1179_);
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0(lean_object* v_toPure_1181_, lean_object* v_inst_1182_, lean_object* v_inst_1183_, lean_object* v_____do__lift_1184_){
_start:
{
lean_object* v_leFn_x3f_1185_; 
v_leFn_x3f_1185_ = lean_ctor_get(v_____do__lift_1184_, 20);
lean_inc(v_leFn_x3f_1185_);
lean_dec_ref(v_____do__lift_1184_);
if (lean_obj_tag(v_leFn_x3f_1185_) == 1)
{
lean_object* v_val_1186_; lean_object* v___x_1187_; 
lean_dec_ref(v_inst_1183_);
lean_dec_ref(v_inst_1182_);
v_val_1186_ = lean_ctor_get(v_leFn_x3f_1185_, 0);
lean_inc(v_val_1186_);
lean_dec_ref(v_leFn_x3f_1185_);
v___x_1187_ = lean_apply_2(v_toPure_1181_, lean_box(0), v_val_1186_);
return v___x_1187_;
}
else
{
lean_object* v___x_1188_; lean_object* v___x_1189_; 
lean_dec(v_leFn_x3f_1185_);
lean_dec(v_toPure_1181_);
v___x_1188_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0___closed__1);
v___x_1189_ = l_Lean_throwError___redArg(v_inst_1182_, v_inst_1183_, v___x_1188_);
return v___x_1189_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg(lean_object* v_inst_1190_, lean_object* v_inst_1191_, lean_object* v_inst_1192_){
_start:
{
lean_object* v_toApplicative_1193_; lean_object* v_toBind_1194_; lean_object* v_toPure_1195_; lean_object* v___f_1196_; lean_object* v___x_1197_; 
v_toApplicative_1193_ = lean_ctor_get(v_inst_1190_, 0);
v_toBind_1194_ = lean_ctor_get(v_inst_1190_, 1);
lean_inc(v_toBind_1194_);
v_toPure_1195_ = lean_ctor_get(v_toApplicative_1193_, 1);
lean_inc(v_toPure_1195_);
v___f_1196_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1196_, 0, v_toPure_1195_);
lean_closure_set(v___f_1196_, 1, v_inst_1190_);
lean_closure_set(v___f_1196_, 2, v_inst_1191_);
v___x_1197_ = lean_apply_4(v_toBind_1194_, lean_box(0), lean_box(0), v_inst_1192_, v___f_1196_);
return v___x_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getLeFn(lean_object* v_m_1198_, lean_object* v_inst_1199_, lean_object* v_inst_1200_, lean_object* v_inst_1201_){
_start:
{
lean_object* v___x_1202_; 
v___x_1202_ = l_Lean_Meta_Grind_Arith_Linear_getLeFn___redArg(v_inst_1199_, v_inst_1200_, v_inst_1201_);
return v___x_1202_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___closed__1(void){
_start:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1204_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___closed__0));
v___x_1205_ = l_Lean_stringToMessageData(v___x_1204_);
return v___x_1205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst(lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_){
_start:
{
lean_object* v___x_1218_; 
v___x_1218_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1206_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_, v_a_1214_, v_a_1215_, v_a_1216_);
if (lean_obj_tag(v___x_1218_) == 0)
{
lean_object* v_a_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1230_; 
v_a_1219_ = lean_ctor_get(v___x_1218_, 0);
v_isSharedCheck_1230_ = !lean_is_exclusive(v___x_1218_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1221_ = v___x_1218_;
v_isShared_1222_ = v_isSharedCheck_1230_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_a_1219_);
lean_dec(v___x_1218_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1230_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v_isLinearInst_x3f_1223_; 
v_isLinearInst_x3f_1223_ = lean_ctor_get(v_a_1219_, 10);
lean_inc(v_isLinearInst_x3f_1223_);
lean_dec(v_a_1219_);
if (lean_obj_tag(v_isLinearInst_x3f_1223_) == 1)
{
lean_object* v_val_1224_; lean_object* v___x_1226_; 
v_val_1224_ = lean_ctor_get(v_isLinearInst_x3f_1223_, 0);
lean_inc(v_val_1224_);
lean_dec_ref(v_isLinearInst_x3f_1223_);
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 0, v_val_1224_);
v___x_1226_ = v___x_1221_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v_val_1224_);
v___x_1226_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
return v___x_1226_;
}
}
else
{
lean_object* v___x_1228_; lean_object* v___x_1229_; 
lean_dec(v_isLinearInst_x3f_1223_);
lean_del_object(v___x_1221_);
v___x_1228_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___closed__1);
v___x_1229_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_1228_, v_a_1213_, v_a_1214_, v_a_1215_, v_a_1216_);
return v___x_1229_;
}
}
}
else
{
lean_object* v_a_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1238_; 
v_a_1231_ = lean_ctor_get(v___x_1218_, 0);
v_isSharedCheck_1238_ = !lean_is_exclusive(v___x_1218_);
if (v_isSharedCheck_1238_ == 0)
{
v___x_1233_ = v___x_1218_;
v_isShared_1234_ = v_isSharedCheck_1238_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_a_1231_);
lean_dec(v___x_1218_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1238_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___x_1236_; 
if (v_isShared_1234_ == 0)
{
v___x_1236_ = v___x_1233_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v_a_1231_);
v___x_1236_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
return v___x_1236_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst___boxed(lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_){
_start:
{
lean_object* v_res_1251_; 
v_res_1251_ = l_Lean_Meta_Grind_Arith_Linear_getIsLinearOrderInst(v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_, v_a_1244_, v_a_1245_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_);
lean_dec(v_a_1249_);
lean_dec_ref(v_a_1248_);
lean_dec(v_a_1247_);
lean_dec_ref(v_a_1246_);
lean_dec(v_a_1245_);
lean_dec_ref(v_a_1244_);
lean_dec(v_a_1243_);
lean_dec_ref(v_a_1242_);
lean_dec(v_a_1241_);
lean_dec(v_a_1240_);
lean_dec(v_a_1239_);
return v_res_1251_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getRingInst___closed__1(void){
_start:
{
lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_1253_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getRingInst___closed__0));
v___x_1254_ = l_Lean_stringToMessageData(v___x_1253_);
return v___x_1254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getRingInst(lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_){
_start:
{
lean_object* v___x_1267_; 
v___x_1267_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_, v_a_1262_, v_a_1263_, v_a_1264_, v_a_1265_);
if (lean_obj_tag(v___x_1267_) == 0)
{
lean_object* v_a_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1279_; 
v_a_1268_ = lean_ctor_get(v___x_1267_, 0);
v_isSharedCheck_1279_ = !lean_is_exclusive(v___x_1267_);
if (v_isSharedCheck_1279_ == 0)
{
v___x_1270_ = v___x_1267_;
v_isShared_1271_ = v_isSharedCheck_1279_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_a_1268_);
lean_dec(v___x_1267_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1279_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v_ringInst_x3f_1272_; 
v_ringInst_x3f_1272_ = lean_ctor_get(v_a_1268_, 12);
lean_inc(v_ringInst_x3f_1272_);
lean_dec(v_a_1268_);
if (lean_obj_tag(v_ringInst_x3f_1272_) == 1)
{
lean_object* v_val_1273_; lean_object* v___x_1275_; 
v_val_1273_ = lean_ctor_get(v_ringInst_x3f_1272_, 0);
lean_inc(v_val_1273_);
lean_dec_ref(v_ringInst_x3f_1272_);
if (v_isShared_1271_ == 0)
{
lean_ctor_set(v___x_1270_, 0, v_val_1273_);
v___x_1275_ = v___x_1270_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_val_1273_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
return v___x_1275_;
}
}
else
{
lean_object* v___x_1277_; lean_object* v___x_1278_; 
lean_dec(v_ringInst_x3f_1272_);
lean_del_object(v___x_1270_);
v___x_1277_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getRingInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getRingInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getRingInst___closed__1);
v___x_1278_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_1277_, v_a_1262_, v_a_1263_, v_a_1264_, v_a_1265_);
return v___x_1278_;
}
}
}
else
{
lean_object* v_a_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1287_; 
v_a_1280_ = lean_ctor_get(v___x_1267_, 0);
v_isSharedCheck_1287_ = !lean_is_exclusive(v___x_1267_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1282_ = v___x_1267_;
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_a_1280_);
lean_dec(v___x_1267_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v___x_1285_; 
if (v_isShared_1283_ == 0)
{
v___x_1285_ = v___x_1282_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_a_1280_);
v___x_1285_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
return v___x_1285_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getRingInst___boxed(lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_){
_start:
{
lean_object* v_res_1300_; 
v_res_1300_ = l_Lean_Meta_Grind_Arith_Linear_getRingInst(v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_);
lean_dec(v_a_1298_);
lean_dec_ref(v_a_1297_);
lean_dec(v_a_1296_);
lean_dec_ref(v_a_1295_);
lean_dec(v_a_1294_);
lean_dec_ref(v_a_1293_);
lean_dec(v_a_1292_);
lean_dec_ref(v_a_1291_);
lean_dec(v_a_1290_);
lean_dec(v_a_1289_);
lean_dec(v_a_1288_);
return v_res_1300_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___closed__1(void){
_start:
{
lean_object* v___x_1302_; lean_object* v___x_1303_; 
v___x_1302_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___closed__0));
v___x_1303_ = l_Lean_stringToMessageData(v___x_1302_);
return v___x_1303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getCommRingInst(lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_){
_start:
{
lean_object* v___x_1316_; 
v___x_1316_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
if (lean_obj_tag(v___x_1316_) == 0)
{
lean_object* v_a_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1328_; 
v_a_1317_ = lean_ctor_get(v___x_1316_, 0);
v_isSharedCheck_1328_ = !lean_is_exclusive(v___x_1316_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1319_ = v___x_1316_;
v_isShared_1320_ = v_isSharedCheck_1328_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_a_1317_);
lean_dec(v___x_1316_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1328_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v_commRingInst_x3f_1321_; 
v_commRingInst_x3f_1321_ = lean_ctor_get(v_a_1317_, 13);
lean_inc(v_commRingInst_x3f_1321_);
lean_dec(v_a_1317_);
if (lean_obj_tag(v_commRingInst_x3f_1321_) == 1)
{
lean_object* v_val_1322_; lean_object* v___x_1324_; 
v_val_1322_ = lean_ctor_get(v_commRingInst_x3f_1321_, 0);
lean_inc(v_val_1322_);
lean_dec_ref(v_commRingInst_x3f_1321_);
if (v_isShared_1320_ == 0)
{
lean_ctor_set(v___x_1319_, 0, v_val_1322_);
v___x_1324_ = v___x_1319_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_val_1322_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
return v___x_1324_;
}
}
else
{
lean_object* v___x_1326_; lean_object* v___x_1327_; 
lean_dec(v_commRingInst_x3f_1321_);
lean_del_object(v___x_1319_);
v___x_1326_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___closed__1);
v___x_1327_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_1326_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_);
return v___x_1327_;
}
}
}
else
{
lean_object* v_a_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1336_; 
v_a_1329_ = lean_ctor_get(v___x_1316_, 0);
v_isSharedCheck_1336_ = !lean_is_exclusive(v___x_1316_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1331_ = v___x_1316_;
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_a_1329_);
lean_dec(v___x_1316_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v___x_1334_; 
if (v_isShared_1332_ == 0)
{
v___x_1334_ = v___x_1331_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v_a_1329_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
return v___x_1334_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getCommRingInst___boxed(lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_){
_start:
{
lean_object* v_res_1349_; 
v_res_1349_ = l_Lean_Meta_Grind_Arith_Linear_getCommRingInst(v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_);
lean_dec(v_a_1347_);
lean_dec_ref(v_a_1346_);
lean_dec(v_a_1345_);
lean_dec_ref(v_a_1344_);
lean_dec(v_a_1343_);
lean_dec_ref(v_a_1342_);
lean_dec(v_a_1341_);
lean_dec_ref(v_a_1340_);
lean_dec(v_a_1339_);
lean_dec(v_a_1338_);
lean_dec(v_a_1337_);
return v_res_1349_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___closed__1(void){
_start:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; 
v___x_1351_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___closed__0));
v___x_1352_ = l_Lean_stringToMessageData(v___x_1351_);
return v___x_1352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst(lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_){
_start:
{
lean_object* v___x_1365_; 
v___x_1365_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_);
if (lean_obj_tag(v___x_1365_) == 0)
{
lean_object* v_a_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1377_; 
v_a_1366_ = lean_ctor_get(v___x_1365_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1365_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1368_ = v___x_1365_;
v_isShared_1369_ = v_isSharedCheck_1377_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_a_1366_);
lean_dec(v___x_1365_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1377_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
lean_object* v_orderedRingInst_x3f_1370_; 
v_orderedRingInst_x3f_1370_ = lean_ctor_get(v_a_1366_, 14);
lean_inc(v_orderedRingInst_x3f_1370_);
lean_dec(v_a_1366_);
if (lean_obj_tag(v_orderedRingInst_x3f_1370_) == 1)
{
lean_object* v_val_1371_; lean_object* v___x_1373_; 
v_val_1371_ = lean_ctor_get(v_orderedRingInst_x3f_1370_, 0);
lean_inc(v_val_1371_);
lean_dec_ref(v_orderedRingInst_x3f_1370_);
if (v_isShared_1369_ == 0)
{
lean_ctor_set(v___x_1368_, 0, v_val_1371_);
v___x_1373_ = v___x_1368_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_val_1371_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
else
{
lean_object* v___x_1375_; lean_object* v___x_1376_; 
lean_dec(v_orderedRingInst_x3f_1370_);
lean_del_object(v___x_1368_);
v___x_1375_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___closed__1, &l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___closed__1);
v___x_1376_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_1375_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_);
return v___x_1376_;
}
}
}
else
{
lean_object* v_a_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1385_; 
v_a_1378_ = lean_ctor_get(v___x_1365_, 0);
v_isSharedCheck_1385_ = !lean_is_exclusive(v___x_1365_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1380_ = v___x_1365_;
v_isShared_1381_ = v_isSharedCheck_1385_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_a_1378_);
lean_dec(v___x_1365_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1385_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v___x_1383_; 
if (v_isShared_1381_ == 0)
{
v___x_1383_ = v___x_1380_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v_a_1378_);
v___x_1383_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
return v___x_1383_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst___boxed(lean_object* v_a_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_){
_start:
{
lean_object* v_res_1398_; 
v_res_1398_ = l_Lean_Meta_Grind_Arith_Linear_getOrderedRingInst(v_a_1386_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_);
lean_dec(v_a_1396_);
lean_dec_ref(v_a_1395_);
lean_dec(v_a_1394_);
lean_dec_ref(v_a_1393_);
lean_dec(v_a_1392_);
lean_dec_ref(v_a_1391_);
lean_dec(v_a_1390_);
lean_dec_ref(v_a_1389_);
lean_dec(v_a_1388_);
lean_dec(v_a_1387_);
lean_dec(v_a_1386_);
return v_res_1398_;
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_eval_x3f_go_spec__0(lean_object* v_a_1399_){
_start:
{
lean_object* v___x_1400_; 
v___x_1400_ = l_Rat_ofInt(v_a_1399_);
return v___x_1400_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_eval_x3f_go(lean_object* v_a_1401_, lean_object* v_v_1402_, lean_object* v_a_1403_){
_start:
{
if (lean_obj_tag(v_a_1403_) == 0)
{
lean_object* v___x_1404_; 
lean_dec_ref(v_a_1401_);
v___x_1404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1404_, 0, v_v_1402_);
return v___x_1404_;
}
else
{
lean_object* v_k_1405_; lean_object* v_v_1406_; lean_object* v_p_1407_; lean_object* v_size_1408_; uint8_t v___x_1409_; 
v_k_1405_ = lean_ctor_get(v_a_1403_, 0);
lean_inc(v_k_1405_);
v_v_1406_ = lean_ctor_get(v_a_1403_, 1);
lean_inc(v_v_1406_);
v_p_1407_ = lean_ctor_get(v_a_1403_, 2);
lean_inc(v_p_1407_);
lean_dec_ref(v_a_1403_);
v_size_1408_ = lean_ctor_get(v_a_1401_, 2);
v___x_1409_ = lean_nat_dec_lt(v_v_1406_, v_size_1408_);
if (v___x_1409_ == 0)
{
lean_object* v___x_1410_; 
lean_dec(v_p_1407_);
lean_dec(v_v_1406_);
lean_dec(v_k_1405_);
lean_dec_ref(v_v_1402_);
lean_dec_ref(v_a_1401_);
v___x_1410_ = lean_box(0);
return v___x_1410_;
}
else
{
lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1411_ = l_Rat_ofInt(v_k_1405_);
v___x_1412_ = l_instInhabitedRat;
lean_inc_ref(v_a_1401_);
v___x_1413_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1412_, v_a_1401_, v_v_1406_);
lean_dec(v_v_1406_);
v___x_1414_ = l_Rat_mul(v___x_1411_, v___x_1413_);
lean_dec_ref(v___x_1411_);
v___x_1415_ = l_Rat_add(v_v_1402_, v___x_1414_);
v_v_1402_ = v___x_1415_;
v_a_1403_ = v_p_1407_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Grind_Linarith_Poly_eval_x3f_spec__0(lean_object* v_a_1417_){
_start:
{
lean_object* v___x_1418_; lean_object* v___x_1419_; 
v___x_1418_ = lean_nat_to_int(v_a_1417_);
v___x_1419_ = l_Rat_ofInt(v___x_1418_);
return v___x_1419_;
}
}
static lean_object* _init_l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0(void){
_start:
{
lean_object* v___x_1420_; lean_object* v___x_1421_; 
v___x_1420_ = lean_unsigned_to_nat(0u);
v___x_1421_ = l_Nat_cast___at___00Lean_Grind_Linarith_Poly_eval_x3f_spec__0(v___x_1420_);
return v___x_1421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_eval_x3f(lean_object* v_p_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_){
_start:
{
lean_object* v___x_1435_; 
v___x_1435_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1423_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_, v_a_1428_, v_a_1429_, v_a_1430_, v_a_1431_, v_a_1432_, v_a_1433_);
if (lean_obj_tag(v___x_1435_) == 0)
{
lean_object* v_a_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1446_; 
v_a_1436_ = lean_ctor_get(v___x_1435_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___x_1435_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1438_ = v___x_1435_;
v_isShared_1439_ = v_isSharedCheck_1446_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_a_1436_);
lean_dec(v___x_1435_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1446_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v_assignment_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1444_; 
v_assignment_1440_ = lean_ctor_get(v_a_1436_, 35);
lean_inc_ref(v_assignment_1440_);
lean_dec(v_a_1436_);
v___x_1441_ = lean_obj_once(&l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0, &l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0_once, _init_l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0);
v___x_1442_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_eval_x3f_go(v_assignment_1440_, v___x_1441_, v_p_1422_);
if (v_isShared_1439_ == 0)
{
lean_ctor_set(v___x_1438_, 0, v___x_1442_);
v___x_1444_ = v___x_1438_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v___x_1442_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
}
else
{
lean_object* v_a_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1454_; 
lean_dec(v_p_1422_);
v_a_1447_ = lean_ctor_get(v___x_1435_, 0);
v_isSharedCheck_1454_ = !lean_is_exclusive(v___x_1435_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1449_ = v___x_1435_;
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_a_1447_);
lean_dec(v___x_1435_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1452_; 
if (v_isShared_1450_ == 0)
{
v___x_1452_ = v___x_1449_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_a_1447_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_eval_x3f___boxed(lean_object* v_p_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_){
_start:
{
lean_object* v_res_1468_; 
v_res_1468_ = l_Lean_Grind_Linarith_Poly_eval_x3f(v_p_1455_, v_a_1456_, v_a_1457_, v_a_1458_, v_a_1459_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_);
lean_dec(v_a_1466_);
lean_dec_ref(v_a_1465_);
lean_dec(v_a_1464_);
lean_dec_ref(v_a_1463_);
lean_dec(v_a_1462_);
lean_dec_ref(v_a_1461_);
lean_dec(v_a_1460_);
lean_dec_ref(v_a_1459_);
lean_dec(v_a_1458_);
lean_dec(v_a_1457_);
lean_dec(v_a_1456_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Nat_cast___at___00Lean_Grind_Linarith_Poly_eval_x3f_spec__0_spec__0(lean_object* v_a_1469_){
_start:
{
lean_object* v___x_1470_; 
v___x_1470_ = lean_nat_to_int(v_a_1469_);
return v___x_1470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_satisfied(lean_object* v_c_1471_, lean_object* v_a_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_){
_start:
{
lean_object* v_p_1484_; uint8_t v_strict_1485_; lean_object* v___x_1486_; 
v_p_1484_ = lean_ctor_get(v_c_1471_, 0);
lean_inc(v_p_1484_);
v_strict_1485_ = lean_ctor_get_uint8(v_c_1471_, sizeof(void*)*2);
lean_dec_ref(v_c_1471_);
v___x_1486_ = l_Lean_Grind_Linarith_Poly_eval_x3f(v_p_1484_, v_a_1472_, v_a_1473_, v_a_1474_, v_a_1475_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_, v_a_1480_, v_a_1481_, v_a_1482_);
if (lean_obj_tag(v___x_1486_) == 0)
{
lean_object* v_a_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1512_; 
v_a_1487_ = lean_ctor_get(v___x_1486_, 0);
v_isSharedCheck_1512_ = !lean_is_exclusive(v___x_1486_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1489_ = v___x_1486_;
v_isShared_1490_ = v_isSharedCheck_1512_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_a_1487_);
lean_dec(v___x_1486_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1512_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
if (lean_obj_tag(v_a_1487_) == 1)
{
if (v_strict_1485_ == 0)
{
lean_object* v_val_1491_; lean_object* v___x_1492_; uint8_t v___x_1493_; uint8_t v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1497_; 
v_val_1491_ = lean_ctor_get(v_a_1487_, 0);
lean_inc(v_val_1491_);
lean_dec_ref(v_a_1487_);
v___x_1492_ = lean_obj_once(&l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0, &l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0_once, _init_l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0);
v___x_1493_ = l_Rat_instDecidableLe(v_val_1491_, v___x_1492_);
v___x_1494_ = l_Bool_toLBool(v___x_1493_);
v___x_1495_ = lean_box(v___x_1494_);
if (v_isShared_1490_ == 0)
{
lean_ctor_set(v___x_1489_, 0, v___x_1495_);
v___x_1497_ = v___x_1489_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v___x_1495_);
v___x_1497_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
return v___x_1497_;
}
}
else
{
lean_object* v_val_1499_; lean_object* v___x_1500_; uint8_t v___x_1501_; uint8_t v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1505_; 
v_val_1499_ = lean_ctor_get(v_a_1487_, 0);
lean_inc(v_val_1499_);
lean_dec_ref(v_a_1487_);
v___x_1500_ = lean_obj_once(&l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0, &l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0_once, _init_l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0);
v___x_1501_ = l_Rat_blt(v_val_1499_, v___x_1500_);
v___x_1502_ = l_Bool_toLBool(v___x_1501_);
v___x_1503_ = lean_box(v___x_1502_);
if (v_isShared_1490_ == 0)
{
lean_ctor_set(v___x_1489_, 0, v___x_1503_);
v___x_1505_ = v___x_1489_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v___x_1503_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
}
}
}
else
{
uint8_t v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1510_; 
lean_dec(v_a_1487_);
v___x_1507_ = 2;
v___x_1508_ = lean_box(v___x_1507_);
if (v_isShared_1490_ == 0)
{
lean_ctor_set(v___x_1489_, 0, v___x_1508_);
v___x_1510_ = v___x_1489_;
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
}
else
{
lean_object* v_a_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1520_; 
v_a_1513_ = lean_ctor_get(v___x_1486_, 0);
v_isSharedCheck_1520_ = !lean_is_exclusive(v___x_1486_);
if (v_isSharedCheck_1520_ == 0)
{
v___x_1515_ = v___x_1486_;
v_isShared_1516_ = v_isSharedCheck_1520_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_a_1513_);
lean_dec(v___x_1486_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_satisfied___boxed(lean_object* v_c_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_){
_start:
{
lean_object* v_res_1534_; 
v_res_1534_ = l_Lean_Meta_Grind_Arith_Linear_IneqCnstr_satisfied(v_c_1521_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_, v_a_1526_, v_a_1527_, v_a_1528_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_);
lean_dec(v_a_1532_);
lean_dec_ref(v_a_1531_);
lean_dec(v_a_1530_);
lean_dec_ref(v_a_1529_);
lean_dec(v_a_1528_);
lean_dec_ref(v_a_1527_);
lean_dec(v_a_1526_);
lean_dec_ref(v_a_1525_);
lean_dec(v_a_1524_);
lean_dec(v_a_1523_);
lean_dec(v_a_1522_);
return v_res_1534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_satisfied(lean_object* v_c_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_){
_start:
{
lean_object* v_p_1548_; lean_object* v___x_1549_; 
v_p_1548_ = lean_ctor_get(v_c_1535_, 0);
lean_inc(v_p_1548_);
lean_dec_ref(v_c_1535_);
v___x_1549_ = l_Lean_Grind_Linarith_Poly_eval_x3f(v_p_1548_, v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_, v_a_1543_, v_a_1544_, v_a_1545_, v_a_1546_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_object* v_a_1550_; lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1569_; 
v_a_1550_ = lean_ctor_get(v___x_1549_, 0);
v_isSharedCheck_1569_ = !lean_is_exclusive(v___x_1549_);
if (v_isSharedCheck_1569_ == 0)
{
v___x_1552_ = v___x_1549_;
v_isShared_1553_ = v_isSharedCheck_1569_;
goto v_resetjp_1551_;
}
else
{
lean_inc(v_a_1550_);
lean_dec(v___x_1549_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1569_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
uint8_t v___y_1555_; 
if (lean_obj_tag(v_a_1550_) == 1)
{
lean_object* v_val_1561_; lean_object* v___x_1562_; uint8_t v___x_1563_; 
v_val_1561_ = lean_ctor_get(v_a_1550_, 0);
lean_inc(v_val_1561_);
lean_dec_ref(v_a_1550_);
v___x_1562_ = lean_obj_once(&l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0, &l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0_once, _init_l_Lean_Grind_Linarith_Poly_eval_x3f___closed__0);
v___x_1563_ = l_instDecidableEqRat_decEq(v_val_1561_, v___x_1562_);
lean_dec(v_val_1561_);
if (v___x_1563_ == 0)
{
uint8_t v___x_1564_; 
v___x_1564_ = 1;
v___y_1555_ = v___x_1564_;
goto v___jp_1554_;
}
else
{
uint8_t v___x_1565_; 
v___x_1565_ = 0;
v___y_1555_ = v___x_1565_;
goto v___jp_1554_;
}
}
else
{
uint8_t v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; 
lean_del_object(v___x_1552_);
lean_dec(v_a_1550_);
v___x_1566_ = 2;
v___x_1567_ = lean_box(v___x_1566_);
v___x_1568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1568_, 0, v___x_1567_);
return v___x_1568_;
}
v___jp_1554_:
{
uint8_t v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1559_; 
v___x_1556_ = l_Bool_toLBool(v___y_1555_);
v___x_1557_ = lean_box(v___x_1556_);
if (v_isShared_1553_ == 0)
{
lean_ctor_set(v___x_1552_, 0, v___x_1557_);
v___x_1559_ = v___x_1552_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v___x_1557_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
}
}
else
{
lean_object* v_a_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1577_; 
v_a_1570_ = lean_ctor_get(v___x_1549_, 0);
v_isSharedCheck_1577_ = !lean_is_exclusive(v___x_1549_);
if (v_isSharedCheck_1577_ == 0)
{
v___x_1572_ = v___x_1549_;
v_isShared_1573_ = v_isSharedCheck_1577_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_a_1570_);
lean_dec(v___x_1549_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1577_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v___x_1575_; 
if (v_isShared_1573_ == 0)
{
v___x_1575_ = v___x_1572_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v_a_1570_);
v___x_1575_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
return v___x_1575_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_satisfied___boxed(lean_object* v_c_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_){
_start:
{
lean_object* v_res_1591_; 
v_res_1591_ = l_Lean_Meta_Grind_Arith_Linear_DiseqCnstr_satisfied(v_c_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_, v_a_1588_, v_a_1589_);
lean_dec(v_a_1589_);
lean_dec_ref(v_a_1588_);
lean_dec(v_a_1587_);
lean_dec_ref(v_a_1586_);
lean_dec(v_a_1585_);
lean_dec_ref(v_a_1584_);
lean_dec(v_a_1583_);
lean_dec_ref(v_a_1582_);
lean_dec(v_a_1581_);
lean_dec(v_a_1580_);
lean_dec(v_a_1579_);
return v_res_1591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg___lam__0(lean_object* v_a_1592_, lean_object* v_x_1593_, lean_object* v_s_1594_){
_start:
{
lean_object* v_structs_1595_; lean_object* v_typeIdOf_1596_; lean_object* v_exprToStructId_1597_; lean_object* v_exprToStructIdEntries_1598_; lean_object* v_forbiddenNatModules_1599_; lean_object* v_natStructs_1600_; lean_object* v_natTypeIdOf_1601_; lean_object* v_exprToNatStructId_1602_; lean_object* v___x_1603_; uint8_t v___x_1604_; 
v_structs_1595_ = lean_ctor_get(v_s_1594_, 0);
v_typeIdOf_1596_ = lean_ctor_get(v_s_1594_, 1);
v_exprToStructId_1597_ = lean_ctor_get(v_s_1594_, 2);
v_exprToStructIdEntries_1598_ = lean_ctor_get(v_s_1594_, 3);
v_forbiddenNatModules_1599_ = lean_ctor_get(v_s_1594_, 4);
v_natStructs_1600_ = lean_ctor_get(v_s_1594_, 5);
v_natTypeIdOf_1601_ = lean_ctor_get(v_s_1594_, 6);
v_exprToNatStructId_1602_ = lean_ctor_get(v_s_1594_, 7);
v___x_1603_ = lean_array_get_size(v_structs_1595_);
v___x_1604_ = lean_nat_dec_lt(v_a_1592_, v___x_1603_);
if (v___x_1604_ == 0)
{
return v_s_1594_;
}
else
{
lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1666_; 
lean_inc_ref(v_exprToNatStructId_1602_);
lean_inc_ref(v_natTypeIdOf_1601_);
lean_inc_ref(v_natStructs_1600_);
lean_inc_ref(v_forbiddenNatModules_1599_);
lean_inc_ref(v_exprToStructIdEntries_1598_);
lean_inc_ref(v_exprToStructId_1597_);
lean_inc_ref(v_typeIdOf_1596_);
lean_inc_ref(v_structs_1595_);
v_isSharedCheck_1666_ = !lean_is_exclusive(v_s_1594_);
if (v_isSharedCheck_1666_ == 0)
{
lean_object* v_unused_1667_; lean_object* v_unused_1668_; lean_object* v_unused_1669_; lean_object* v_unused_1670_; lean_object* v_unused_1671_; lean_object* v_unused_1672_; lean_object* v_unused_1673_; lean_object* v_unused_1674_; 
v_unused_1667_ = lean_ctor_get(v_s_1594_, 7);
lean_dec(v_unused_1667_);
v_unused_1668_ = lean_ctor_get(v_s_1594_, 6);
lean_dec(v_unused_1668_);
v_unused_1669_ = lean_ctor_get(v_s_1594_, 5);
lean_dec(v_unused_1669_);
v_unused_1670_ = lean_ctor_get(v_s_1594_, 4);
lean_dec(v_unused_1670_);
v_unused_1671_ = lean_ctor_get(v_s_1594_, 3);
lean_dec(v_unused_1671_);
v_unused_1672_ = lean_ctor_get(v_s_1594_, 2);
lean_dec(v_unused_1672_);
v_unused_1673_ = lean_ctor_get(v_s_1594_, 1);
lean_dec(v_unused_1673_);
v_unused_1674_ = lean_ctor_get(v_s_1594_, 0);
lean_dec(v_unused_1674_);
v___x_1606_ = v_s_1594_;
v_isShared_1607_ = v_isSharedCheck_1666_;
goto v_resetjp_1605_;
}
else
{
lean_dec(v_s_1594_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1666_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v_v_1608_; lean_object* v_id_1609_; lean_object* v_ringId_x3f_1610_; lean_object* v_type_1611_; lean_object* v_u_1612_; lean_object* v_intModuleInst_1613_; lean_object* v_leInst_x3f_1614_; lean_object* v_ltInst_x3f_1615_; lean_object* v_lawfulOrderLTInst_x3f_1616_; lean_object* v_isPreorderInst_x3f_1617_; lean_object* v_orderedAddInst_x3f_1618_; lean_object* v_isLinearInst_x3f_1619_; lean_object* v_noNatDivInst_x3f_1620_; lean_object* v_ringInst_x3f_1621_; lean_object* v_commRingInst_x3f_1622_; lean_object* v_orderedRingInst_x3f_1623_; lean_object* v_fieldInst_x3f_1624_; lean_object* v_charInst_x3f_1625_; lean_object* v_zero_1626_; lean_object* v_ofNatZero_1627_; lean_object* v_one_x3f_1628_; lean_object* v_leFn_x3f_1629_; lean_object* v_ltFn_x3f_1630_; lean_object* v_addFn_1631_; lean_object* v_zsmulFn_1632_; lean_object* v_nsmulFn_1633_; lean_object* v_zsmulFn_x3f_1634_; lean_object* v_nsmulFn_x3f_1635_; lean_object* v_homomulFn_x3f_1636_; lean_object* v_subFn_1637_; lean_object* v_negFn_1638_; lean_object* v_vars_1639_; lean_object* v_varMap_1640_; lean_object* v_lowers_1641_; lean_object* v_uppers_1642_; lean_object* v_diseqs_1643_; lean_object* v_assignment_1644_; uint8_t v_caseSplits_1645_; lean_object* v_conflict_x3f_1646_; lean_object* v_diseqSplits_1647_; lean_object* v_elimEqs_1648_; lean_object* v_elimStack_1649_; lean_object* v_occurs_1650_; lean_object* v_ignored_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1665_; 
v_v_1608_ = lean_array_fget(v_structs_1595_, v_a_1592_);
v_id_1609_ = lean_ctor_get(v_v_1608_, 0);
v_ringId_x3f_1610_ = lean_ctor_get(v_v_1608_, 1);
v_type_1611_ = lean_ctor_get(v_v_1608_, 2);
v_u_1612_ = lean_ctor_get(v_v_1608_, 3);
v_intModuleInst_1613_ = lean_ctor_get(v_v_1608_, 4);
v_leInst_x3f_1614_ = lean_ctor_get(v_v_1608_, 5);
v_ltInst_x3f_1615_ = lean_ctor_get(v_v_1608_, 6);
v_lawfulOrderLTInst_x3f_1616_ = lean_ctor_get(v_v_1608_, 7);
v_isPreorderInst_x3f_1617_ = lean_ctor_get(v_v_1608_, 8);
v_orderedAddInst_x3f_1618_ = lean_ctor_get(v_v_1608_, 9);
v_isLinearInst_x3f_1619_ = lean_ctor_get(v_v_1608_, 10);
v_noNatDivInst_x3f_1620_ = lean_ctor_get(v_v_1608_, 11);
v_ringInst_x3f_1621_ = lean_ctor_get(v_v_1608_, 12);
v_commRingInst_x3f_1622_ = lean_ctor_get(v_v_1608_, 13);
v_orderedRingInst_x3f_1623_ = lean_ctor_get(v_v_1608_, 14);
v_fieldInst_x3f_1624_ = lean_ctor_get(v_v_1608_, 15);
v_charInst_x3f_1625_ = lean_ctor_get(v_v_1608_, 16);
v_zero_1626_ = lean_ctor_get(v_v_1608_, 17);
v_ofNatZero_1627_ = lean_ctor_get(v_v_1608_, 18);
v_one_x3f_1628_ = lean_ctor_get(v_v_1608_, 19);
v_leFn_x3f_1629_ = lean_ctor_get(v_v_1608_, 20);
v_ltFn_x3f_1630_ = lean_ctor_get(v_v_1608_, 21);
v_addFn_1631_ = lean_ctor_get(v_v_1608_, 22);
v_zsmulFn_1632_ = lean_ctor_get(v_v_1608_, 23);
v_nsmulFn_1633_ = lean_ctor_get(v_v_1608_, 24);
v_zsmulFn_x3f_1634_ = lean_ctor_get(v_v_1608_, 25);
v_nsmulFn_x3f_1635_ = lean_ctor_get(v_v_1608_, 26);
v_homomulFn_x3f_1636_ = lean_ctor_get(v_v_1608_, 27);
v_subFn_1637_ = lean_ctor_get(v_v_1608_, 28);
v_negFn_1638_ = lean_ctor_get(v_v_1608_, 29);
v_vars_1639_ = lean_ctor_get(v_v_1608_, 30);
v_varMap_1640_ = lean_ctor_get(v_v_1608_, 31);
v_lowers_1641_ = lean_ctor_get(v_v_1608_, 32);
v_uppers_1642_ = lean_ctor_get(v_v_1608_, 33);
v_diseqs_1643_ = lean_ctor_get(v_v_1608_, 34);
v_assignment_1644_ = lean_ctor_get(v_v_1608_, 35);
v_caseSplits_1645_ = lean_ctor_get_uint8(v_v_1608_, sizeof(void*)*42);
v_conflict_x3f_1646_ = lean_ctor_get(v_v_1608_, 36);
v_diseqSplits_1647_ = lean_ctor_get(v_v_1608_, 37);
v_elimEqs_1648_ = lean_ctor_get(v_v_1608_, 38);
v_elimStack_1649_ = lean_ctor_get(v_v_1608_, 39);
v_occurs_1650_ = lean_ctor_get(v_v_1608_, 40);
v_ignored_1651_ = lean_ctor_get(v_v_1608_, 41);
v_isSharedCheck_1665_ = !lean_is_exclusive(v_v_1608_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1653_ = v_v_1608_;
v_isShared_1654_ = v_isSharedCheck_1665_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_ignored_1651_);
lean_inc(v_occurs_1650_);
lean_inc(v_elimStack_1649_);
lean_inc(v_elimEqs_1648_);
lean_inc(v_diseqSplits_1647_);
lean_inc(v_conflict_x3f_1646_);
lean_inc(v_assignment_1644_);
lean_inc(v_diseqs_1643_);
lean_inc(v_uppers_1642_);
lean_inc(v_lowers_1641_);
lean_inc(v_varMap_1640_);
lean_inc(v_vars_1639_);
lean_inc(v_negFn_1638_);
lean_inc(v_subFn_1637_);
lean_inc(v_homomulFn_x3f_1636_);
lean_inc(v_nsmulFn_x3f_1635_);
lean_inc(v_zsmulFn_x3f_1634_);
lean_inc(v_nsmulFn_1633_);
lean_inc(v_zsmulFn_1632_);
lean_inc(v_addFn_1631_);
lean_inc(v_ltFn_x3f_1630_);
lean_inc(v_leFn_x3f_1629_);
lean_inc(v_one_x3f_1628_);
lean_inc(v_ofNatZero_1627_);
lean_inc(v_zero_1626_);
lean_inc(v_charInst_x3f_1625_);
lean_inc(v_fieldInst_x3f_1624_);
lean_inc(v_orderedRingInst_x3f_1623_);
lean_inc(v_commRingInst_x3f_1622_);
lean_inc(v_ringInst_x3f_1621_);
lean_inc(v_noNatDivInst_x3f_1620_);
lean_inc(v_isLinearInst_x3f_1619_);
lean_inc(v_orderedAddInst_x3f_1618_);
lean_inc(v_isPreorderInst_x3f_1617_);
lean_inc(v_lawfulOrderLTInst_x3f_1616_);
lean_inc(v_ltInst_x3f_1615_);
lean_inc(v_leInst_x3f_1614_);
lean_inc(v_intModuleInst_1613_);
lean_inc(v_u_1612_);
lean_inc(v_type_1611_);
lean_inc(v_ringId_x3f_1610_);
lean_inc(v_id_1609_);
lean_dec(v_v_1608_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1665_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___x_1655_; lean_object* v_xs_x27_1656_; lean_object* v___x_1657_; lean_object* v___x_1659_; 
v___x_1655_ = lean_box(0);
v_xs_x27_1656_ = lean_array_fset(v_structs_1595_, v_a_1592_, v___x_1655_);
v___x_1657_ = l_Lean_Meta_Grind_Arith_shrink(v_assignment_1644_, v_x_1593_);
if (v_isShared_1654_ == 0)
{
lean_ctor_set(v___x_1653_, 35, v___x_1657_);
v___x_1659_ = v___x_1653_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v_id_1609_);
lean_ctor_set(v_reuseFailAlloc_1664_, 1, v_ringId_x3f_1610_);
lean_ctor_set(v_reuseFailAlloc_1664_, 2, v_type_1611_);
lean_ctor_set(v_reuseFailAlloc_1664_, 3, v_u_1612_);
lean_ctor_set(v_reuseFailAlloc_1664_, 4, v_intModuleInst_1613_);
lean_ctor_set(v_reuseFailAlloc_1664_, 5, v_leInst_x3f_1614_);
lean_ctor_set(v_reuseFailAlloc_1664_, 6, v_ltInst_x3f_1615_);
lean_ctor_set(v_reuseFailAlloc_1664_, 7, v_lawfulOrderLTInst_x3f_1616_);
lean_ctor_set(v_reuseFailAlloc_1664_, 8, v_isPreorderInst_x3f_1617_);
lean_ctor_set(v_reuseFailAlloc_1664_, 9, v_orderedAddInst_x3f_1618_);
lean_ctor_set(v_reuseFailAlloc_1664_, 10, v_isLinearInst_x3f_1619_);
lean_ctor_set(v_reuseFailAlloc_1664_, 11, v_noNatDivInst_x3f_1620_);
lean_ctor_set(v_reuseFailAlloc_1664_, 12, v_ringInst_x3f_1621_);
lean_ctor_set(v_reuseFailAlloc_1664_, 13, v_commRingInst_x3f_1622_);
lean_ctor_set(v_reuseFailAlloc_1664_, 14, v_orderedRingInst_x3f_1623_);
lean_ctor_set(v_reuseFailAlloc_1664_, 15, v_fieldInst_x3f_1624_);
lean_ctor_set(v_reuseFailAlloc_1664_, 16, v_charInst_x3f_1625_);
lean_ctor_set(v_reuseFailAlloc_1664_, 17, v_zero_1626_);
lean_ctor_set(v_reuseFailAlloc_1664_, 18, v_ofNatZero_1627_);
lean_ctor_set(v_reuseFailAlloc_1664_, 19, v_one_x3f_1628_);
lean_ctor_set(v_reuseFailAlloc_1664_, 20, v_leFn_x3f_1629_);
lean_ctor_set(v_reuseFailAlloc_1664_, 21, v_ltFn_x3f_1630_);
lean_ctor_set(v_reuseFailAlloc_1664_, 22, v_addFn_1631_);
lean_ctor_set(v_reuseFailAlloc_1664_, 23, v_zsmulFn_1632_);
lean_ctor_set(v_reuseFailAlloc_1664_, 24, v_nsmulFn_1633_);
lean_ctor_set(v_reuseFailAlloc_1664_, 25, v_zsmulFn_x3f_1634_);
lean_ctor_set(v_reuseFailAlloc_1664_, 26, v_nsmulFn_x3f_1635_);
lean_ctor_set(v_reuseFailAlloc_1664_, 27, v_homomulFn_x3f_1636_);
lean_ctor_set(v_reuseFailAlloc_1664_, 28, v_subFn_1637_);
lean_ctor_set(v_reuseFailAlloc_1664_, 29, v_negFn_1638_);
lean_ctor_set(v_reuseFailAlloc_1664_, 30, v_vars_1639_);
lean_ctor_set(v_reuseFailAlloc_1664_, 31, v_varMap_1640_);
lean_ctor_set(v_reuseFailAlloc_1664_, 32, v_lowers_1641_);
lean_ctor_set(v_reuseFailAlloc_1664_, 33, v_uppers_1642_);
lean_ctor_set(v_reuseFailAlloc_1664_, 34, v_diseqs_1643_);
lean_ctor_set(v_reuseFailAlloc_1664_, 35, v___x_1657_);
lean_ctor_set(v_reuseFailAlloc_1664_, 36, v_conflict_x3f_1646_);
lean_ctor_set(v_reuseFailAlloc_1664_, 37, v_diseqSplits_1647_);
lean_ctor_set(v_reuseFailAlloc_1664_, 38, v_elimEqs_1648_);
lean_ctor_set(v_reuseFailAlloc_1664_, 39, v_elimStack_1649_);
lean_ctor_set(v_reuseFailAlloc_1664_, 40, v_occurs_1650_);
lean_ctor_set(v_reuseFailAlloc_1664_, 41, v_ignored_1651_);
lean_ctor_set_uint8(v_reuseFailAlloc_1664_, sizeof(void*)*42, v_caseSplits_1645_);
v___x_1659_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
lean_object* v___x_1660_; lean_object* v___x_1662_; 
v___x_1660_ = lean_array_fset(v_xs_x27_1656_, v_a_1592_, v___x_1659_);
if (v_isShared_1607_ == 0)
{
lean_ctor_set(v___x_1606_, 0, v___x_1660_);
v___x_1662_ = v___x_1606_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v___x_1660_);
lean_ctor_set(v_reuseFailAlloc_1663_, 1, v_typeIdOf_1596_);
lean_ctor_set(v_reuseFailAlloc_1663_, 2, v_exprToStructId_1597_);
lean_ctor_set(v_reuseFailAlloc_1663_, 3, v_exprToStructIdEntries_1598_);
lean_ctor_set(v_reuseFailAlloc_1663_, 4, v_forbiddenNatModules_1599_);
lean_ctor_set(v_reuseFailAlloc_1663_, 5, v_natStructs_1600_);
lean_ctor_set(v_reuseFailAlloc_1663_, 6, v_natTypeIdOf_1601_);
lean_ctor_set(v_reuseFailAlloc_1663_, 7, v_exprToNatStructId_1602_);
v___x_1662_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
return v___x_1662_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg___lam__0___boxed(lean_object* v_a_1675_, lean_object* v_x_1676_, lean_object* v_s_1677_){
_start:
{
lean_object* v_res_1678_; 
v_res_1678_ = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg___lam__0(v_a_1675_, v_x_1676_, v_s_1677_);
lean_dec(v_x_1676_);
lean_dec(v_a_1675_);
return v_res_1678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg(lean_object* v_x_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_){
_start:
{
lean_object* v___f_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; 
v___f_1683_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1683_, 0, v_a_1680_);
lean_closure_set(v___f_1683_, 1, v_x_1679_);
v___x_1684_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_1685_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1684_, v___f_1683_, v_a_1681_);
return v___x_1685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg___boxed(lean_object* v_x_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_){
_start:
{
lean_object* v_res_1690_; 
v_res_1690_ = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg(v_x_1686_, v_a_1687_, v_a_1688_);
lean_dec(v_a_1688_);
return v_res_1690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom(lean_object* v_x_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_){
_start:
{
lean_object* v___x_1704_; 
v___x_1704_ = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___redArg(v_x_1691_, v_a_1692_, v_a_1693_);
return v___x_1704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom___boxed(lean_object* v_x_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_){
_start:
{
lean_object* v_res_1718_; 
v_res_1718_ = l_Lean_Meta_Grind_Arith_Linear_resetAssignmentFrom(v_x_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_, v_a_1712_, v_a_1713_, v_a_1714_, v_a_1715_, v_a_1716_);
lean_dec(v_a_1716_);
lean_dec_ref(v_a_1715_);
lean_dec(v_a_1714_);
lean_dec_ref(v_a_1713_);
lean_dec(v_a_1712_);
lean_dec_ref(v_a_1711_);
lean_dec(v_a_1710_);
lean_dec_ref(v_a_1709_);
lean_dec(v_a_1708_);
lean_dec(v_a_1707_);
return v_res_1718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getVar(lean_object* v_x_1719_, lean_object* v_a_1720_, lean_object* v_a_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_){
_start:
{
lean_object* v___x_1732_; 
v___x_1732_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1720_, v_a_1721_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_);
if (lean_obj_tag(v___x_1732_) == 0)
{
lean_object* v_a_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1749_; 
v_a_1733_ = lean_ctor_get(v___x_1732_, 0);
v_isSharedCheck_1749_ = !lean_is_exclusive(v___x_1732_);
if (v_isSharedCheck_1749_ == 0)
{
v___x_1735_ = v___x_1732_;
v_isShared_1736_ = v_isSharedCheck_1749_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_a_1733_);
lean_dec(v___x_1732_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1749_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v_vars_1737_; lean_object* v_size_1738_; lean_object* v___x_1739_; uint8_t v___x_1740_; 
v_vars_1737_ = lean_ctor_get(v_a_1733_, 30);
lean_inc_ref(v_vars_1737_);
lean_dec(v_a_1733_);
v_size_1738_ = lean_ctor_get(v_vars_1737_, 2);
v___x_1739_ = l_Lean_instInhabitedExpr;
v___x_1740_ = lean_nat_dec_lt(v_x_1719_, v_size_1738_);
if (v___x_1740_ == 0)
{
lean_object* v___x_1741_; lean_object* v___x_1743_; 
lean_dec_ref(v_vars_1737_);
v___x_1741_ = l_outOfBounds___redArg(v___x_1739_);
if (v_isShared_1736_ == 0)
{
lean_ctor_set(v___x_1735_, 0, v___x_1741_);
v___x_1743_ = v___x_1735_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v___x_1741_);
v___x_1743_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
return v___x_1743_;
}
}
else
{
lean_object* v___x_1745_; lean_object* v___x_1747_; 
v___x_1745_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1739_, v_vars_1737_, v_x_1719_);
if (v_isShared_1736_ == 0)
{
lean_ctor_set(v___x_1735_, 0, v___x_1745_);
v___x_1747_ = v___x_1735_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v___x_1745_);
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
else
{
lean_object* v_a_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1757_; 
v_a_1750_ = lean_ctor_get(v___x_1732_, 0);
v_isSharedCheck_1757_ = !lean_is_exclusive(v___x_1732_);
if (v_isSharedCheck_1757_ == 0)
{
v___x_1752_ = v___x_1732_;
v_isShared_1753_ = v_isSharedCheck_1757_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_a_1750_);
lean_dec(v___x_1732_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1757_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
lean_object* v___x_1755_; 
if (v_isShared_1753_ == 0)
{
v___x_1755_ = v___x_1752_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v_a_1750_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getVar___boxed(lean_object* v_x_1758_, lean_object* v_a_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_, lean_object* v_a_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_){
_start:
{
lean_object* v_res_1771_; 
v_res_1771_ = l_Lean_Meta_Grind_Arith_Linear_getVar(v_x_1758_, v_a_1759_, v_a_1760_, v_a_1761_, v_a_1762_, v_a_1763_, v_a_1764_, v_a_1765_, v_a_1766_, v_a_1767_, v_a_1768_, v_a_1769_);
lean_dec(v_a_1769_);
lean_dec_ref(v_a_1768_);
lean_dec(v_a_1767_);
lean_dec_ref(v_a_1766_);
lean_dec(v_a_1765_);
lean_dec_ref(v_a_1764_);
lean_dec(v_a_1763_);
lean_dec_ref(v_a_1762_);
lean_dec(v_a_1761_);
lean_dec(v_a_1760_);
lean_dec(v_a_1759_);
lean_dec(v_x_1758_);
return v_res_1771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_inconsistent(lean_object* v_a_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_){
_start:
{
lean_object* v___x_1784_; 
v___x_1784_ = l_Lean_Meta_Grind_isInconsistent___redArg(v_a_1773_);
if (lean_obj_tag(v___x_1784_) == 0)
{
lean_object* v_a_1785_; uint8_t v___x_1786_; 
v_a_1785_ = lean_ctor_get(v___x_1784_, 0);
lean_inc(v_a_1785_);
v___x_1786_ = lean_unbox(v_a_1785_);
if (v___x_1786_ == 0)
{
lean_object* v___x_1787_; 
lean_dec_ref(v___x_1784_);
v___x_1787_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1772_, v_a_1773_, v_a_1774_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_);
if (lean_obj_tag(v___x_1787_) == 0)
{
lean_object* v_a_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1801_; 
v_a_1788_ = lean_ctor_get(v___x_1787_, 0);
v_isSharedCheck_1801_ = !lean_is_exclusive(v___x_1787_);
if (v_isSharedCheck_1801_ == 0)
{
v___x_1790_ = v___x_1787_;
v_isShared_1791_ = v_isSharedCheck_1801_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_a_1788_);
lean_dec(v___x_1787_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1801_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v_conflict_x3f_1792_; 
v_conflict_x3f_1792_ = lean_ctor_get(v_a_1788_, 36);
lean_inc(v_conflict_x3f_1792_);
lean_dec(v_a_1788_);
if (lean_obj_tag(v_conflict_x3f_1792_) == 0)
{
lean_object* v___x_1794_; 
if (v_isShared_1791_ == 0)
{
lean_ctor_set(v___x_1790_, 0, v_a_1785_);
v___x_1794_ = v___x_1790_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v_a_1785_);
v___x_1794_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
return v___x_1794_;
}
}
else
{
uint8_t v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1799_; 
lean_dec_ref(v_conflict_x3f_1792_);
lean_dec(v_a_1785_);
v___x_1796_ = 1;
v___x_1797_ = lean_box(v___x_1796_);
if (v_isShared_1791_ == 0)
{
lean_ctor_set(v___x_1790_, 0, v___x_1797_);
v___x_1799_ = v___x_1790_;
goto v_reusejp_1798_;
}
else
{
lean_object* v_reuseFailAlloc_1800_; 
v_reuseFailAlloc_1800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1800_, 0, v___x_1797_);
v___x_1799_ = v_reuseFailAlloc_1800_;
goto v_reusejp_1798_;
}
v_reusejp_1798_:
{
return v___x_1799_;
}
}
}
}
else
{
lean_object* v_a_1802_; lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1809_; 
lean_dec(v_a_1785_);
v_a_1802_ = lean_ctor_get(v___x_1787_, 0);
v_isSharedCheck_1809_ = !lean_is_exclusive(v___x_1787_);
if (v_isSharedCheck_1809_ == 0)
{
v___x_1804_ = v___x_1787_;
v_isShared_1805_ = v_isSharedCheck_1809_;
goto v_resetjp_1803_;
}
else
{
lean_inc(v_a_1802_);
lean_dec(v___x_1787_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1809_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
lean_object* v___x_1807_; 
if (v_isShared_1805_ == 0)
{
v___x_1807_ = v___x_1804_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v_a_1802_);
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
else
{
lean_dec(v_a_1785_);
return v___x_1784_;
}
}
else
{
return v___x_1784_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_inconsistent___boxed(lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_){
_start:
{
lean_object* v_res_1822_; 
v_res_1822_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_);
lean_dec(v_a_1820_);
lean_dec_ref(v_a_1819_);
lean_dec(v_a_1818_);
lean_dec_ref(v_a_1817_);
lean_dec(v_a_1816_);
lean_dec_ref(v_a_1815_);
lean_dec(v_a_1814_);
lean_dec_ref(v_a_1813_);
lean_dec(v_a_1812_);
lean_dec(v_a_1811_);
lean_dec(v_a_1810_);
return v_res_1822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_eliminated(lean_object* v_x_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_){
_start:
{
lean_object* v___x_1836_; 
v___x_1836_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1824_, v_a_1825_, v_a_1826_, v_a_1827_, v_a_1828_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_, v_a_1833_, v_a_1834_);
if (lean_obj_tag(v___x_1836_) == 0)
{
lean_object* v_a_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1859_; 
v_a_1837_ = lean_ctor_get(v___x_1836_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1839_ = v___x_1836_;
v_isShared_1840_ = v_isSharedCheck_1859_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_a_1837_);
lean_dec(v___x_1836_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1859_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
lean_object* v___y_1842_; lean_object* v_elimEqs_1853_; lean_object* v_size_1854_; lean_object* v___x_1855_; uint8_t v___x_1856_; 
v_elimEqs_1853_ = lean_ctor_get(v_a_1837_, 38);
lean_inc_ref(v_elimEqs_1853_);
lean_dec(v_a_1837_);
v_size_1854_ = lean_ctor_get(v_elimEqs_1853_, 2);
v___x_1855_ = lean_box(0);
v___x_1856_ = lean_nat_dec_lt(v_x_1823_, v_size_1854_);
if (v___x_1856_ == 0)
{
lean_object* v___x_1857_; 
lean_dec_ref(v_elimEqs_1853_);
v___x_1857_ = l_outOfBounds___redArg(v___x_1855_);
v___y_1842_ = v___x_1857_;
goto v___jp_1841_;
}
else
{
lean_object* v___x_1858_; 
v___x_1858_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1855_, v_elimEqs_1853_, v_x_1823_);
v___y_1842_ = v___x_1858_;
goto v___jp_1841_;
}
v___jp_1841_:
{
if (lean_obj_tag(v___y_1842_) == 0)
{
uint8_t v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1846_; 
v___x_1843_ = 0;
v___x_1844_ = lean_box(v___x_1843_);
if (v_isShared_1840_ == 0)
{
lean_ctor_set(v___x_1839_, 0, v___x_1844_);
v___x_1846_ = v___x_1839_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v___x_1844_);
v___x_1846_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
return v___x_1846_;
}
}
else
{
uint8_t v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1851_; 
lean_dec_ref(v___y_1842_);
v___x_1848_ = 1;
v___x_1849_ = lean_box(v___x_1848_);
if (v_isShared_1840_ == 0)
{
lean_ctor_set(v___x_1839_, 0, v___x_1849_);
v___x_1851_ = v___x_1839_;
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
}
else
{
lean_object* v_a_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1867_; 
v_a_1860_ = lean_ctor_get(v___x_1836_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1862_ = v___x_1836_;
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_a_1860_);
lean_dec(v___x_1836_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
lean_object* v___x_1865_; 
if (v_isShared_1863_ == 0)
{
v___x_1865_ = v___x_1862_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v_a_1860_);
v___x_1865_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
return v___x_1865_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_eliminated___boxed(lean_object* v_x_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_){
_start:
{
lean_object* v_res_1881_; 
v_res_1881_ = l_Lean_Meta_Grind_Arith_Linear_eliminated(v_x_1868_, v_a_1869_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_, v_a_1874_, v_a_1875_, v_a_1876_, v_a_1877_, v_a_1878_, v_a_1879_);
lean_dec(v_a_1879_);
lean_dec_ref(v_a_1878_);
lean_dec(v_a_1877_);
lean_dec_ref(v_a_1876_);
lean_dec(v_a_1875_);
lean_dec_ref(v_a_1874_);
lean_dec(v_a_1873_);
lean_dec_ref(v_a_1872_);
lean_dec(v_a_1871_);
lean_dec(v_a_1870_);
lean_dec(v_a_1869_);
lean_dec(v_x_1868_);
return v_res_1881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOccursOf(lean_object* v_x_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_){
_start:
{
lean_object* v___x_1895_; 
v___x_1895_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_1883_, v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_);
if (lean_obj_tag(v___x_1895_) == 0)
{
lean_object* v_a_1896_; lean_object* v___x_1898_; uint8_t v_isShared_1899_; uint8_t v_isSharedCheck_1912_; 
v_a_1896_ = lean_ctor_get(v___x_1895_, 0);
v_isSharedCheck_1912_ = !lean_is_exclusive(v___x_1895_);
if (v_isSharedCheck_1912_ == 0)
{
v___x_1898_ = v___x_1895_;
v_isShared_1899_ = v_isSharedCheck_1912_;
goto v_resetjp_1897_;
}
else
{
lean_inc(v_a_1896_);
lean_dec(v___x_1895_);
v___x_1898_ = lean_box(0);
v_isShared_1899_ = v_isSharedCheck_1912_;
goto v_resetjp_1897_;
}
v_resetjp_1897_:
{
lean_object* v_occurs_1900_; lean_object* v_size_1901_; lean_object* v___x_1902_; uint8_t v___x_1903_; 
v_occurs_1900_ = lean_ctor_get(v_a_1896_, 40);
lean_inc_ref(v_occurs_1900_);
lean_dec(v_a_1896_);
v_size_1901_ = lean_ctor_get(v_occurs_1900_, 2);
v___x_1902_ = lean_box(1);
v___x_1903_ = lean_nat_dec_lt(v_x_1882_, v_size_1901_);
if (v___x_1903_ == 0)
{
lean_object* v___x_1904_; lean_object* v___x_1906_; 
lean_dec_ref(v_occurs_1900_);
v___x_1904_ = l_outOfBounds___redArg(v___x_1902_);
if (v_isShared_1899_ == 0)
{
lean_ctor_set(v___x_1898_, 0, v___x_1904_);
v___x_1906_ = v___x_1898_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v___x_1904_);
v___x_1906_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
return v___x_1906_;
}
}
else
{
lean_object* v___x_1908_; lean_object* v___x_1910_; 
v___x_1908_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1902_, v_occurs_1900_, v_x_1882_);
if (v_isShared_1899_ == 0)
{
lean_ctor_set(v___x_1898_, 0, v___x_1908_);
v___x_1910_ = v___x_1898_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v___x_1908_);
v___x_1910_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
return v___x_1910_;
}
}
}
}
else
{
lean_object* v_a_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1920_; 
v_a_1913_ = lean_ctor_get(v___x_1895_, 0);
v_isSharedCheck_1920_ = !lean_is_exclusive(v___x_1895_);
if (v_isSharedCheck_1920_ == 0)
{
v___x_1915_ = v___x_1895_;
v_isShared_1916_ = v_isSharedCheck_1920_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_a_1913_);
lean_dec(v___x_1895_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1920_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v___x_1918_; 
if (v_isShared_1916_ == 0)
{
v___x_1918_ = v___x_1915_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_a_1913_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_getOccursOf___boxed(lean_object* v_x_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_){
_start:
{
lean_object* v_res_1934_; 
v_res_1934_ = l_Lean_Meta_Grind_Arith_Linear_getOccursOf(v_x_1921_, v_a_1922_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_, v_a_1932_);
lean_dec(v_a_1932_);
lean_dec_ref(v_a_1931_);
lean_dec(v_a_1930_);
lean_dec_ref(v_a_1929_);
lean_dec(v_a_1928_);
lean_dec_ref(v_a_1927_);
lean_dec(v_a_1926_);
lean_dec_ref(v_a_1925_);
lean_dec(v_a_1924_);
lean_dec(v_a_1923_);
lean_dec(v_a_1922_);
lean_dec(v_x_1921_);
return v_res_1934_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg(lean_object* v_k_1935_, lean_object* v_t_1936_){
_start:
{
if (lean_obj_tag(v_t_1936_) == 0)
{
lean_object* v_k_1937_; lean_object* v_l_1938_; lean_object* v_r_1939_; uint8_t v___x_1940_; 
v_k_1937_ = lean_ctor_get(v_t_1936_, 1);
v_l_1938_ = lean_ctor_get(v_t_1936_, 3);
v_r_1939_ = lean_ctor_get(v_t_1936_, 4);
v___x_1940_ = lean_nat_dec_lt(v_k_1935_, v_k_1937_);
if (v___x_1940_ == 0)
{
uint8_t v___x_1941_; 
v___x_1941_ = lean_nat_dec_eq(v_k_1935_, v_k_1937_);
if (v___x_1941_ == 0)
{
v_t_1936_ = v_r_1939_;
goto _start;
}
else
{
return v___x_1941_;
}
}
else
{
v_t_1936_ = v_l_1938_;
goto _start;
}
}
else
{
uint8_t v___x_1944_; 
v___x_1944_ = 0;
return v___x_1944_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg___boxed(lean_object* v_k_1945_, lean_object* v_t_1946_){
_start:
{
uint8_t v_res_1947_; lean_object* v_r_1948_; 
v_res_1947_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg(v_k_1945_, v_t_1946_);
lean_dec(v_t_1946_);
lean_dec(v_k_1945_);
v_r_1948_ = lean_box(v_res_1947_);
return v_r_1948_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1___redArg(lean_object* v_k_1949_, lean_object* v_v_1950_, lean_object* v_t_1951_){
_start:
{
if (lean_obj_tag(v_t_1951_) == 0)
{
lean_object* v_size_1952_; lean_object* v_k_1953_; lean_object* v_v_1954_; lean_object* v_l_1955_; lean_object* v_r_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_2237_; 
v_size_1952_ = lean_ctor_get(v_t_1951_, 0);
v_k_1953_ = lean_ctor_get(v_t_1951_, 1);
v_v_1954_ = lean_ctor_get(v_t_1951_, 2);
v_l_1955_ = lean_ctor_get(v_t_1951_, 3);
v_r_1956_ = lean_ctor_get(v_t_1951_, 4);
v_isSharedCheck_2237_ = !lean_is_exclusive(v_t_1951_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_1958_ = v_t_1951_;
v_isShared_1959_ = v_isSharedCheck_2237_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_r_1956_);
lean_inc(v_l_1955_);
lean_inc(v_v_1954_);
lean_inc(v_k_1953_);
lean_inc(v_size_1952_);
lean_dec(v_t_1951_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_2237_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
uint8_t v___x_1960_; 
v___x_1960_ = lean_nat_dec_lt(v_k_1949_, v_k_1953_);
if (v___x_1960_ == 0)
{
uint8_t v___x_1961_; 
v___x_1961_ = lean_nat_dec_eq(v_k_1949_, v_k_1953_);
if (v___x_1961_ == 0)
{
lean_object* v_impl_1962_; lean_object* v___x_1963_; 
lean_dec(v_size_1952_);
v_impl_1962_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1___redArg(v_k_1949_, v_v_1950_, v_r_1956_);
v___x_1963_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1955_) == 0)
{
lean_object* v_size_1964_; lean_object* v_size_1965_; lean_object* v_k_1966_; lean_object* v_v_1967_; lean_object* v_l_1968_; lean_object* v_r_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; uint8_t v___x_1972_; 
v_size_1964_ = lean_ctor_get(v_l_1955_, 0);
v_size_1965_ = lean_ctor_get(v_impl_1962_, 0);
lean_inc(v_size_1965_);
v_k_1966_ = lean_ctor_get(v_impl_1962_, 1);
lean_inc(v_k_1966_);
v_v_1967_ = lean_ctor_get(v_impl_1962_, 2);
lean_inc(v_v_1967_);
v_l_1968_ = lean_ctor_get(v_impl_1962_, 3);
lean_inc(v_l_1968_);
v_r_1969_ = lean_ctor_get(v_impl_1962_, 4);
lean_inc(v_r_1969_);
v___x_1970_ = lean_unsigned_to_nat(3u);
v___x_1971_ = lean_nat_mul(v___x_1970_, v_size_1964_);
v___x_1972_ = lean_nat_dec_lt(v___x_1971_, v_size_1965_);
lean_dec(v___x_1971_);
if (v___x_1972_ == 0)
{
lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1976_; 
lean_dec(v_r_1969_);
lean_dec(v_l_1968_);
lean_dec(v_v_1967_);
lean_dec(v_k_1966_);
v___x_1973_ = lean_nat_add(v___x_1963_, v_size_1964_);
v___x_1974_ = lean_nat_add(v___x_1973_, v_size_1965_);
lean_dec(v_size_1965_);
lean_dec(v___x_1973_);
if (v_isShared_1959_ == 0)
{
lean_ctor_set(v___x_1958_, 4, v_impl_1962_);
lean_ctor_set(v___x_1958_, 0, v___x_1974_);
v___x_1976_ = v___x_1958_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v___x_1974_);
lean_ctor_set(v_reuseFailAlloc_1977_, 1, v_k_1953_);
lean_ctor_set(v_reuseFailAlloc_1977_, 2, v_v_1954_);
lean_ctor_set(v_reuseFailAlloc_1977_, 3, v_l_1955_);
lean_ctor_set(v_reuseFailAlloc_1977_, 4, v_impl_1962_);
v___x_1976_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
return v___x_1976_;
}
}
else
{
lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_2041_; 
v_isSharedCheck_2041_ = !lean_is_exclusive(v_impl_1962_);
if (v_isSharedCheck_2041_ == 0)
{
lean_object* v_unused_2042_; lean_object* v_unused_2043_; lean_object* v_unused_2044_; lean_object* v_unused_2045_; lean_object* v_unused_2046_; 
v_unused_2042_ = lean_ctor_get(v_impl_1962_, 4);
lean_dec(v_unused_2042_);
v_unused_2043_ = lean_ctor_get(v_impl_1962_, 3);
lean_dec(v_unused_2043_);
v_unused_2044_ = lean_ctor_get(v_impl_1962_, 2);
lean_dec(v_unused_2044_);
v_unused_2045_ = lean_ctor_get(v_impl_1962_, 1);
lean_dec(v_unused_2045_);
v_unused_2046_ = lean_ctor_get(v_impl_1962_, 0);
lean_dec(v_unused_2046_);
v___x_1979_ = v_impl_1962_;
v_isShared_1980_ = v_isSharedCheck_2041_;
goto v_resetjp_1978_;
}
else
{
lean_dec(v_impl_1962_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_2041_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
lean_object* v_size_1981_; lean_object* v_k_1982_; lean_object* v_v_1983_; lean_object* v_l_1984_; lean_object* v_r_1985_; lean_object* v_size_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; uint8_t v___x_1989_; 
v_size_1981_ = lean_ctor_get(v_l_1968_, 0);
v_k_1982_ = lean_ctor_get(v_l_1968_, 1);
v_v_1983_ = lean_ctor_get(v_l_1968_, 2);
v_l_1984_ = lean_ctor_get(v_l_1968_, 3);
v_r_1985_ = lean_ctor_get(v_l_1968_, 4);
v_size_1986_ = lean_ctor_get(v_r_1969_, 0);
v___x_1987_ = lean_unsigned_to_nat(2u);
v___x_1988_ = lean_nat_mul(v___x_1987_, v_size_1986_);
v___x_1989_ = lean_nat_dec_lt(v_size_1981_, v___x_1988_);
lean_dec(v___x_1988_);
if (v___x_1989_ == 0)
{
lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_2017_; 
lean_inc(v_r_1985_);
lean_inc(v_l_1984_);
lean_inc(v_v_1983_);
lean_inc(v_k_1982_);
v_isSharedCheck_2017_ = !lean_is_exclusive(v_l_1968_);
if (v_isSharedCheck_2017_ == 0)
{
lean_object* v_unused_2018_; lean_object* v_unused_2019_; lean_object* v_unused_2020_; lean_object* v_unused_2021_; lean_object* v_unused_2022_; 
v_unused_2018_ = lean_ctor_get(v_l_1968_, 4);
lean_dec(v_unused_2018_);
v_unused_2019_ = lean_ctor_get(v_l_1968_, 3);
lean_dec(v_unused_2019_);
v_unused_2020_ = lean_ctor_get(v_l_1968_, 2);
lean_dec(v_unused_2020_);
v_unused_2021_ = lean_ctor_get(v_l_1968_, 1);
lean_dec(v_unused_2021_);
v_unused_2022_ = lean_ctor_get(v_l_1968_, 0);
lean_dec(v_unused_2022_);
v___x_1991_ = v_l_1968_;
v_isShared_1992_ = v_isSharedCheck_2017_;
goto v_resetjp_1990_;
}
else
{
lean_dec(v_l_1968_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_2017_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___y_1996_; lean_object* v___y_1997_; lean_object* v___y_1998_; lean_object* v___y_2007_; 
v___x_1993_ = lean_nat_add(v___x_1963_, v_size_1964_);
v___x_1994_ = lean_nat_add(v___x_1993_, v_size_1965_);
lean_dec(v_size_1965_);
if (lean_obj_tag(v_l_1984_) == 0)
{
lean_object* v_size_2015_; 
v_size_2015_ = lean_ctor_get(v_l_1984_, 0);
lean_inc(v_size_2015_);
v___y_2007_ = v_size_2015_;
goto v___jp_2006_;
}
else
{
lean_object* v___x_2016_; 
v___x_2016_ = lean_unsigned_to_nat(0u);
v___y_2007_ = v___x_2016_;
goto v___jp_2006_;
}
v___jp_1995_:
{
lean_object* v___x_1999_; lean_object* v___x_2001_; 
v___x_1999_ = lean_nat_add(v___y_1996_, v___y_1998_);
lean_dec(v___y_1998_);
lean_dec(v___y_1996_);
if (v_isShared_1992_ == 0)
{
lean_ctor_set(v___x_1991_, 4, v_r_1969_);
lean_ctor_set(v___x_1991_, 3, v_r_1985_);
lean_ctor_set(v___x_1991_, 2, v_v_1967_);
lean_ctor_set(v___x_1991_, 1, v_k_1966_);
lean_ctor_set(v___x_1991_, 0, v___x_1999_);
v___x_2001_ = v___x_1991_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v___x_1999_);
lean_ctor_set(v_reuseFailAlloc_2005_, 1, v_k_1966_);
lean_ctor_set(v_reuseFailAlloc_2005_, 2, v_v_1967_);
lean_ctor_set(v_reuseFailAlloc_2005_, 3, v_r_1985_);
lean_ctor_set(v_reuseFailAlloc_2005_, 4, v_r_1969_);
v___x_2001_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
lean_object* v___x_2003_; 
if (v_isShared_1980_ == 0)
{
lean_ctor_set(v___x_1979_, 4, v___x_2001_);
lean_ctor_set(v___x_1979_, 3, v___y_1997_);
lean_ctor_set(v___x_1979_, 2, v_v_1983_);
lean_ctor_set(v___x_1979_, 1, v_k_1982_);
lean_ctor_set(v___x_1979_, 0, v___x_1994_);
v___x_2003_ = v___x_1979_;
goto v_reusejp_2002_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v___x_1994_);
lean_ctor_set(v_reuseFailAlloc_2004_, 1, v_k_1982_);
lean_ctor_set(v_reuseFailAlloc_2004_, 2, v_v_1983_);
lean_ctor_set(v_reuseFailAlloc_2004_, 3, v___y_1997_);
lean_ctor_set(v_reuseFailAlloc_2004_, 4, v___x_2001_);
v___x_2003_ = v_reuseFailAlloc_2004_;
goto v_reusejp_2002_;
}
v_reusejp_2002_:
{
return v___x_2003_;
}
}
}
v___jp_2006_:
{
lean_object* v___x_2008_; lean_object* v___x_2010_; 
v___x_2008_ = lean_nat_add(v___x_1993_, v___y_2007_);
lean_dec(v___y_2007_);
lean_dec(v___x_1993_);
if (v_isShared_1959_ == 0)
{
lean_ctor_set(v___x_1958_, 4, v_l_1984_);
lean_ctor_set(v___x_1958_, 0, v___x_2008_);
v___x_2010_ = v___x_1958_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v___x_2008_);
lean_ctor_set(v_reuseFailAlloc_2014_, 1, v_k_1953_);
lean_ctor_set(v_reuseFailAlloc_2014_, 2, v_v_1954_);
lean_ctor_set(v_reuseFailAlloc_2014_, 3, v_l_1955_);
lean_ctor_set(v_reuseFailAlloc_2014_, 4, v_l_1984_);
v___x_2010_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
lean_object* v___x_2011_; 
v___x_2011_ = lean_nat_add(v___x_1963_, v_size_1986_);
if (lean_obj_tag(v_r_1985_) == 0)
{
lean_object* v_size_2012_; 
v_size_2012_ = lean_ctor_get(v_r_1985_, 0);
lean_inc(v_size_2012_);
v___y_1996_ = v___x_2011_;
v___y_1997_ = v___x_2010_;
v___y_1998_ = v_size_2012_;
goto v___jp_1995_;
}
else
{
lean_object* v___x_2013_; 
v___x_2013_ = lean_unsigned_to_nat(0u);
v___y_1996_ = v___x_2011_;
v___y_1997_ = v___x_2010_;
v___y_1998_ = v___x_2013_;
goto v___jp_1995_;
}
}
}
}
}
else
{
lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2027_; 
lean_del_object(v___x_1958_);
v___x_2023_ = lean_nat_add(v___x_1963_, v_size_1964_);
v___x_2024_ = lean_nat_add(v___x_2023_, v_size_1965_);
lean_dec(v_size_1965_);
v___x_2025_ = lean_nat_add(v___x_2023_, v_size_1981_);
lean_dec(v___x_2023_);
lean_inc_ref(v_l_1955_);
if (v_isShared_1980_ == 0)
{
lean_ctor_set(v___x_1979_, 4, v_l_1968_);
lean_ctor_set(v___x_1979_, 3, v_l_1955_);
lean_ctor_set(v___x_1979_, 2, v_v_1954_);
lean_ctor_set(v___x_1979_, 1, v_k_1953_);
lean_ctor_set(v___x_1979_, 0, v___x_2025_);
v___x_2027_ = v___x_1979_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v___x_2025_);
lean_ctor_set(v_reuseFailAlloc_2040_, 1, v_k_1953_);
lean_ctor_set(v_reuseFailAlloc_2040_, 2, v_v_1954_);
lean_ctor_set(v_reuseFailAlloc_2040_, 3, v_l_1955_);
lean_ctor_set(v_reuseFailAlloc_2040_, 4, v_l_1968_);
v___x_2027_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2034_; 
v_isSharedCheck_2034_ = !lean_is_exclusive(v_l_1955_);
if (v_isSharedCheck_2034_ == 0)
{
lean_object* v_unused_2035_; lean_object* v_unused_2036_; lean_object* v_unused_2037_; lean_object* v_unused_2038_; lean_object* v_unused_2039_; 
v_unused_2035_ = lean_ctor_get(v_l_1955_, 4);
lean_dec(v_unused_2035_);
v_unused_2036_ = lean_ctor_get(v_l_1955_, 3);
lean_dec(v_unused_2036_);
v_unused_2037_ = lean_ctor_get(v_l_1955_, 2);
lean_dec(v_unused_2037_);
v_unused_2038_ = lean_ctor_get(v_l_1955_, 1);
lean_dec(v_unused_2038_);
v_unused_2039_ = lean_ctor_get(v_l_1955_, 0);
lean_dec(v_unused_2039_);
v___x_2029_ = v_l_1955_;
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
else
{
lean_dec(v_l_1955_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
lean_object* v___x_2032_; 
if (v_isShared_2030_ == 0)
{
lean_ctor_set(v___x_2029_, 4, v_r_1969_);
lean_ctor_set(v___x_2029_, 3, v___x_2027_);
lean_ctor_set(v___x_2029_, 2, v_v_1967_);
lean_ctor_set(v___x_2029_, 1, v_k_1966_);
lean_ctor_set(v___x_2029_, 0, v___x_2024_);
v___x_2032_ = v___x_2029_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v___x_2024_);
lean_ctor_set(v_reuseFailAlloc_2033_, 1, v_k_1966_);
lean_ctor_set(v_reuseFailAlloc_2033_, 2, v_v_1967_);
lean_ctor_set(v_reuseFailAlloc_2033_, 3, v___x_2027_);
lean_ctor_set(v_reuseFailAlloc_2033_, 4, v_r_1969_);
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
}
}
else
{
lean_object* v_l_2047_; 
v_l_2047_ = lean_ctor_get(v_impl_1962_, 3);
lean_inc(v_l_2047_);
if (lean_obj_tag(v_l_2047_) == 0)
{
lean_object* v_r_2048_; lean_object* v_k_2049_; lean_object* v_v_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2073_; 
v_r_2048_ = lean_ctor_get(v_impl_1962_, 4);
v_k_2049_ = lean_ctor_get(v_impl_1962_, 1);
v_v_2050_ = lean_ctor_get(v_impl_1962_, 2);
v_isSharedCheck_2073_ = !lean_is_exclusive(v_impl_1962_);
if (v_isSharedCheck_2073_ == 0)
{
lean_object* v_unused_2074_; lean_object* v_unused_2075_; 
v_unused_2074_ = lean_ctor_get(v_impl_1962_, 3);
lean_dec(v_unused_2074_);
v_unused_2075_ = lean_ctor_get(v_impl_1962_, 0);
lean_dec(v_unused_2075_);
v___x_2052_ = v_impl_1962_;
v_isShared_2053_ = v_isSharedCheck_2073_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_r_2048_);
lean_inc(v_v_2050_);
lean_inc(v_k_2049_);
lean_dec(v_impl_1962_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2073_;
goto v_resetjp_2051_;
}
v_resetjp_2051_:
{
lean_object* v_k_2054_; lean_object* v_v_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2069_; 
v_k_2054_ = lean_ctor_get(v_l_2047_, 1);
v_v_2055_ = lean_ctor_get(v_l_2047_, 2);
v_isSharedCheck_2069_ = !lean_is_exclusive(v_l_2047_);
if (v_isSharedCheck_2069_ == 0)
{
lean_object* v_unused_2070_; lean_object* v_unused_2071_; lean_object* v_unused_2072_; 
v_unused_2070_ = lean_ctor_get(v_l_2047_, 4);
lean_dec(v_unused_2070_);
v_unused_2071_ = lean_ctor_get(v_l_2047_, 3);
lean_dec(v_unused_2071_);
v_unused_2072_ = lean_ctor_get(v_l_2047_, 0);
lean_dec(v_unused_2072_);
v___x_2057_ = v_l_2047_;
v_isShared_2058_ = v_isSharedCheck_2069_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_v_2055_);
lean_inc(v_k_2054_);
lean_dec(v_l_2047_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2069_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v___x_2059_; lean_object* v___x_2061_; 
v___x_2059_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2048_, 2);
if (v_isShared_2058_ == 0)
{
lean_ctor_set(v___x_2057_, 4, v_r_2048_);
lean_ctor_set(v___x_2057_, 3, v_r_2048_);
lean_ctor_set(v___x_2057_, 2, v_v_1954_);
lean_ctor_set(v___x_2057_, 1, v_k_1953_);
lean_ctor_set(v___x_2057_, 0, v___x_1963_);
v___x_2061_ = v___x_2057_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v___x_1963_);
lean_ctor_set(v_reuseFailAlloc_2068_, 1, v_k_1953_);
lean_ctor_set(v_reuseFailAlloc_2068_, 2, v_v_1954_);
lean_ctor_set(v_reuseFailAlloc_2068_, 3, v_r_2048_);
lean_ctor_set(v_reuseFailAlloc_2068_, 4, v_r_2048_);
v___x_2061_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
lean_object* v___x_2063_; 
lean_inc(v_r_2048_);
if (v_isShared_2053_ == 0)
{
lean_ctor_set(v___x_2052_, 3, v_r_2048_);
lean_ctor_set(v___x_2052_, 0, v___x_1963_);
v___x_2063_ = v___x_2052_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v___x_1963_);
lean_ctor_set(v_reuseFailAlloc_2067_, 1, v_k_2049_);
lean_ctor_set(v_reuseFailAlloc_2067_, 2, v_v_2050_);
lean_ctor_set(v_reuseFailAlloc_2067_, 3, v_r_2048_);
lean_ctor_set(v_reuseFailAlloc_2067_, 4, v_r_2048_);
v___x_2063_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
lean_object* v___x_2065_; 
if (v_isShared_1959_ == 0)
{
lean_ctor_set(v___x_1958_, 4, v___x_2063_);
lean_ctor_set(v___x_1958_, 3, v___x_2061_);
lean_ctor_set(v___x_1958_, 2, v_v_2055_);
lean_ctor_set(v___x_1958_, 1, v_k_2054_);
lean_ctor_set(v___x_1958_, 0, v___x_2059_);
v___x_2065_ = v___x_1958_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v___x_2059_);
lean_ctor_set(v_reuseFailAlloc_2066_, 1, v_k_2054_);
lean_ctor_set(v_reuseFailAlloc_2066_, 2, v_v_2055_);
lean_ctor_set(v_reuseFailAlloc_2066_, 3, v___x_2061_);
lean_ctor_set(v_reuseFailAlloc_2066_, 4, v___x_2063_);
v___x_2065_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
return v___x_2065_;
}
}
}
}
}
}
else
{
lean_object* v_r_2076_; 
v_r_2076_ = lean_ctor_get(v_impl_1962_, 4);
lean_inc(v_r_2076_);
if (lean_obj_tag(v_r_2076_) == 0)
{
lean_object* v_k_2077_; lean_object* v_v_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2089_; 
v_k_2077_ = lean_ctor_get(v_impl_1962_, 1);
v_v_2078_ = lean_ctor_get(v_impl_1962_, 2);
v_isSharedCheck_2089_ = !lean_is_exclusive(v_impl_1962_);
if (v_isSharedCheck_2089_ == 0)
{
lean_object* v_unused_2090_; lean_object* v_unused_2091_; lean_object* v_unused_2092_; 
v_unused_2090_ = lean_ctor_get(v_impl_1962_, 4);
lean_dec(v_unused_2090_);
v_unused_2091_ = lean_ctor_get(v_impl_1962_, 3);
lean_dec(v_unused_2091_);
v_unused_2092_ = lean_ctor_get(v_impl_1962_, 0);
lean_dec(v_unused_2092_);
v___x_2080_ = v_impl_1962_;
v_isShared_2081_ = v_isSharedCheck_2089_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_v_2078_);
lean_inc(v_k_2077_);
lean_dec(v_impl_1962_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2089_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
lean_object* v___x_2082_; lean_object* v___x_2084_; 
v___x_2082_ = lean_unsigned_to_nat(3u);
if (v_isShared_2081_ == 0)
{
lean_ctor_set(v___x_2080_, 4, v_l_2047_);
lean_ctor_set(v___x_2080_, 2, v_v_1954_);
lean_ctor_set(v___x_2080_, 1, v_k_1953_);
lean_ctor_set(v___x_2080_, 0, v___x_1963_);
v___x_2084_ = v___x_2080_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v___x_1963_);
lean_ctor_set(v_reuseFailAlloc_2088_, 1, v_k_1953_);
lean_ctor_set(v_reuseFailAlloc_2088_, 2, v_v_1954_);
lean_ctor_set(v_reuseFailAlloc_2088_, 3, v_l_2047_);
lean_ctor_set(v_reuseFailAlloc_2088_, 4, v_l_2047_);
v___x_2084_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
lean_object* v___x_2086_; 
if (v_isShared_1959_ == 0)
{
lean_ctor_set(v___x_1958_, 4, v_r_2076_);
lean_ctor_set(v___x_1958_, 3, v___x_2084_);
lean_ctor_set(v___x_1958_, 2, v_v_2078_);
lean_ctor_set(v___x_1958_, 1, v_k_2077_);
lean_ctor_set(v___x_1958_, 0, v___x_2082_);
v___x_2086_ = v___x_1958_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v___x_2082_);
lean_ctor_set(v_reuseFailAlloc_2087_, 1, v_k_2077_);
lean_ctor_set(v_reuseFailAlloc_2087_, 2, v_v_2078_);
lean_ctor_set(v_reuseFailAlloc_2087_, 3, v___x_2084_);
lean_ctor_set(v_reuseFailAlloc_2087_, 4, v_r_2076_);
v___x_2086_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
return v___x_2086_;
}
}
}
}
else
{
lean_object* v___x_2093_; lean_object* v___x_2095_; 
v___x_2093_ = lean_unsigned_to_nat(2u);
if (v_isShared_1959_ == 0)
{
lean_ctor_set(v___x_1958_, 4, v_impl_1962_);
lean_ctor_set(v___x_1958_, 3, v_r_2076_);
lean_ctor_set(v___x_1958_, 0, v___x_2093_);
v___x_2095_ = v___x_1958_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v___x_2093_);
lean_ctor_set(v_reuseFailAlloc_2096_, 1, v_k_1953_);
lean_ctor_set(v_reuseFailAlloc_2096_, 2, v_v_1954_);
lean_ctor_set(v_reuseFailAlloc_2096_, 3, v_r_2076_);
lean_ctor_set(v_reuseFailAlloc_2096_, 4, v_impl_1962_);
v___x_2095_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
return v___x_2095_;
}
}
}
}
}
else
{
lean_object* v___x_2098_; 
lean_dec(v_v_1954_);
lean_dec(v_k_1953_);
if (v_isShared_1959_ == 0)
{
lean_ctor_set(v___x_1958_, 2, v_v_1950_);
lean_ctor_set(v___x_1958_, 1, v_k_1949_);
v___x_2098_ = v___x_1958_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v_size_1952_);
lean_ctor_set(v_reuseFailAlloc_2099_, 1, v_k_1949_);
lean_ctor_set(v_reuseFailAlloc_2099_, 2, v_v_1950_);
lean_ctor_set(v_reuseFailAlloc_2099_, 3, v_l_1955_);
lean_ctor_set(v_reuseFailAlloc_2099_, 4, v_r_1956_);
v___x_2098_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
return v___x_2098_;
}
}
}
else
{
lean_object* v_impl_2100_; lean_object* v___x_2101_; 
lean_dec(v_size_1952_);
v_impl_2100_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1___redArg(v_k_1949_, v_v_1950_, v_l_1955_);
v___x_2101_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1956_) == 0)
{
lean_object* v_size_2102_; lean_object* v_size_2103_; lean_object* v_k_2104_; lean_object* v_v_2105_; lean_object* v_l_2106_; lean_object* v_r_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; uint8_t v___x_2110_; 
v_size_2102_ = lean_ctor_get(v_r_1956_, 0);
v_size_2103_ = lean_ctor_get(v_impl_2100_, 0);
lean_inc(v_size_2103_);
v_k_2104_ = lean_ctor_get(v_impl_2100_, 1);
lean_inc(v_k_2104_);
v_v_2105_ = lean_ctor_get(v_impl_2100_, 2);
lean_inc(v_v_2105_);
v_l_2106_ = lean_ctor_get(v_impl_2100_, 3);
lean_inc(v_l_2106_);
v_r_2107_ = lean_ctor_get(v_impl_2100_, 4);
lean_inc(v_r_2107_);
v___x_2108_ = lean_unsigned_to_nat(3u);
v___x_2109_ = lean_nat_mul(v___x_2108_, v_size_2102_);
v___x_2110_ = lean_nat_dec_lt(v___x_2109_, v_size_2103_);
lean_dec(v___x_2109_);
if (v___x_2110_ == 0)
{
lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2114_; 
lean_dec(v_r_2107_);
lean_dec(v_l_2106_);
lean_dec(v_v_2105_);
lean_dec(v_k_2104_);
v___x_2111_ = lean_nat_add(v___x_2101_, v_size_2103_);
lean_dec(v_size_2103_);
v___x_2112_ = lean_nat_add(v___x_2111_, v_size_2102_);
lean_dec(v___x_2111_);
if (v_isShared_1959_ == 0)
{
lean_ctor_set(v___x_1958_, 3, v_impl_2100_);
lean_ctor_set(v___x_1958_, 0, v___x_2112_);
v___x_2114_ = v___x_1958_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v___x_2112_);
lean_ctor_set(v_reuseFailAlloc_2115_, 1, v_k_1953_);
lean_ctor_set(v_reuseFailAlloc_2115_, 2, v_v_1954_);
lean_ctor_set(v_reuseFailAlloc_2115_, 3, v_impl_2100_);
lean_ctor_set(v_reuseFailAlloc_2115_, 4, v_r_1956_);
v___x_2114_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
return v___x_2114_;
}
}
else
{
lean_object* v___x_2117_; uint8_t v_isShared_2118_; uint8_t v_isSharedCheck_2181_; 
v_isSharedCheck_2181_ = !lean_is_exclusive(v_impl_2100_);
if (v_isSharedCheck_2181_ == 0)
{
lean_object* v_unused_2182_; lean_object* v_unused_2183_; lean_object* v_unused_2184_; lean_object* v_unused_2185_; lean_object* v_unused_2186_; 
v_unused_2182_ = lean_ctor_get(v_impl_2100_, 4);
lean_dec(v_unused_2182_);
v_unused_2183_ = lean_ctor_get(v_impl_2100_, 3);
lean_dec(v_unused_2183_);
v_unused_2184_ = lean_ctor_get(v_impl_2100_, 2);
lean_dec(v_unused_2184_);
v_unused_2185_ = lean_ctor_get(v_impl_2100_, 1);
lean_dec(v_unused_2185_);
v_unused_2186_ = lean_ctor_get(v_impl_2100_, 0);
lean_dec(v_unused_2186_);
v___x_2117_ = v_impl_2100_;
v_isShared_2118_ = v_isSharedCheck_2181_;
goto v_resetjp_2116_;
}
else
{
lean_dec(v_impl_2100_);
v___x_2117_ = lean_box(0);
v_isShared_2118_ = v_isSharedCheck_2181_;
goto v_resetjp_2116_;
}
v_resetjp_2116_:
{
lean_object* v_size_2119_; lean_object* v_size_2120_; lean_object* v_k_2121_; lean_object* v_v_2122_; lean_object* v_l_2123_; lean_object* v_r_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; uint8_t v___x_2127_; 
v_size_2119_ = lean_ctor_get(v_l_2106_, 0);
v_size_2120_ = lean_ctor_get(v_r_2107_, 0);
v_k_2121_ = lean_ctor_get(v_r_2107_, 1);
v_v_2122_ = lean_ctor_get(v_r_2107_, 2);
v_l_2123_ = lean_ctor_get(v_r_2107_, 3);
v_r_2124_ = lean_ctor_get(v_r_2107_, 4);
v___x_2125_ = lean_unsigned_to_nat(2u);
v___x_2126_ = lean_nat_mul(v___x_2125_, v_size_2119_);
v___x_2127_ = lean_nat_dec_lt(v_size_2120_, v___x_2126_);
lean_dec(v___x_2126_);
if (v___x_2127_ == 0)
{
lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2156_; 
lean_inc(v_r_2124_);
lean_inc(v_l_2123_);
lean_inc(v_v_2122_);
lean_inc(v_k_2121_);
v_isSharedCheck_2156_ = !lean_is_exclusive(v_r_2107_);
if (v_isSharedCheck_2156_ == 0)
{
lean_object* v_unused_2157_; lean_object* v_unused_2158_; lean_object* v_unused_2159_; lean_object* v_unused_2160_; lean_object* v_unused_2161_; 
v_unused_2157_ = lean_ctor_get(v_r_2107_, 4);
lean_dec(v_unused_2157_);
v_unused_2158_ = lean_ctor_get(v_r_2107_, 3);
lean_dec(v_unused_2158_);
v_unused_2159_ = lean_ctor_get(v_r_2107_, 2);
lean_dec(v_unused_2159_);
v_unused_2160_ = lean_ctor_get(v_r_2107_, 1);
lean_dec(v_unused_2160_);
v_unused_2161_ = lean_ctor_get(v_r_2107_, 0);
lean_dec(v_unused_2161_);
v___x_2129_ = v_r_2107_;
v_isShared_2130_ = v_isSharedCheck_2156_;
goto v_resetjp_2128_;
}
else
{
lean_dec(v_r_2107_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2156_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___y_2134_; lean_object* v___y_2135_; lean_object* v___y_2136_; lean_object* v___x_2144_; lean_object* v___y_2146_; 
v___x_2131_ = lean_nat_add(v___x_2101_, v_size_2103_);
lean_dec(v_size_2103_);
v___x_2132_ = lean_nat_add(v___x_2131_, v_size_2102_);
lean_dec(v___x_2131_);
v___x_2144_ = lean_nat_add(v___x_2101_, v_size_2119_);
if (lean_obj_tag(v_l_2123_) == 0)
{
lean_object* v_size_2154_; 
v_size_2154_ = lean_ctor_get(v_l_2123_, 0);
lean_inc(v_size_2154_);
v___y_2146_ = v_size_2154_;
goto v___jp_2145_;
}
else
{
lean_object* v___x_2155_; 
v___x_2155_ = lean_unsigned_to_nat(0u);
v___y_2146_ = v___x_2155_;
goto v___jp_2145_;
}
v___jp_2133_:
{
lean_object* v___x_2137_; lean_object* v___x_2139_; 
v___x_2137_ = lean_nat_add(v___y_2134_, v___y_2136_);
lean_dec(v___y_2136_);
lean_dec(v___y_2134_);
if (v_isShared_2130_ == 0)
{
lean_ctor_set(v___x_2129_, 4, v_r_1956_);
lean_ctor_set(v___x_2129_, 3, v_r_2124_);
lean_ctor_set(v___x_2129_, 2, v_v_1954_);
lean_ctor_set(v___x_2129_, 1, v_k_1953_);
lean_ctor_set(v___x_2129_, 0, v___x_2137_);
v___x_2139_ = v___x_2129_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v___x_2137_);
lean_ctor_set(v_reuseFailAlloc_2143_, 1, v_k_1953_);
lean_ctor_set(v_reuseFailAlloc_2143_, 2, v_v_1954_);
lean_ctor_set(v_reuseFailAlloc_2143_, 3, v_r_2124_);
lean_ctor_set(v_reuseFailAlloc_2143_, 4, v_r_1956_);
v___x_2139_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
lean_object* v___x_2141_; 
if (v_isShared_2118_ == 0)
{
lean_ctor_set(v___x_2117_, 4, v___x_2139_);
lean_ctor_set(v___x_2117_, 3, v___y_2135_);
lean_ctor_set(v___x_2117_, 2, v_v_2122_);
lean_ctor_set(v___x_2117_, 1, v_k_2121_);
lean_ctor_set(v___x_2117_, 0, v___x_2132_);
v___x_2141_ = v___x_2117_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v___x_2132_);
lean_ctor_set(v_reuseFailAlloc_2142_, 1, v_k_2121_);
lean_ctor_set(v_reuseFailAlloc_2142_, 2, v_v_2122_);
lean_ctor_set(v_reuseFailAlloc_2142_, 3, v___y_2135_);
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
v___jp_2145_:
{
lean_object* v___x_2147_; lean_object* v___x_2149_; 
v___x_2147_ = lean_nat_add(v___x_2144_, v___y_2146_);
lean_dec(v___y_2146_);
lean_dec(v___x_2144_);
if (v_isShared_1959_ == 0)
{
lean_ctor_set(v___x_1958_, 4, v_l_2123_);
lean_ctor_set(v___x_1958_, 3, v_l_2106_);
lean_ctor_set(v___x_1958_, 2, v_v_2105_);
lean_ctor_set(v___x_1958_, 1, v_k_2104_);
lean_ctor_set(v___x_1958_, 0, v___x_2147_);
v___x_2149_ = v___x_1958_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v___x_2147_);
lean_ctor_set(v_reuseFailAlloc_2153_, 1, v_k_2104_);
lean_ctor_set(v_reuseFailAlloc_2153_, 2, v_v_2105_);
lean_ctor_set(v_reuseFailAlloc_2153_, 3, v_l_2106_);
lean_ctor_set(v_reuseFailAlloc_2153_, 4, v_l_2123_);
v___x_2149_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
lean_object* v___x_2150_; 
v___x_2150_ = lean_nat_add(v___x_2101_, v_size_2102_);
if (lean_obj_tag(v_r_2124_) == 0)
{
lean_object* v_size_2151_; 
v_size_2151_ = lean_ctor_get(v_r_2124_, 0);
lean_inc(v_size_2151_);
v___y_2134_ = v___x_2150_;
v___y_2135_ = v___x_2149_;
v___y_2136_ = v_size_2151_;
goto v___jp_2133_;
}
else
{
lean_object* v___x_2152_; 
v___x_2152_ = lean_unsigned_to_nat(0u);
v___y_2134_ = v___x_2150_;
v___y_2135_ = v___x_2149_;
v___y_2136_ = v___x_2152_;
goto v___jp_2133_;
}
}
}
}
}
else
{
lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2167_; 
lean_del_object(v___x_1958_);
v___x_2162_ = lean_nat_add(v___x_2101_, v_size_2103_);
lean_dec(v_size_2103_);
v___x_2163_ = lean_nat_add(v___x_2162_, v_size_2102_);
lean_dec(v___x_2162_);
v___x_2164_ = lean_nat_add(v___x_2101_, v_size_2102_);
v___x_2165_ = lean_nat_add(v___x_2164_, v_size_2120_);
lean_dec(v___x_2164_);
lean_inc_ref(v_r_1956_);
if (v_isShared_2118_ == 0)
{
lean_ctor_set(v___x_2117_, 4, v_r_1956_);
lean_ctor_set(v___x_2117_, 3, v_r_2107_);
lean_ctor_set(v___x_2117_, 2, v_v_1954_);
lean_ctor_set(v___x_2117_, 1, v_k_1953_);
lean_ctor_set(v___x_2117_, 0, v___x_2165_);
v___x_2167_ = v___x_2117_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v___x_2165_);
lean_ctor_set(v_reuseFailAlloc_2180_, 1, v_k_1953_);
lean_ctor_set(v_reuseFailAlloc_2180_, 2, v_v_1954_);
lean_ctor_set(v_reuseFailAlloc_2180_, 3, v_r_2107_);
lean_ctor_set(v_reuseFailAlloc_2180_, 4, v_r_1956_);
v___x_2167_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2174_; 
v_isSharedCheck_2174_ = !lean_is_exclusive(v_r_1956_);
if (v_isSharedCheck_2174_ == 0)
{
lean_object* v_unused_2175_; lean_object* v_unused_2176_; lean_object* v_unused_2177_; lean_object* v_unused_2178_; lean_object* v_unused_2179_; 
v_unused_2175_ = lean_ctor_get(v_r_1956_, 4);
lean_dec(v_unused_2175_);
v_unused_2176_ = lean_ctor_get(v_r_1956_, 3);
lean_dec(v_unused_2176_);
v_unused_2177_ = lean_ctor_get(v_r_1956_, 2);
lean_dec(v_unused_2177_);
v_unused_2178_ = lean_ctor_get(v_r_1956_, 1);
lean_dec(v_unused_2178_);
v_unused_2179_ = lean_ctor_get(v_r_1956_, 0);
lean_dec(v_unused_2179_);
v___x_2169_ = v_r_1956_;
v_isShared_2170_ = v_isSharedCheck_2174_;
goto v_resetjp_2168_;
}
else
{
lean_dec(v_r_1956_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2174_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
lean_object* v___x_2172_; 
if (v_isShared_2170_ == 0)
{
lean_ctor_set(v___x_2169_, 4, v___x_2167_);
lean_ctor_set(v___x_2169_, 3, v_l_2106_);
lean_ctor_set(v___x_2169_, 2, v_v_2105_);
lean_ctor_set(v___x_2169_, 1, v_k_2104_);
lean_ctor_set(v___x_2169_, 0, v___x_2163_);
v___x_2172_ = v___x_2169_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v___x_2163_);
lean_ctor_set(v_reuseFailAlloc_2173_, 1, v_k_2104_);
lean_ctor_set(v_reuseFailAlloc_2173_, 2, v_v_2105_);
lean_ctor_set(v_reuseFailAlloc_2173_, 3, v_l_2106_);
lean_ctor_set(v_reuseFailAlloc_2173_, 4, v___x_2167_);
v___x_2172_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
return v___x_2172_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2187_; 
v_l_2187_ = lean_ctor_get(v_impl_2100_, 3);
lean_inc(v_l_2187_);
if (lean_obj_tag(v_l_2187_) == 0)
{
lean_object* v_r_2188_; lean_object* v_k_2189_; lean_object* v_v_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2201_; 
v_r_2188_ = lean_ctor_get(v_impl_2100_, 4);
v_k_2189_ = lean_ctor_get(v_impl_2100_, 1);
v_v_2190_ = lean_ctor_get(v_impl_2100_, 2);
v_isSharedCheck_2201_ = !lean_is_exclusive(v_impl_2100_);
if (v_isSharedCheck_2201_ == 0)
{
lean_object* v_unused_2202_; lean_object* v_unused_2203_; 
v_unused_2202_ = lean_ctor_get(v_impl_2100_, 3);
lean_dec(v_unused_2202_);
v_unused_2203_ = lean_ctor_get(v_impl_2100_, 0);
lean_dec(v_unused_2203_);
v___x_2192_ = v_impl_2100_;
v_isShared_2193_ = v_isSharedCheck_2201_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_r_2188_);
lean_inc(v_v_2190_);
lean_inc(v_k_2189_);
lean_dec(v_impl_2100_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2201_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2194_; lean_object* v___x_2196_; 
v___x_2194_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2188_);
if (v_isShared_2193_ == 0)
{
lean_ctor_set(v___x_2192_, 3, v_r_2188_);
lean_ctor_set(v___x_2192_, 2, v_v_1954_);
lean_ctor_set(v___x_2192_, 1, v_k_1953_);
lean_ctor_set(v___x_2192_, 0, v___x_2101_);
v___x_2196_ = v___x_2192_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v___x_2101_);
lean_ctor_set(v_reuseFailAlloc_2200_, 1, v_k_1953_);
lean_ctor_set(v_reuseFailAlloc_2200_, 2, v_v_1954_);
lean_ctor_set(v_reuseFailAlloc_2200_, 3, v_r_2188_);
lean_ctor_set(v_reuseFailAlloc_2200_, 4, v_r_2188_);
v___x_2196_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
lean_object* v___x_2198_; 
if (v_isShared_1959_ == 0)
{
lean_ctor_set(v___x_1958_, 4, v___x_2196_);
lean_ctor_set(v___x_1958_, 3, v_l_2187_);
lean_ctor_set(v___x_1958_, 2, v_v_2190_);
lean_ctor_set(v___x_1958_, 1, v_k_2189_);
lean_ctor_set(v___x_1958_, 0, v___x_2194_);
v___x_2198_ = v___x_1958_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v___x_2194_);
lean_ctor_set(v_reuseFailAlloc_2199_, 1, v_k_2189_);
lean_ctor_set(v_reuseFailAlloc_2199_, 2, v_v_2190_);
lean_ctor_set(v_reuseFailAlloc_2199_, 3, v_l_2187_);
lean_ctor_set(v_reuseFailAlloc_2199_, 4, v___x_2196_);
v___x_2198_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
return v___x_2198_;
}
}
}
}
else
{
lean_object* v_r_2204_; 
v_r_2204_ = lean_ctor_get(v_impl_2100_, 4);
lean_inc(v_r_2204_);
if (lean_obj_tag(v_r_2204_) == 0)
{
lean_object* v_k_2205_; lean_object* v_v_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2229_; 
v_k_2205_ = lean_ctor_get(v_impl_2100_, 1);
v_v_2206_ = lean_ctor_get(v_impl_2100_, 2);
v_isSharedCheck_2229_ = !lean_is_exclusive(v_impl_2100_);
if (v_isSharedCheck_2229_ == 0)
{
lean_object* v_unused_2230_; lean_object* v_unused_2231_; lean_object* v_unused_2232_; 
v_unused_2230_ = lean_ctor_get(v_impl_2100_, 4);
lean_dec(v_unused_2230_);
v_unused_2231_ = lean_ctor_get(v_impl_2100_, 3);
lean_dec(v_unused_2231_);
v_unused_2232_ = lean_ctor_get(v_impl_2100_, 0);
lean_dec(v_unused_2232_);
v___x_2208_ = v_impl_2100_;
v_isShared_2209_ = v_isSharedCheck_2229_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_v_2206_);
lean_inc(v_k_2205_);
lean_dec(v_impl_2100_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2229_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v_k_2210_; lean_object* v_v_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2225_; 
v_k_2210_ = lean_ctor_get(v_r_2204_, 1);
v_v_2211_ = lean_ctor_get(v_r_2204_, 2);
v_isSharedCheck_2225_ = !lean_is_exclusive(v_r_2204_);
if (v_isSharedCheck_2225_ == 0)
{
lean_object* v_unused_2226_; lean_object* v_unused_2227_; lean_object* v_unused_2228_; 
v_unused_2226_ = lean_ctor_get(v_r_2204_, 4);
lean_dec(v_unused_2226_);
v_unused_2227_ = lean_ctor_get(v_r_2204_, 3);
lean_dec(v_unused_2227_);
v_unused_2228_ = lean_ctor_get(v_r_2204_, 0);
lean_dec(v_unused_2228_);
v___x_2213_ = v_r_2204_;
v_isShared_2214_ = v_isSharedCheck_2225_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_v_2211_);
lean_inc(v_k_2210_);
lean_dec(v_r_2204_);
v___x_2213_ = lean_box(0);
v_isShared_2214_ = v_isSharedCheck_2225_;
goto v_resetjp_2212_;
}
v_resetjp_2212_:
{
lean_object* v___x_2215_; lean_object* v___x_2217_; 
v___x_2215_ = lean_unsigned_to_nat(3u);
if (v_isShared_2214_ == 0)
{
lean_ctor_set(v___x_2213_, 4, v_l_2187_);
lean_ctor_set(v___x_2213_, 3, v_l_2187_);
lean_ctor_set(v___x_2213_, 2, v_v_2206_);
lean_ctor_set(v___x_2213_, 1, v_k_2205_);
lean_ctor_set(v___x_2213_, 0, v___x_2101_);
v___x_2217_ = v___x_2213_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v___x_2101_);
lean_ctor_set(v_reuseFailAlloc_2224_, 1, v_k_2205_);
lean_ctor_set(v_reuseFailAlloc_2224_, 2, v_v_2206_);
lean_ctor_set(v_reuseFailAlloc_2224_, 3, v_l_2187_);
lean_ctor_set(v_reuseFailAlloc_2224_, 4, v_l_2187_);
v___x_2217_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
lean_object* v___x_2219_; 
if (v_isShared_2209_ == 0)
{
lean_ctor_set(v___x_2208_, 4, v_l_2187_);
lean_ctor_set(v___x_2208_, 2, v_v_1954_);
lean_ctor_set(v___x_2208_, 1, v_k_1953_);
lean_ctor_set(v___x_2208_, 0, v___x_2101_);
v___x_2219_ = v___x_2208_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v___x_2101_);
lean_ctor_set(v_reuseFailAlloc_2223_, 1, v_k_1953_);
lean_ctor_set(v_reuseFailAlloc_2223_, 2, v_v_1954_);
lean_ctor_set(v_reuseFailAlloc_2223_, 3, v_l_2187_);
lean_ctor_set(v_reuseFailAlloc_2223_, 4, v_l_2187_);
v___x_2219_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
lean_object* v___x_2221_; 
if (v_isShared_1959_ == 0)
{
lean_ctor_set(v___x_1958_, 4, v___x_2219_);
lean_ctor_set(v___x_1958_, 3, v___x_2217_);
lean_ctor_set(v___x_1958_, 2, v_v_2211_);
lean_ctor_set(v___x_1958_, 1, v_k_2210_);
lean_ctor_set(v___x_1958_, 0, v___x_2215_);
v___x_2221_ = v___x_1958_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v___x_2215_);
lean_ctor_set(v_reuseFailAlloc_2222_, 1, v_k_2210_);
lean_ctor_set(v_reuseFailAlloc_2222_, 2, v_v_2211_);
lean_ctor_set(v_reuseFailAlloc_2222_, 3, v___x_2217_);
lean_ctor_set(v_reuseFailAlloc_2222_, 4, v___x_2219_);
v___x_2221_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2220_;
}
v_reusejp_2220_:
{
return v___x_2221_;
}
}
}
}
}
}
else
{
lean_object* v___x_2233_; lean_object* v___x_2235_; 
v___x_2233_ = lean_unsigned_to_nat(2u);
if (v_isShared_1959_ == 0)
{
lean_ctor_set(v___x_1958_, 4, v_r_2204_);
lean_ctor_set(v___x_1958_, 3, v_impl_2100_);
lean_ctor_set(v___x_1958_, 0, v___x_2233_);
v___x_2235_ = v___x_1958_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v___x_2233_);
lean_ctor_set(v_reuseFailAlloc_2236_, 1, v_k_1953_);
lean_ctor_set(v_reuseFailAlloc_2236_, 2, v_v_1954_);
lean_ctor_set(v_reuseFailAlloc_2236_, 3, v_impl_2100_);
lean_ctor_set(v_reuseFailAlloc_2236_, 4, v_r_2204_);
v___x_2235_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
return v___x_2235_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2238_; lean_object* v___x_2239_; 
v___x_2238_ = lean_unsigned_to_nat(1u);
v___x_2239_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2239_, 0, v___x_2238_);
lean_ctor_set(v___x_2239_, 1, v_k_1949_);
lean_ctor_set(v___x_2239_, 2, v_v_1950_);
lean_ctor_set(v___x_2239_, 3, v_t_1951_);
lean_ctor_set(v___x_2239_, 4, v_t_1951_);
return v___x_2239_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2___redArg(lean_object* v_y_2240_, lean_object* v_x_2241_, size_t v_x_2242_, size_t v_x_2243_){
_start:
{
if (lean_obj_tag(v_x_2241_) == 0)
{
lean_object* v_cs_2244_; size_t v_j_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; uint8_t v___x_2248_; 
v_cs_2244_ = lean_ctor_get(v_x_2241_, 0);
v_j_2245_ = lean_usize_shift_right(v_x_2242_, v_x_2243_);
v___x_2246_ = lean_usize_to_nat(v_j_2245_);
v___x_2247_ = lean_array_get_size(v_cs_2244_);
v___x_2248_ = lean_nat_dec_lt(v___x_2246_, v___x_2247_);
if (v___x_2248_ == 0)
{
lean_dec(v___x_2246_);
lean_dec(v_y_2240_);
return v_x_2241_;
}
else
{
lean_object* v___x_2250_; uint8_t v_isShared_2251_; uint8_t v_isSharedCheck_2266_; 
lean_inc_ref(v_cs_2244_);
v_isSharedCheck_2266_ = !lean_is_exclusive(v_x_2241_);
if (v_isSharedCheck_2266_ == 0)
{
lean_object* v_unused_2267_; 
v_unused_2267_ = lean_ctor_get(v_x_2241_, 0);
lean_dec(v_unused_2267_);
v___x_2250_ = v_x_2241_;
v_isShared_2251_ = v_isSharedCheck_2266_;
goto v_resetjp_2249_;
}
else
{
lean_dec(v_x_2241_);
v___x_2250_ = lean_box(0);
v_isShared_2251_ = v_isSharedCheck_2266_;
goto v_resetjp_2249_;
}
v_resetjp_2249_:
{
size_t v___x_2252_; size_t v___x_2253_; size_t v___x_2254_; size_t v_i_2255_; size_t v___x_2256_; size_t v_shift_2257_; lean_object* v_v_2258_; lean_object* v___x_2259_; lean_object* v_xs_x27_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2264_; 
v___x_2252_ = ((size_t)1ULL);
v___x_2253_ = lean_usize_shift_left(v___x_2252_, v_x_2243_);
v___x_2254_ = lean_usize_sub(v___x_2253_, v___x_2252_);
v_i_2255_ = lean_usize_land(v_x_2242_, v___x_2254_);
v___x_2256_ = ((size_t)5ULL);
v_shift_2257_ = lean_usize_sub(v_x_2243_, v___x_2256_);
v_v_2258_ = lean_array_fget(v_cs_2244_, v___x_2246_);
v___x_2259_ = lean_box(0);
v_xs_x27_2260_ = lean_array_fset(v_cs_2244_, v___x_2246_, v___x_2259_);
v___x_2261_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2___redArg(v_y_2240_, v_v_2258_, v_i_2255_, v_shift_2257_);
v___x_2262_ = lean_array_fset(v_xs_x27_2260_, v___x_2246_, v___x_2261_);
lean_dec(v___x_2246_);
if (v_isShared_2251_ == 0)
{
lean_ctor_set(v___x_2250_, 0, v___x_2262_);
v___x_2264_ = v___x_2250_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v___x_2262_);
v___x_2264_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
return v___x_2264_;
}
}
}
}
else
{
lean_object* v_vs_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; uint8_t v___x_2271_; 
v_vs_2268_ = lean_ctor_get(v_x_2241_, 0);
v___x_2269_ = lean_usize_to_nat(v_x_2242_);
v___x_2270_ = lean_array_get_size(v_vs_2268_);
v___x_2271_ = lean_nat_dec_lt(v___x_2269_, v___x_2270_);
if (v___x_2271_ == 0)
{
lean_dec(v___x_2269_);
lean_dec(v_y_2240_);
return v_x_2241_;
}
else
{
lean_object* v___x_2273_; uint8_t v_isShared_2274_; uint8_t v_isSharedCheck_2286_; 
lean_inc_ref(v_vs_2268_);
v_isSharedCheck_2286_ = !lean_is_exclusive(v_x_2241_);
if (v_isSharedCheck_2286_ == 0)
{
lean_object* v_unused_2287_; 
v_unused_2287_ = lean_ctor_get(v_x_2241_, 0);
lean_dec(v_unused_2287_);
v___x_2273_ = v_x_2241_;
v_isShared_2274_ = v_isSharedCheck_2286_;
goto v_resetjp_2272_;
}
else
{
lean_dec(v_x_2241_);
v___x_2273_ = lean_box(0);
v_isShared_2274_ = v_isSharedCheck_2286_;
goto v_resetjp_2272_;
}
v_resetjp_2272_:
{
lean_object* v_v_2275_; lean_object* v___x_2276_; lean_object* v_xs_x27_2277_; lean_object* v___y_2279_; uint8_t v___x_2284_; 
v_v_2275_ = lean_array_fget(v_vs_2268_, v___x_2269_);
v___x_2276_ = lean_box(0);
v_xs_x27_2277_ = lean_array_fset(v_vs_2268_, v___x_2269_, v___x_2276_);
v___x_2284_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg(v_y_2240_, v_v_2275_);
if (v___x_2284_ == 0)
{
lean_object* v___x_2285_; 
v___x_2285_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1___redArg(v_y_2240_, v___x_2276_, v_v_2275_);
v___y_2279_ = v___x_2285_;
goto v___jp_2278_;
}
else
{
lean_dec(v_y_2240_);
v___y_2279_ = v_v_2275_;
goto v___jp_2278_;
}
v___jp_2278_:
{
lean_object* v___x_2280_; lean_object* v___x_2282_; 
v___x_2280_ = lean_array_fset(v_xs_x27_2277_, v___x_2269_, v___y_2279_);
lean_dec(v___x_2269_);
if (v_isShared_2274_ == 0)
{
lean_ctor_set(v___x_2273_, 0, v___x_2280_);
v___x_2282_ = v___x_2273_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2283_; 
v_reuseFailAlloc_2283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2283_, 0, v___x_2280_);
v___x_2282_ = v_reuseFailAlloc_2283_;
goto v_reusejp_2281_;
}
v_reusejp_2281_:
{
return v___x_2282_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2___redArg___boxed(lean_object* v_y_2288_, lean_object* v_x_2289_, lean_object* v_x_2290_, lean_object* v_x_2291_){
_start:
{
size_t v_x_6121__boxed_2292_; size_t v_x_6122__boxed_2293_; lean_object* v_res_2294_; 
v_x_6121__boxed_2292_ = lean_unbox_usize(v_x_2290_);
lean_dec(v_x_2290_);
v_x_6122__boxed_2293_ = lean_unbox_usize(v_x_2291_);
lean_dec(v_x_2291_);
v_res_2294_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2___redArg(v_y_2288_, v_x_2289_, v_x_6121__boxed_2292_, v_x_6122__boxed_2293_);
return v_res_2294_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2(lean_object* v_y_2295_, lean_object* v_inst_2296_, lean_object* v_t_2297_, lean_object* v_i_2298_){
_start:
{
lean_object* v_root_2299_; lean_object* v_tail_2300_; lean_object* v_size_2301_; size_t v_shift_2302_; lean_object* v_tailOff_2303_; lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2330_; 
v_root_2299_ = lean_ctor_get(v_t_2297_, 0);
v_tail_2300_ = lean_ctor_get(v_t_2297_, 1);
v_size_2301_ = lean_ctor_get(v_t_2297_, 2);
v_shift_2302_ = lean_ctor_get_usize(v_t_2297_, 4);
v_tailOff_2303_ = lean_ctor_get(v_t_2297_, 3);
v_isSharedCheck_2330_ = !lean_is_exclusive(v_t_2297_);
if (v_isSharedCheck_2330_ == 0)
{
v___x_2305_ = v_t_2297_;
v_isShared_2306_ = v_isSharedCheck_2330_;
goto v_resetjp_2304_;
}
else
{
lean_inc(v_tailOff_2303_);
lean_inc(v_size_2301_);
lean_inc(v_tail_2300_);
lean_inc(v_root_2299_);
lean_dec(v_t_2297_);
v___x_2305_ = lean_box(0);
v_isShared_2306_ = v_isSharedCheck_2330_;
goto v_resetjp_2304_;
}
v_resetjp_2304_:
{
uint8_t v___x_2307_; 
v___x_2307_ = lean_nat_dec_le(v_tailOff_2303_, v_i_2298_);
if (v___x_2307_ == 0)
{
size_t v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2311_; 
v___x_2308_ = lean_usize_of_nat(v_i_2298_);
v___x_2309_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2___redArg(v_y_2295_, v_root_2299_, v___x_2308_, v_shift_2302_);
if (v_isShared_2306_ == 0)
{
lean_ctor_set(v___x_2305_, 0, v___x_2309_);
v___x_2311_ = v___x_2305_;
goto v_reusejp_2310_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v___x_2309_);
lean_ctor_set(v_reuseFailAlloc_2312_, 1, v_tail_2300_);
lean_ctor_set(v_reuseFailAlloc_2312_, 2, v_size_2301_);
lean_ctor_set(v_reuseFailAlloc_2312_, 3, v_tailOff_2303_);
lean_ctor_set_usize(v_reuseFailAlloc_2312_, 4, v_shift_2302_);
v___x_2311_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2310_;
}
v_reusejp_2310_:
{
return v___x_2311_;
}
}
else
{
lean_object* v___x_2313_; lean_object* v___x_2314_; uint8_t v___x_2315_; 
v___x_2313_ = lean_nat_sub(v_i_2298_, v_tailOff_2303_);
v___x_2314_ = lean_array_get_size(v_tail_2300_);
v___x_2315_ = lean_nat_dec_lt(v___x_2313_, v___x_2314_);
if (v___x_2315_ == 0)
{
lean_object* v___x_2317_; 
lean_dec(v___x_2313_);
lean_dec(v_y_2295_);
if (v_isShared_2306_ == 0)
{
v___x_2317_ = v___x_2305_;
goto v_reusejp_2316_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v_root_2299_);
lean_ctor_set(v_reuseFailAlloc_2318_, 1, v_tail_2300_);
lean_ctor_set(v_reuseFailAlloc_2318_, 2, v_size_2301_);
lean_ctor_set(v_reuseFailAlloc_2318_, 3, v_tailOff_2303_);
lean_ctor_set_usize(v_reuseFailAlloc_2318_, 4, v_shift_2302_);
v___x_2317_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2316_;
}
v_reusejp_2316_:
{
return v___x_2317_;
}
}
else
{
lean_object* v_v_2319_; lean_object* v___x_2320_; lean_object* v_xs_x27_2321_; lean_object* v___y_2323_; uint8_t v___x_2328_; 
v_v_2319_ = lean_array_fget(v_tail_2300_, v___x_2313_);
v___x_2320_ = lean_box(0);
v_xs_x27_2321_ = lean_array_fset(v_tail_2300_, v___x_2313_, v___x_2320_);
v___x_2328_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg(v_y_2295_, v_v_2319_);
if (v___x_2328_ == 0)
{
lean_object* v___x_2329_; 
v___x_2329_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1___redArg(v_y_2295_, v___x_2320_, v_v_2319_);
v___y_2323_ = v___x_2329_;
goto v___jp_2322_;
}
else
{
lean_dec(v_y_2295_);
v___y_2323_ = v_v_2319_;
goto v___jp_2322_;
}
v___jp_2322_:
{
lean_object* v___x_2324_; lean_object* v___x_2326_; 
v___x_2324_ = lean_array_fset(v_xs_x27_2321_, v___x_2313_, v___y_2323_);
lean_dec(v___x_2313_);
if (v_isShared_2306_ == 0)
{
lean_ctor_set(v___x_2305_, 1, v___x_2324_);
v___x_2326_ = v___x_2305_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v_root_2299_);
lean_ctor_set(v_reuseFailAlloc_2327_, 1, v___x_2324_);
lean_ctor_set(v_reuseFailAlloc_2327_, 2, v_size_2301_);
lean_ctor_set(v_reuseFailAlloc_2327_, 3, v_tailOff_2303_);
lean_ctor_set_usize(v_reuseFailAlloc_2327_, 4, v_shift_2302_);
v___x_2326_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
return v___x_2326_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2___boxed(lean_object* v_y_2331_, lean_object* v_inst_2332_, lean_object* v_t_2333_, lean_object* v_i_2334_){
_start:
{
lean_object* v_res_2335_; 
v_res_2335_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2(v_y_2331_, v_inst_2332_, v_t_2333_, v_i_2334_);
lean_dec(v_i_2334_);
lean_dec(v_inst_2332_);
return v_res_2335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_addOcc___lam__0(lean_object* v_a_2336_, lean_object* v_y_2337_, lean_object* v_x_2338_, lean_object* v_s_2339_){
_start:
{
lean_object* v_structs_2340_; lean_object* v_typeIdOf_2341_; lean_object* v_exprToStructId_2342_; lean_object* v_exprToStructIdEntries_2343_; lean_object* v_forbiddenNatModules_2344_; lean_object* v_natStructs_2345_; lean_object* v_natTypeIdOf_2346_; lean_object* v_exprToNatStructId_2347_; lean_object* v___x_2348_; uint8_t v___x_2349_; 
v_structs_2340_ = lean_ctor_get(v_s_2339_, 0);
v_typeIdOf_2341_ = lean_ctor_get(v_s_2339_, 1);
v_exprToStructId_2342_ = lean_ctor_get(v_s_2339_, 2);
v_exprToStructIdEntries_2343_ = lean_ctor_get(v_s_2339_, 3);
v_forbiddenNatModules_2344_ = lean_ctor_get(v_s_2339_, 4);
v_natStructs_2345_ = lean_ctor_get(v_s_2339_, 5);
v_natTypeIdOf_2346_ = lean_ctor_get(v_s_2339_, 6);
v_exprToNatStructId_2347_ = lean_ctor_get(v_s_2339_, 7);
v___x_2348_ = lean_array_get_size(v_structs_2340_);
v___x_2349_ = lean_nat_dec_lt(v_a_2336_, v___x_2348_);
if (v___x_2349_ == 0)
{
lean_dec(v_y_2337_);
return v_s_2339_;
}
else
{
lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2412_; 
lean_inc_ref(v_exprToNatStructId_2347_);
lean_inc_ref(v_natTypeIdOf_2346_);
lean_inc_ref(v_natStructs_2345_);
lean_inc_ref(v_forbiddenNatModules_2344_);
lean_inc_ref(v_exprToStructIdEntries_2343_);
lean_inc_ref(v_exprToStructId_2342_);
lean_inc_ref(v_typeIdOf_2341_);
lean_inc_ref(v_structs_2340_);
v_isSharedCheck_2412_ = !lean_is_exclusive(v_s_2339_);
if (v_isSharedCheck_2412_ == 0)
{
lean_object* v_unused_2413_; lean_object* v_unused_2414_; lean_object* v_unused_2415_; lean_object* v_unused_2416_; lean_object* v_unused_2417_; lean_object* v_unused_2418_; lean_object* v_unused_2419_; lean_object* v_unused_2420_; 
v_unused_2413_ = lean_ctor_get(v_s_2339_, 7);
lean_dec(v_unused_2413_);
v_unused_2414_ = lean_ctor_get(v_s_2339_, 6);
lean_dec(v_unused_2414_);
v_unused_2415_ = lean_ctor_get(v_s_2339_, 5);
lean_dec(v_unused_2415_);
v_unused_2416_ = lean_ctor_get(v_s_2339_, 4);
lean_dec(v_unused_2416_);
v_unused_2417_ = lean_ctor_get(v_s_2339_, 3);
lean_dec(v_unused_2417_);
v_unused_2418_ = lean_ctor_get(v_s_2339_, 2);
lean_dec(v_unused_2418_);
v_unused_2419_ = lean_ctor_get(v_s_2339_, 1);
lean_dec(v_unused_2419_);
v_unused_2420_ = lean_ctor_get(v_s_2339_, 0);
lean_dec(v_unused_2420_);
v___x_2351_ = v_s_2339_;
v_isShared_2352_ = v_isSharedCheck_2412_;
goto v_resetjp_2350_;
}
else
{
lean_dec(v_s_2339_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2412_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v_v_2353_; lean_object* v_id_2354_; lean_object* v_ringId_x3f_2355_; lean_object* v_type_2356_; lean_object* v_u_2357_; lean_object* v_intModuleInst_2358_; lean_object* v_leInst_x3f_2359_; lean_object* v_ltInst_x3f_2360_; lean_object* v_lawfulOrderLTInst_x3f_2361_; lean_object* v_isPreorderInst_x3f_2362_; lean_object* v_orderedAddInst_x3f_2363_; lean_object* v_isLinearInst_x3f_2364_; lean_object* v_noNatDivInst_x3f_2365_; lean_object* v_ringInst_x3f_2366_; lean_object* v_commRingInst_x3f_2367_; lean_object* v_orderedRingInst_x3f_2368_; lean_object* v_fieldInst_x3f_2369_; lean_object* v_charInst_x3f_2370_; lean_object* v_zero_2371_; lean_object* v_ofNatZero_2372_; lean_object* v_one_x3f_2373_; lean_object* v_leFn_x3f_2374_; lean_object* v_ltFn_x3f_2375_; lean_object* v_addFn_2376_; lean_object* v_zsmulFn_2377_; lean_object* v_nsmulFn_2378_; lean_object* v_zsmulFn_x3f_2379_; lean_object* v_nsmulFn_x3f_2380_; lean_object* v_homomulFn_x3f_2381_; lean_object* v_subFn_2382_; lean_object* v_negFn_2383_; lean_object* v_vars_2384_; lean_object* v_varMap_2385_; lean_object* v_lowers_2386_; lean_object* v_uppers_2387_; lean_object* v_diseqs_2388_; lean_object* v_assignment_2389_; uint8_t v_caseSplits_2390_; lean_object* v_conflict_x3f_2391_; lean_object* v_diseqSplits_2392_; lean_object* v_elimEqs_2393_; lean_object* v_elimStack_2394_; lean_object* v_occurs_2395_; lean_object* v_ignored_2396_; lean_object* v___x_2398_; uint8_t v_isShared_2399_; uint8_t v_isSharedCheck_2411_; 
v_v_2353_ = lean_array_fget(v_structs_2340_, v_a_2336_);
v_id_2354_ = lean_ctor_get(v_v_2353_, 0);
v_ringId_x3f_2355_ = lean_ctor_get(v_v_2353_, 1);
v_type_2356_ = lean_ctor_get(v_v_2353_, 2);
v_u_2357_ = lean_ctor_get(v_v_2353_, 3);
v_intModuleInst_2358_ = lean_ctor_get(v_v_2353_, 4);
v_leInst_x3f_2359_ = lean_ctor_get(v_v_2353_, 5);
v_ltInst_x3f_2360_ = lean_ctor_get(v_v_2353_, 6);
v_lawfulOrderLTInst_x3f_2361_ = lean_ctor_get(v_v_2353_, 7);
v_isPreorderInst_x3f_2362_ = lean_ctor_get(v_v_2353_, 8);
v_orderedAddInst_x3f_2363_ = lean_ctor_get(v_v_2353_, 9);
v_isLinearInst_x3f_2364_ = lean_ctor_get(v_v_2353_, 10);
v_noNatDivInst_x3f_2365_ = lean_ctor_get(v_v_2353_, 11);
v_ringInst_x3f_2366_ = lean_ctor_get(v_v_2353_, 12);
v_commRingInst_x3f_2367_ = lean_ctor_get(v_v_2353_, 13);
v_orderedRingInst_x3f_2368_ = lean_ctor_get(v_v_2353_, 14);
v_fieldInst_x3f_2369_ = lean_ctor_get(v_v_2353_, 15);
v_charInst_x3f_2370_ = lean_ctor_get(v_v_2353_, 16);
v_zero_2371_ = lean_ctor_get(v_v_2353_, 17);
v_ofNatZero_2372_ = lean_ctor_get(v_v_2353_, 18);
v_one_x3f_2373_ = lean_ctor_get(v_v_2353_, 19);
v_leFn_x3f_2374_ = lean_ctor_get(v_v_2353_, 20);
v_ltFn_x3f_2375_ = lean_ctor_get(v_v_2353_, 21);
v_addFn_2376_ = lean_ctor_get(v_v_2353_, 22);
v_zsmulFn_2377_ = lean_ctor_get(v_v_2353_, 23);
v_nsmulFn_2378_ = lean_ctor_get(v_v_2353_, 24);
v_zsmulFn_x3f_2379_ = lean_ctor_get(v_v_2353_, 25);
v_nsmulFn_x3f_2380_ = lean_ctor_get(v_v_2353_, 26);
v_homomulFn_x3f_2381_ = lean_ctor_get(v_v_2353_, 27);
v_subFn_2382_ = lean_ctor_get(v_v_2353_, 28);
v_negFn_2383_ = lean_ctor_get(v_v_2353_, 29);
v_vars_2384_ = lean_ctor_get(v_v_2353_, 30);
v_varMap_2385_ = lean_ctor_get(v_v_2353_, 31);
v_lowers_2386_ = lean_ctor_get(v_v_2353_, 32);
v_uppers_2387_ = lean_ctor_get(v_v_2353_, 33);
v_diseqs_2388_ = lean_ctor_get(v_v_2353_, 34);
v_assignment_2389_ = lean_ctor_get(v_v_2353_, 35);
v_caseSplits_2390_ = lean_ctor_get_uint8(v_v_2353_, sizeof(void*)*42);
v_conflict_x3f_2391_ = lean_ctor_get(v_v_2353_, 36);
v_diseqSplits_2392_ = lean_ctor_get(v_v_2353_, 37);
v_elimEqs_2393_ = lean_ctor_get(v_v_2353_, 38);
v_elimStack_2394_ = lean_ctor_get(v_v_2353_, 39);
v_occurs_2395_ = lean_ctor_get(v_v_2353_, 40);
v_ignored_2396_ = lean_ctor_get(v_v_2353_, 41);
v_isSharedCheck_2411_ = !lean_is_exclusive(v_v_2353_);
if (v_isSharedCheck_2411_ == 0)
{
v___x_2398_ = v_v_2353_;
v_isShared_2399_ = v_isSharedCheck_2411_;
goto v_resetjp_2397_;
}
else
{
lean_inc(v_ignored_2396_);
lean_inc(v_occurs_2395_);
lean_inc(v_elimStack_2394_);
lean_inc(v_elimEqs_2393_);
lean_inc(v_diseqSplits_2392_);
lean_inc(v_conflict_x3f_2391_);
lean_inc(v_assignment_2389_);
lean_inc(v_diseqs_2388_);
lean_inc(v_uppers_2387_);
lean_inc(v_lowers_2386_);
lean_inc(v_varMap_2385_);
lean_inc(v_vars_2384_);
lean_inc(v_negFn_2383_);
lean_inc(v_subFn_2382_);
lean_inc(v_homomulFn_x3f_2381_);
lean_inc(v_nsmulFn_x3f_2380_);
lean_inc(v_zsmulFn_x3f_2379_);
lean_inc(v_nsmulFn_2378_);
lean_inc(v_zsmulFn_2377_);
lean_inc(v_addFn_2376_);
lean_inc(v_ltFn_x3f_2375_);
lean_inc(v_leFn_x3f_2374_);
lean_inc(v_one_x3f_2373_);
lean_inc(v_ofNatZero_2372_);
lean_inc(v_zero_2371_);
lean_inc(v_charInst_x3f_2370_);
lean_inc(v_fieldInst_x3f_2369_);
lean_inc(v_orderedRingInst_x3f_2368_);
lean_inc(v_commRingInst_x3f_2367_);
lean_inc(v_ringInst_x3f_2366_);
lean_inc(v_noNatDivInst_x3f_2365_);
lean_inc(v_isLinearInst_x3f_2364_);
lean_inc(v_orderedAddInst_x3f_2363_);
lean_inc(v_isPreorderInst_x3f_2362_);
lean_inc(v_lawfulOrderLTInst_x3f_2361_);
lean_inc(v_ltInst_x3f_2360_);
lean_inc(v_leInst_x3f_2359_);
lean_inc(v_intModuleInst_2358_);
lean_inc(v_u_2357_);
lean_inc(v_type_2356_);
lean_inc(v_ringId_x3f_2355_);
lean_inc(v_id_2354_);
lean_dec(v_v_2353_);
v___x_2398_ = lean_box(0);
v_isShared_2399_ = v_isSharedCheck_2411_;
goto v_resetjp_2397_;
}
v_resetjp_2397_:
{
lean_object* v___x_2400_; lean_object* v_xs_x27_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2405_; 
v___x_2400_ = lean_box(0);
v_xs_x27_2401_ = lean_array_fset(v_structs_2340_, v_a_2336_, v___x_2400_);
v___x_2402_ = lean_box(1);
v___x_2403_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2(v_y_2337_, v___x_2402_, v_occurs_2395_, v_x_2338_);
if (v_isShared_2399_ == 0)
{
lean_ctor_set(v___x_2398_, 40, v___x_2403_);
v___x_2405_ = v___x_2398_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(0, 42, 1);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v_id_2354_);
lean_ctor_set(v_reuseFailAlloc_2410_, 1, v_ringId_x3f_2355_);
lean_ctor_set(v_reuseFailAlloc_2410_, 2, v_type_2356_);
lean_ctor_set(v_reuseFailAlloc_2410_, 3, v_u_2357_);
lean_ctor_set(v_reuseFailAlloc_2410_, 4, v_intModuleInst_2358_);
lean_ctor_set(v_reuseFailAlloc_2410_, 5, v_leInst_x3f_2359_);
lean_ctor_set(v_reuseFailAlloc_2410_, 6, v_ltInst_x3f_2360_);
lean_ctor_set(v_reuseFailAlloc_2410_, 7, v_lawfulOrderLTInst_x3f_2361_);
lean_ctor_set(v_reuseFailAlloc_2410_, 8, v_isPreorderInst_x3f_2362_);
lean_ctor_set(v_reuseFailAlloc_2410_, 9, v_orderedAddInst_x3f_2363_);
lean_ctor_set(v_reuseFailAlloc_2410_, 10, v_isLinearInst_x3f_2364_);
lean_ctor_set(v_reuseFailAlloc_2410_, 11, v_noNatDivInst_x3f_2365_);
lean_ctor_set(v_reuseFailAlloc_2410_, 12, v_ringInst_x3f_2366_);
lean_ctor_set(v_reuseFailAlloc_2410_, 13, v_commRingInst_x3f_2367_);
lean_ctor_set(v_reuseFailAlloc_2410_, 14, v_orderedRingInst_x3f_2368_);
lean_ctor_set(v_reuseFailAlloc_2410_, 15, v_fieldInst_x3f_2369_);
lean_ctor_set(v_reuseFailAlloc_2410_, 16, v_charInst_x3f_2370_);
lean_ctor_set(v_reuseFailAlloc_2410_, 17, v_zero_2371_);
lean_ctor_set(v_reuseFailAlloc_2410_, 18, v_ofNatZero_2372_);
lean_ctor_set(v_reuseFailAlloc_2410_, 19, v_one_x3f_2373_);
lean_ctor_set(v_reuseFailAlloc_2410_, 20, v_leFn_x3f_2374_);
lean_ctor_set(v_reuseFailAlloc_2410_, 21, v_ltFn_x3f_2375_);
lean_ctor_set(v_reuseFailAlloc_2410_, 22, v_addFn_2376_);
lean_ctor_set(v_reuseFailAlloc_2410_, 23, v_zsmulFn_2377_);
lean_ctor_set(v_reuseFailAlloc_2410_, 24, v_nsmulFn_2378_);
lean_ctor_set(v_reuseFailAlloc_2410_, 25, v_zsmulFn_x3f_2379_);
lean_ctor_set(v_reuseFailAlloc_2410_, 26, v_nsmulFn_x3f_2380_);
lean_ctor_set(v_reuseFailAlloc_2410_, 27, v_homomulFn_x3f_2381_);
lean_ctor_set(v_reuseFailAlloc_2410_, 28, v_subFn_2382_);
lean_ctor_set(v_reuseFailAlloc_2410_, 29, v_negFn_2383_);
lean_ctor_set(v_reuseFailAlloc_2410_, 30, v_vars_2384_);
lean_ctor_set(v_reuseFailAlloc_2410_, 31, v_varMap_2385_);
lean_ctor_set(v_reuseFailAlloc_2410_, 32, v_lowers_2386_);
lean_ctor_set(v_reuseFailAlloc_2410_, 33, v_uppers_2387_);
lean_ctor_set(v_reuseFailAlloc_2410_, 34, v_diseqs_2388_);
lean_ctor_set(v_reuseFailAlloc_2410_, 35, v_assignment_2389_);
lean_ctor_set(v_reuseFailAlloc_2410_, 36, v_conflict_x3f_2391_);
lean_ctor_set(v_reuseFailAlloc_2410_, 37, v_diseqSplits_2392_);
lean_ctor_set(v_reuseFailAlloc_2410_, 38, v_elimEqs_2393_);
lean_ctor_set(v_reuseFailAlloc_2410_, 39, v_elimStack_2394_);
lean_ctor_set(v_reuseFailAlloc_2410_, 40, v___x_2403_);
lean_ctor_set(v_reuseFailAlloc_2410_, 41, v_ignored_2396_);
lean_ctor_set_uint8(v_reuseFailAlloc_2410_, sizeof(void*)*42, v_caseSplits_2390_);
v___x_2405_ = v_reuseFailAlloc_2410_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
lean_object* v___x_2406_; lean_object* v___x_2408_; 
v___x_2406_ = lean_array_fset(v_xs_x27_2401_, v_a_2336_, v___x_2405_);
if (v_isShared_2352_ == 0)
{
lean_ctor_set(v___x_2351_, 0, v___x_2406_);
v___x_2408_ = v___x_2351_;
goto v_reusejp_2407_;
}
else
{
lean_object* v_reuseFailAlloc_2409_; 
v_reuseFailAlloc_2409_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_2409_, 0, v___x_2406_);
lean_ctor_set(v_reuseFailAlloc_2409_, 1, v_typeIdOf_2341_);
lean_ctor_set(v_reuseFailAlloc_2409_, 2, v_exprToStructId_2342_);
lean_ctor_set(v_reuseFailAlloc_2409_, 3, v_exprToStructIdEntries_2343_);
lean_ctor_set(v_reuseFailAlloc_2409_, 4, v_forbiddenNatModules_2344_);
lean_ctor_set(v_reuseFailAlloc_2409_, 5, v_natStructs_2345_);
lean_ctor_set(v_reuseFailAlloc_2409_, 6, v_natTypeIdOf_2346_);
lean_ctor_set(v_reuseFailAlloc_2409_, 7, v_exprToNatStructId_2347_);
v___x_2408_ = v_reuseFailAlloc_2409_;
goto v_reusejp_2407_;
}
v_reusejp_2407_:
{
return v___x_2408_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_addOcc___lam__0___boxed(lean_object* v_a_2421_, lean_object* v_y_2422_, lean_object* v_x_2423_, lean_object* v_s_2424_){
_start:
{
lean_object* v_res_2425_; 
v_res_2425_ = l_Lean_Meta_Grind_Arith_Linear_addOcc___lam__0(v_a_2421_, v_y_2422_, v_x_2423_, v_s_2424_);
lean_dec(v_x_2423_);
lean_dec(v_a_2421_);
return v_res_2425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_addOcc(lean_object* v_x_2426_, lean_object* v_y_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_){
_start:
{
lean_object* v___x_2440_; 
v___x_2440_ = l_Lean_Meta_Grind_Arith_Linear_getOccursOf(v_x_2426_, v_a_2428_, v_a_2429_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_, v_a_2438_);
if (lean_obj_tag(v___x_2440_) == 0)
{
lean_object* v_a_2441_; lean_object* v___x_2443_; uint8_t v_isShared_2444_; uint8_t v_isSharedCheck_2453_; 
v_a_2441_ = lean_ctor_get(v___x_2440_, 0);
v_isSharedCheck_2453_ = !lean_is_exclusive(v___x_2440_);
if (v_isSharedCheck_2453_ == 0)
{
v___x_2443_ = v___x_2440_;
v_isShared_2444_ = v_isSharedCheck_2453_;
goto v_resetjp_2442_;
}
else
{
lean_inc(v_a_2441_);
lean_dec(v___x_2440_);
v___x_2443_ = lean_box(0);
v_isShared_2444_ = v_isSharedCheck_2453_;
goto v_resetjp_2442_;
}
v_resetjp_2442_:
{
uint8_t v___x_2445_; 
v___x_2445_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg(v_y_2427_, v_a_2441_);
lean_dec(v_a_2441_);
if (v___x_2445_ == 0)
{
lean_object* v___f_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; 
lean_del_object(v___x_2443_);
v___f_2446_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Linear_addOcc___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2446_, 0, v_a_2428_);
lean_closure_set(v___f_2446_, 1, v_y_2427_);
lean_closure_set(v___f_2446_, 2, v_x_2426_);
v___x_2447_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
v___x_2448_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2447_, v___f_2446_, v_a_2429_);
return v___x_2448_;
}
else
{
lean_object* v___x_2449_; lean_object* v___x_2451_; 
lean_dec(v_a_2428_);
lean_dec(v_y_2427_);
lean_dec(v_x_2426_);
v___x_2449_ = lean_box(0);
if (v_isShared_2444_ == 0)
{
lean_ctor_set(v___x_2443_, 0, v___x_2449_);
v___x_2451_ = v___x_2443_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v___x_2449_);
v___x_2451_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2450_;
}
v_reusejp_2450_:
{
return v___x_2451_;
}
}
}
}
else
{
lean_object* v_a_2454_; lean_object* v___x_2456_; uint8_t v_isShared_2457_; uint8_t v_isSharedCheck_2461_; 
lean_dec(v_a_2428_);
lean_dec(v_y_2427_);
lean_dec(v_x_2426_);
v_a_2454_ = lean_ctor_get(v___x_2440_, 0);
v_isSharedCheck_2461_ = !lean_is_exclusive(v___x_2440_);
if (v_isSharedCheck_2461_ == 0)
{
v___x_2456_ = v___x_2440_;
v_isShared_2457_ = v_isSharedCheck_2461_;
goto v_resetjp_2455_;
}
else
{
lean_inc(v_a_2454_);
lean_dec(v___x_2440_);
v___x_2456_ = lean_box(0);
v_isShared_2457_ = v_isSharedCheck_2461_;
goto v_resetjp_2455_;
}
v_resetjp_2455_:
{
lean_object* v___x_2459_; 
if (v_isShared_2457_ == 0)
{
v___x_2459_ = v___x_2456_;
goto v_reusejp_2458_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v_a_2454_);
v___x_2459_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2458_;
}
v_reusejp_2458_:
{
return v___x_2459_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_addOcc___boxed(lean_object* v_x_2462_, lean_object* v_y_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_){
_start:
{
lean_object* v_res_2476_; 
v_res_2476_ = l_Lean_Meta_Grind_Arith_Linear_addOcc(v_x_2462_, v_y_2463_, v_a_2464_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_, v_a_2474_);
lean_dec(v_a_2474_);
lean_dec_ref(v_a_2473_);
lean_dec(v_a_2472_);
lean_dec_ref(v_a_2471_);
lean_dec(v_a_2470_);
lean_dec_ref(v_a_2469_);
lean_dec(v_a_2468_);
lean_dec_ref(v_a_2467_);
lean_dec(v_a_2466_);
lean_dec(v_a_2465_);
return v_res_2476_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0(lean_object* v_00_u03b2_2477_, lean_object* v_k_2478_, lean_object* v_t_2479_){
_start:
{
uint8_t v___x_2480_; 
v___x_2480_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___redArg(v_k_2478_, v_t_2479_);
return v___x_2480_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0___boxed(lean_object* v_00_u03b2_2481_, lean_object* v_k_2482_, lean_object* v_t_2483_){
_start:
{
uint8_t v_res_2484_; lean_object* v_r_2485_; 
v_res_2484_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__0(v_00_u03b2_2481_, v_k_2482_, v_t_2483_);
lean_dec(v_t_2483_);
lean_dec(v_k_2482_);
v_r_2485_ = lean_box(v_res_2484_);
return v_r_2485_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1(lean_object* v_00_u03b2_2486_, lean_object* v_k_2487_, lean_object* v_v_2488_, lean_object* v_t_2489_, lean_object* v_hl_2490_){
_start:
{
lean_object* v___x_2491_; 
v___x_2491_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__1___redArg(v_k_2487_, v_v_2488_, v_t_2489_);
return v___x_2491_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2(lean_object* v_y_2492_, lean_object* v_inst_2493_, lean_object* v_x_2494_, size_t v_x_2495_, size_t v_x_2496_){
_start:
{
lean_object* v___x_2497_; 
v___x_2497_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2___redArg(v_y_2492_, v_x_2494_, v_x_2495_, v_x_2496_);
return v___x_2497_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2___boxed(lean_object* v_y_2498_, lean_object* v_inst_2499_, lean_object* v_x_2500_, lean_object* v_x_2501_, lean_object* v_x_2502_){
_start:
{
size_t v_x_6401__boxed_2503_; size_t v_x_6402__boxed_2504_; lean_object* v_res_2505_; 
v_x_6401__boxed_2503_ = lean_unbox_usize(v_x_2501_);
lean_dec(v_x_2501_);
v_x_6402__boxed_2504_ = lean_unbox_usize(v_x_2502_);
lean_dec(v_x_2502_);
v_res_2505_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Linear_addOcc_spec__2_spec__2(v_y_2498_, v_inst_2499_, v_x_2500_, v_x_6401__boxed_2503_, v_x_6402__boxed_2504_);
lean_dec(v_inst_2499_);
return v_res_2505_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_updateOccs_go(lean_object* v_y_2506_, lean_object* v_p_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_){
_start:
{
if (lean_obj_tag(v_p_2507_) == 1)
{
lean_object* v_v_2520_; lean_object* v_p_2521_; lean_object* v___x_2522_; 
v_v_2520_ = lean_ctor_get(v_p_2507_, 1);
lean_inc(v_v_2520_);
v_p_2521_ = lean_ctor_get(v_p_2507_, 2);
lean_inc(v_p_2521_);
lean_dec_ref(v_p_2507_);
lean_inc(v_a_2508_);
lean_inc(v_y_2506_);
v___x_2522_ = l_Lean_Meta_Grind_Arith_Linear_addOcc(v_v_2520_, v_y_2506_, v_a_2508_, v_a_2509_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_);
if (lean_obj_tag(v___x_2522_) == 0)
{
lean_dec_ref(v___x_2522_);
v_p_2507_ = v_p_2521_;
goto _start;
}
else
{
lean_dec(v_p_2521_);
lean_dec(v_a_2508_);
lean_dec(v_y_2506_);
return v___x_2522_;
}
}
else
{
lean_object* v___x_2524_; lean_object* v___x_2525_; 
lean_dec(v_a_2508_);
lean_dec(v_p_2507_);
lean_dec(v_y_2506_);
v___x_2524_ = lean_box(0);
v___x_2525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2525_, 0, v___x_2524_);
return v___x_2525_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_updateOccs_go___boxed(lean_object* v_y_2526_, lean_object* v_p_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_){
_start:
{
lean_object* v_res_2540_; 
v_res_2540_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_updateOccs_go(v_y_2526_, v_p_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_, v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_);
lean_dec(v_a_2538_);
lean_dec_ref(v_a_2537_);
lean_dec(v_a_2536_);
lean_dec_ref(v_a_2535_);
lean_dec(v_a_2534_);
lean_dec_ref(v_a_2533_);
lean_dec(v_a_2532_);
lean_dec_ref(v_a_2531_);
lean_dec(v_a_2530_);
lean_dec(v_a_2529_);
return v_res_2540_;
}
}
static lean_object* _init_l_Lean_Grind_Linarith_Poly_updateOccs___closed__1(void){
_start:
{
lean_object* v___x_2542_; lean_object* v___x_2543_; 
v___x_2542_ = ((lean_object*)(l_Lean_Grind_Linarith_Poly_updateOccs___closed__0));
v___x_2543_ = l_Lean_stringToMessageData(v___x_2542_);
return v___x_2543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_updateOccs(lean_object* v_p_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_){
_start:
{
if (lean_obj_tag(v_p_2544_) == 1)
{
lean_object* v_v_2557_; lean_object* v_p_2558_; lean_object* v___x_2559_; 
v_v_2557_ = lean_ctor_get(v_p_2544_, 1);
lean_inc(v_v_2557_);
v_p_2558_ = lean_ctor_get(v_p_2544_, 2);
lean_inc(v_p_2558_);
lean_dec_ref(v_p_2544_);
v___x_2559_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_updateOccs_go(v_v_2557_, v_p_2558_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_);
return v___x_2559_;
}
else
{
lean_object* v___x_2560_; lean_object* v___x_2561_; 
lean_dec(v_a_2545_);
lean_dec(v_p_2544_);
v___x_2560_ = lean_obj_once(&l_Lean_Grind_Linarith_Poly_updateOccs___closed__1, &l_Lean_Grind_Linarith_Poly_updateOccs___closed__1_once, _init_l_Lean_Grind_Linarith_Poly_updateOccs___closed__1);
v___x_2561_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNoNatDivInst_spec__0___redArg(v___x_2560_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_);
return v___x_2561_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_updateOccs___boxed(lean_object* v_p_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_){
_start:
{
lean_object* v_res_2575_; 
v_res_2575_ = l_Lean_Grind_Linarith_Poly_updateOccs(v_p_2562_, v_a_2563_, v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_, v_a_2573_);
lean_dec(v_a_2573_);
lean_dec_ref(v_a_2572_);
lean_dec(v_a_2571_);
lean_dec_ref(v_a_2570_);
lean_dec(v_a_2569_);
lean_dec_ref(v_a_2568_);
lean_dec(v_a_2567_);
lean_dec_ref(v_a_2566_);
lean_dec(v_a_2565_);
lean_dec(v_a_2564_);
return v_res_2575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_findVarToSubst(lean_object* v_p_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_){
_start:
{
if (lean_obj_tag(v_p_2576_) == 0)
{
lean_object* v___x_2589_; lean_object* v___x_2590_; 
v___x_2589_ = lean_box(0);
v___x_2590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2590_, 0, v___x_2589_);
return v___x_2590_;
}
else
{
lean_object* v_k_2591_; lean_object* v_v_2592_; lean_object* v_p_2593_; lean_object* v___x_2594_; 
v_k_2591_ = lean_ctor_get(v_p_2576_, 0);
v_v_2592_ = lean_ctor_get(v_p_2576_, 1);
v_p_2593_ = lean_ctor_get(v_p_2576_, 2);
v___x_2594_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_, v_a_2585_, v_a_2586_, v_a_2587_);
if (lean_obj_tag(v___x_2594_) == 0)
{
lean_object* v_a_2595_; lean_object* v___x_2597_; uint8_t v_isShared_2598_; uint8_t v_isSharedCheck_2621_; 
v_a_2595_ = lean_ctor_get(v___x_2594_, 0);
v_isSharedCheck_2621_ = !lean_is_exclusive(v___x_2594_);
if (v_isSharedCheck_2621_ == 0)
{
v___x_2597_ = v___x_2594_;
v_isShared_2598_ = v_isSharedCheck_2621_;
goto v_resetjp_2596_;
}
else
{
lean_inc(v_a_2595_);
lean_dec(v___x_2594_);
v___x_2597_ = lean_box(0);
v_isShared_2598_ = v_isSharedCheck_2621_;
goto v_resetjp_2596_;
}
v_resetjp_2596_:
{
lean_object* v___y_2600_; lean_object* v_elimEqs_2615_; lean_object* v_size_2616_; lean_object* v___x_2617_; uint8_t v___x_2618_; 
v_elimEqs_2615_ = lean_ctor_get(v_a_2595_, 38);
lean_inc_ref(v_elimEqs_2615_);
lean_dec(v_a_2595_);
v_size_2616_ = lean_ctor_get(v_elimEqs_2615_, 2);
v___x_2617_ = lean_box(0);
v___x_2618_ = lean_nat_dec_lt(v_v_2592_, v_size_2616_);
if (v___x_2618_ == 0)
{
lean_object* v___x_2619_; 
lean_dec_ref(v_elimEqs_2615_);
v___x_2619_ = l_outOfBounds___redArg(v___x_2617_);
v___y_2600_ = v___x_2619_;
goto v___jp_2599_;
}
else
{
lean_object* v___x_2620_; 
v___x_2620_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2617_, v_elimEqs_2615_, v_v_2592_);
v___y_2600_ = v___x_2620_;
goto v___jp_2599_;
}
v___jp_2599_:
{
if (lean_obj_tag(v___y_2600_) == 1)
{
lean_object* v_val_2601_; lean_object* v___x_2603_; uint8_t v_isShared_2604_; uint8_t v_isSharedCheck_2613_; 
v_val_2601_ = lean_ctor_get(v___y_2600_, 0);
v_isSharedCheck_2613_ = !lean_is_exclusive(v___y_2600_);
if (v_isSharedCheck_2613_ == 0)
{
v___x_2603_ = v___y_2600_;
v_isShared_2604_ = v_isSharedCheck_2613_;
goto v_resetjp_2602_;
}
else
{
lean_inc(v_val_2601_);
lean_dec(v___y_2600_);
v___x_2603_ = lean_box(0);
v_isShared_2604_ = v_isSharedCheck_2613_;
goto v_resetjp_2602_;
}
v_resetjp_2602_:
{
lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2608_; 
lean_inc(v_v_2592_);
v___x_2605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2605_, 0, v_v_2592_);
lean_ctor_set(v___x_2605_, 1, v_val_2601_);
lean_inc(v_k_2591_);
v___x_2606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2606_, 0, v_k_2591_);
lean_ctor_set(v___x_2606_, 1, v___x_2605_);
if (v_isShared_2604_ == 0)
{
lean_ctor_set(v___x_2603_, 0, v___x_2606_);
v___x_2608_ = v___x_2603_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v___x_2606_);
v___x_2608_ = v_reuseFailAlloc_2612_;
goto v_reusejp_2607_;
}
v_reusejp_2607_:
{
lean_object* v___x_2610_; 
if (v_isShared_2598_ == 0)
{
lean_ctor_set(v___x_2597_, 0, v___x_2608_);
v___x_2610_ = v___x_2597_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v___x_2608_);
v___x_2610_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
return v___x_2610_;
}
}
}
}
else
{
lean_dec(v___y_2600_);
lean_del_object(v___x_2597_);
v_p_2576_ = v_p_2593_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2622_; lean_object* v___x_2624_; uint8_t v_isShared_2625_; uint8_t v_isSharedCheck_2629_; 
v_a_2622_ = lean_ctor_get(v___x_2594_, 0);
v_isSharedCheck_2629_ = !lean_is_exclusive(v___x_2594_);
if (v_isSharedCheck_2629_ == 0)
{
v___x_2624_ = v___x_2594_;
v_isShared_2625_ = v_isSharedCheck_2629_;
goto v_resetjp_2623_;
}
else
{
lean_inc(v_a_2622_);
lean_dec(v___x_2594_);
v___x_2624_ = lean_box(0);
v_isShared_2625_ = v_isSharedCheck_2629_;
goto v_resetjp_2623_;
}
v_resetjp_2623_:
{
lean_object* v___x_2627_; 
if (v_isShared_2625_ == 0)
{
v___x_2627_ = v___x_2624_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2628_; 
v_reuseFailAlloc_2628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2628_, 0, v_a_2622_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_findVarToSubst___boxed(lean_object* v_p_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_){
_start:
{
lean_object* v_res_2643_; 
v_res_2643_ = l_Lean_Grind_Linarith_Poly_findVarToSubst(v_p_2630_, v_a_2631_, v_a_2632_, v_a_2633_, v_a_2634_, v_a_2635_, v_a_2636_, v_a_2637_, v_a_2638_, v_a_2639_, v_a_2640_, v_a_2641_);
lean_dec(v_a_2641_);
lean_dec_ref(v_a_2640_);
lean_dec(v_a_2639_);
lean_dec_ref(v_a_2638_);
lean_dec(v_a_2637_);
lean_dec_ref(v_a_2636_);
lean_dec(v_a_2635_);
lean_dec_ref(v_a_2634_);
lean_dec(v_a_2633_);
lean_dec(v_a_2632_);
lean_dec(v_a_2631_);
lean_dec(v_p_2630_);
return v_res_2643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_gcdCoeffsAux(lean_object* v_x_2644_, lean_object* v_x_2645_){
_start:
{
if (lean_obj_tag(v_x_2644_) == 0)
{
return v_x_2645_;
}
else
{
lean_object* v_k_2646_; lean_object* v_p_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; 
v_k_2646_ = lean_ctor_get(v_x_2644_, 0);
v_p_2647_ = lean_ctor_get(v_x_2644_, 2);
v___x_2648_ = lean_nat_to_int(v_x_2645_);
v___x_2649_ = l_Int_gcd(v_k_2646_, v___x_2648_);
lean_dec(v___x_2648_);
v_x_2644_ = v_p_2647_;
v_x_2645_ = v___x_2649_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_gcdCoeffsAux___boxed(lean_object* v_x_2651_, lean_object* v_x_2652_){
_start:
{
lean_object* v_res_2653_; 
v_res_2653_ = l_Lean_Grind_Linarith_Poly_gcdCoeffsAux(v_x_2651_, v_x_2652_);
lean_dec(v_x_2651_);
return v_res_2653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_gcdCoeffs(lean_object* v_p_2654_){
_start:
{
if (lean_obj_tag(v_p_2654_) == 0)
{
lean_object* v___x_2655_; 
v___x_2655_ = lean_unsigned_to_nat(1u);
return v___x_2655_;
}
else
{
lean_object* v_k_2656_; lean_object* v_p_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; 
v_k_2656_ = lean_ctor_get(v_p_2654_, 0);
v_p_2657_ = lean_ctor_get(v_p_2654_, 2);
v___x_2658_ = lean_nat_abs(v_k_2656_);
v___x_2659_ = l_Lean_Grind_Linarith_Poly_gcdCoeffsAux(v_p_2657_, v___x_2658_);
return v___x_2659_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_gcdCoeffs___boxed(lean_object* v_p_2660_){
_start:
{
lean_object* v_res_2661_; 
v_res_2661_ = l_Lean_Grind_Linarith_Poly_gcdCoeffs(v_p_2660_);
lean_dec(v_p_2660_);
return v_res_2661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_div(lean_object* v_p_2662_, lean_object* v_k_2663_){
_start:
{
if (lean_obj_tag(v_p_2662_) == 0)
{
return v_p_2662_;
}
else
{
lean_object* v_k_2664_; lean_object* v_v_2665_; lean_object* v_p_2666_; lean_object* v___x_2668_; uint8_t v_isShared_2669_; uint8_t v_isSharedCheck_2675_; 
v_k_2664_ = lean_ctor_get(v_p_2662_, 0);
v_v_2665_ = lean_ctor_get(v_p_2662_, 1);
v_p_2666_ = lean_ctor_get(v_p_2662_, 2);
v_isSharedCheck_2675_ = !lean_is_exclusive(v_p_2662_);
if (v_isSharedCheck_2675_ == 0)
{
v___x_2668_ = v_p_2662_;
v_isShared_2669_ = v_isSharedCheck_2675_;
goto v_resetjp_2667_;
}
else
{
lean_inc(v_p_2666_);
lean_inc(v_v_2665_);
lean_inc(v_k_2664_);
lean_dec(v_p_2662_);
v___x_2668_ = lean_box(0);
v_isShared_2669_ = v_isSharedCheck_2675_;
goto v_resetjp_2667_;
}
v_resetjp_2667_:
{
lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2673_; 
v___x_2670_ = lean_int_ediv(v_k_2664_, v_k_2663_);
lean_dec(v_k_2664_);
v___x_2671_ = l_Lean_Grind_Linarith_Poly_div(v_p_2666_, v_k_2663_);
if (v_isShared_2669_ == 0)
{
lean_ctor_set(v___x_2668_, 2, v___x_2671_);
lean_ctor_set(v___x_2668_, 0, v___x_2670_);
v___x_2673_ = v___x_2668_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v___x_2670_);
lean_ctor_set(v_reuseFailAlloc_2674_, 1, v_v_2665_);
lean_ctor_set(v_reuseFailAlloc_2674_, 2, v___x_2671_);
v___x_2673_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
return v___x_2673_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_div___boxed(lean_object* v_p_2676_, lean_object* v_k_2677_){
_start:
{
lean_object* v_res_2678_; 
v_res_2678_ = l_Lean_Grind_Linarith_Poly_div(v_p_2676_, v_k_2677_);
lean_dec(v_k_2677_);
return v_res_2678_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__0(void){
_start:
{
lean_object* v___x_2679_; lean_object* v___x_2680_; 
v___x_2679_ = lean_unsigned_to_nat(1u);
v___x_2680_ = lean_nat_to_int(v___x_2679_);
return v___x_2680_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__1(void){
_start:
{
lean_object* v___x_2681_; lean_object* v___x_2682_; 
v___x_2681_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__0);
v___x_2682_ = lean_int_neg(v___x_2681_);
return v___x_2682_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go(lean_object* v_k_2683_, lean_object* v_x_2684_, lean_object* v_p_2685_){
_start:
{
uint8_t v___y_2687_; lean_object* v___x_2698_; uint8_t v___x_2699_; 
v___x_2698_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__0);
v___x_2699_ = lean_int_dec_eq(v_k_2683_, v___x_2698_);
if (v___x_2699_ == 0)
{
lean_object* v___x_2700_; uint8_t v___x_2701_; 
v___x_2700_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go___closed__1);
v___x_2701_ = lean_int_dec_eq(v_k_2683_, v___x_2700_);
v___y_2687_ = v___x_2701_;
goto v___jp_2686_;
}
else
{
v___y_2687_ = v___x_2699_;
goto v___jp_2686_;
}
v___jp_2686_:
{
if (v___y_2687_ == 0)
{
if (lean_obj_tag(v_p_2685_) == 0)
{
lean_object* v___x_2688_; 
v___x_2688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2688_, 0, v_k_2683_);
lean_ctor_set(v___x_2688_, 1, v_x_2684_);
return v___x_2688_;
}
else
{
lean_object* v_k_2689_; lean_object* v_v_2690_; lean_object* v_p_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; uint8_t v___x_2694_; 
v_k_2689_ = lean_ctor_get(v_p_2685_, 0);
lean_inc(v_k_2689_);
v_v_2690_ = lean_ctor_get(v_p_2685_, 1);
lean_inc(v_v_2690_);
v_p_2691_ = lean_ctor_get(v_p_2685_, 2);
lean_inc(v_p_2691_);
lean_dec_ref(v_p_2685_);
v___x_2692_ = lean_nat_abs(v_k_2689_);
v___x_2693_ = lean_nat_abs(v_k_2683_);
v___x_2694_ = lean_nat_dec_lt(v___x_2692_, v___x_2693_);
lean_dec(v___x_2693_);
lean_dec(v___x_2692_);
if (v___x_2694_ == 0)
{
lean_dec(v_v_2690_);
lean_dec(v_k_2689_);
v_p_2685_ = v_p_2691_;
goto _start;
}
else
{
lean_dec(v_x_2684_);
lean_dec(v_k_2683_);
v_k_2683_ = v_k_2689_;
v_x_2684_ = v_v_2690_;
v_p_2685_ = v_p_2691_;
goto _start;
}
}
}
else
{
lean_object* v___x_2697_; 
lean_dec(v_p_2685_);
v___x_2697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2697_, 0, v_k_2683_);
lean_ctor_set(v___x_2697_, 1, v_x_2684_);
return v___x_2697_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_pickVarToElim_x3f(lean_object* v_p_2702_){
_start:
{
if (lean_obj_tag(v_p_2702_) == 0)
{
lean_object* v___x_2703_; 
v___x_2703_ = lean_box(0);
return v___x_2703_;
}
else
{
lean_object* v_k_2704_; lean_object* v_v_2705_; lean_object* v_p_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; 
v_k_2704_ = lean_ctor_get(v_p_2702_, 0);
lean_inc(v_k_2704_);
v_v_2705_ = lean_ctor_get(v_p_2702_, 1);
lean_inc(v_v_2705_);
v_p_2706_ = lean_ctor_get(v_p_2702_, 2);
lean_inc(v_p_2706_);
lean_dec_ref(v_p_2702_);
v___x_2707_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Util_0__Lean_Grind_Linarith_Poly_pickVarToElim_x3f_go(v_k_2704_, v_v_2705_, v_p_2706_);
v___x_2708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2708_, 0, v___x_2707_);
return v___x_2708_;
}
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Util(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Gcd(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Util(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
